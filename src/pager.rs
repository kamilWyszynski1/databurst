use anyhow::bail;

use crate::{
    constants::{PAGE_SIZE, TABLE_MAX_PAGES},
    node::Node,
    row::{TableDefinition, MAX_TABLE_DEFINITION_SIZE},
};
use std::{
    cell::RefCell,
    fs::{File, OpenOptions},
    io::{BufReader, Read, Seek, SeekFrom, Write},
    path::Path,
    rc::Rc,
};

pub fn vector_to_array<T, const N: usize>(mut v: Vec<T>) -> anyhow::Result<[T; N]>
where
    T: Default,
{
    let missing = N
        .checked_sub(v.len())
        .ok_or_else(|| anyhow::anyhow!("invalid len of input"))?;
    v.append(&mut (0..missing).map(|_| T::default()).collect());

    let t: Result<[T; N], _> = v.try_into();

    match t {
        Ok(t) => Ok(t),
        Err(_) => bail!("could not convert vector to array"),
    }
}
#[derive(Debug, Clone)]
pub struct Page {
    pub data: [u8; PAGE_SIZE],

    /// Amount of bytes that row's key takes. It is dynamical because indexes' keys can be arbitrary values like strings.
    pub key_size: usize,
    /// Amount of bytes that row "body" takes.
    pub row_size: usize,
}

impl Page {
    pub fn new(key_size: usize, row_size: usize) -> Self {
        if key_size == 276 {}
        Self {
            data: [0; PAGE_SIZE],
            key_size,
            row_size,
        }
    }

    fn content(&self) -> Vec<u8> {
        self.data.to_vec()
    }

    /// Fetches a slice of bytes from certain offset and of certain size.
    pub fn get_ptr_from_offset(&self, offset: usize, size: usize) -> &[u8] {
        &self.data[offset..offset + size]
    }
}

impl TryFrom<Node> for Page {
    type Error = anyhow::Error;

    fn try_from(value: Node) -> anyhow::Result<Self, Self::Error> {
        Ok(Self {
            key_size: value.key_size,
            row_size: value.row_size,
            data: value.try_into()?,
        })
    }
}

#[derive(Debug)]
pub struct Pager {
    f: File,
    pub file_len: u32,
    pub num_pages: u32,
    pub pages_rc: [Option<Rc<RefCell<Page>>>; TABLE_MAX_PAGES],
}

impl Pager {
    pub fn new<P: AsRef<Path>>(p: P) -> anyhow::Result<Self> {
        let f = OpenOptions::new()
            .write(true)
            .read(true)
            .create(true)
            .open(p)?;

        let mut f_len = f.metadata()?.len();
        if f_len >= MAX_TABLE_DEFINITION_SIZE as u64 {
            f_len -= MAX_TABLE_DEFINITION_SIZE as u64;
        }

        let file_len = f_len as u32;
        let num_pages = (file_len as usize / PAGE_SIZE) as u32;

        const INIT: Option<Rc<RefCell<Page>>> = None;

        Ok(Self {
            f,
            file_len,
            num_pages,
            pages_rc: [INIT; TABLE_MAX_PAGES],
        })
    }

    /// Until we start recycling free pages, new pages will always go onto the end of the database file.
    /// TODO: reuse already alocated(written) pages after deletion
    pub fn get_unused_page_num(&self) -> u32 {
        self.num_pages
    }

    pub fn get_page(
        &mut self,
        page_num: u32,
        key_size: usize,
        row_size: usize,
    ) -> anyhow::Result<Rc<RefCell<Page>>> {
        if page_num as usize > TABLE_MAX_PAGES {
            bail!(
                "tried to fetch pager number out of bounds: {} > {}",
                page_num,
                TABLE_MAX_PAGES
            )
        }

        if let Some(Some(page)) = self.pages_rc.get(page_num as usize) {
            return Ok(page.clone());
        }

        // not found
        let mut num_pages = self.file_len as usize / PAGE_SIZE;

        // We might save a partial page at the end of the file
        if self.file_len as usize % PAGE_SIZE == 1 {
            num_pages += 1;
        }

        let page = if num_pages >= page_num as usize {
            // read and parse Row from the file
            let mut buf = vec![];

            let mut reader = BufReader::new(&self.f);

            reader.seek(SeekFrom::Start(
                (MAX_TABLE_DEFINITION_SIZE + page_num as usize * PAGE_SIZE).try_into()?,
            ))?;
            reader.take(PAGE_SIZE as u64).read_to_end(&mut buf)?;

            // let's split page into chunks
            let mut page = Page::new(key_size, row_size);
            page.data = vector_to_array(buf)?;

            page
        } else {
            Page::new(key_size, row_size)
        };

        let p = Rc::new(RefCell::new(page));
        self.pages_rc[page_num as usize] = Some(p.clone());

        if page_num >= self.num_pages {
            self.num_pages = page_num + 1
        }

        Ok(p)
    }

    /// Gets pages content and write it to file filling missing bytes.
    /// Additionally we will write TableDefinition if this is first write to a file.
    pub fn flush(mut self, table_def: TableDefinition) -> anyhow::Result<()> {
        if self.file_len == 0 {
            self.f.rewind()?; // at the very end of a file

            let mut table_def_bytes: Vec<u8> = table_def.into();
            table_def_bytes.append(&mut vec![
                0u8;
                MAX_TABLE_DEFINITION_SIZE - table_def_bytes.len()
            ]);
            self.f.write_all(&table_def_bytes)?;
        }

        for (i, page) in self
            .pages_rc
            .into_iter()
            .enumerate()
            .filter(|(_, p)| p.is_some())
            .map(|(i, p)| (i, p.unwrap()))
        {
            // go into proper place in file
            let offset: u64 = (MAX_TABLE_DEFINITION_SIZE + (i * PAGE_SIZE)).try_into()?;
            self.f.seek(SeekFrom::Start(offset))?;
            // write content
            let mut content = page.borrow().content();

            content.append(&mut vec![0u8; PAGE_SIZE - content.len()]);

            self.f.write_all(&content)?;
        }
        Ok(())
    }

    pub fn read_table_definition(&mut self) -> anyhow::Result<Option<TableDefinition>> {
        if self.file_len == 0 {
            return Ok(None);
        }
        let mut table_def_bytes = [0; MAX_TABLE_DEFINITION_SIZE];
        self.f.read_exact(&mut table_def_bytes)?;

        Ok(Some(TableDefinition::try_from(table_def_bytes.to_vec())?))
    }

    pub fn write_node(&mut self, page_num: u32, node: Node) -> anyhow::Result<()> {
        let (key_size, row_size) = (node.key_size, node.row_size);
        self.get_page(page_num, key_size, row_size)?
            .try_borrow_mut()?
            .data = node.try_into()?;
        Ok(())
    }
}
