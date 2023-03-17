use crate::{
    constants::{PAGE_SIZE, TABLE_MAX_PAGES},
    table::vector_to_array,
};
use anyhow::bail;
use std::{
    cell::RefCell,
    fs::{File, OpenOptions},
    io::{BufReader, Read, Seek, SeekFrom, Write},
    path::Path,
    rc::Rc,
};

#[derive(Debug, Clone)]
pub struct Page {
    pub data: [u8; PAGE_SIZE],
}

impl Page {
    fn new() -> Self {
        Self {
            data: [0; PAGE_SIZE],
        }
    }

    fn content(&self) -> Vec<u8> {
        self.data.to_vec()
    }

    /// get_ptr_from_offset fetches a slice of bytes from certain offset and of certain size.
    pub fn get_ptr_from_offset(&self, offset: usize, size: usize) -> &[u8] {
        &self.data[offset..offset + size]
    }
}

#[derive(Debug)]
pub struct Pager {
    f: File,
    pub file_len: usize,
    pub num_pages: usize,
    pub pages_rc: [Option<Rc<RefCell<Page>>>; TABLE_MAX_PAGES],
}

impl Pager {
    pub fn new<P: AsRef<Path>>(p: P) -> anyhow::Result<Self> {
        let f = OpenOptions::new()
            .write(true)
            .read(true)
            .create(true)
            .open(p)?;

        let file_len = f.metadata()?.len() as usize;
        let num_pages = file_len / PAGE_SIZE;

        const INIT: Option<Rc<RefCell<Page>>> = None;

        Ok(Self {
            f,
            file_len,
            num_pages,
            pages_rc: [INIT; TABLE_MAX_PAGES],
        })
    }

    pub fn get_page(&mut self, page_num: usize) -> anyhow::Result<Rc<RefCell<Page>>> {
        if page_num > TABLE_MAX_PAGES {
            bail!(
                "tried to fetch pager number out of bounds: {} > {}",
                page_num,
                TABLE_MAX_PAGES
            )
        }

        if let Some(Some(page)) = self.pages_rc.get(page_num) {
            return Ok(page.clone());
        }

        // not found
        let mut num_pages = self.file_len / PAGE_SIZE;

        // We might save a partial page at the end of the file
        if self.file_len % PAGE_SIZE == 1 {
            num_pages += 1;
        }

        let page = if num_pages >= page_num {
            // read and parse Row from the file
            let mut buf = vec![];

            let mut reader = BufReader::new(&self.f);
            // let reader = self.f.by_ref();

            reader.seek(SeekFrom::Start((page_num * PAGE_SIZE).try_into()?))?;
            reader.take(PAGE_SIZE as u64).read_to_end(&mut buf)?;

            // let's split page into chunks
            let mut page = Page::new();
            page.data = vector_to_array(buf)?;

            page
        } else {
            Page::new()
        };

        let p = Rc::new(RefCell::new(page));
        self.pages_rc[page_num] = Some(p.clone());

        if page_num >= self.num_pages {
            self.num_pages = page_num + 1
        }

        Ok(p)
    }

    /// Gets pages content and write it to file filling missing bytes.
    pub fn flush(mut self) -> anyhow::Result<()> {
        for (i, page) in self
            .pages_rc
            .into_iter()
            .enumerate()
            .filter(|(_, p)| p.is_some())
            .map(|(i, p)| (i, p.unwrap()))
        {
            // go into proper place in file
            self.f.seek(SeekFrom::Start((i * PAGE_SIZE).try_into()?))?;
            // write content
            let mut content = page.borrow().content();

            content.append(&mut vec![0u8; PAGE_SIZE - content.len()]);

            self.f.write_all(&content)?;
        }
        Ok(())
    }
}
