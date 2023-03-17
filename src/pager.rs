use crate::constants::{PAGE_SIZE, ROWS_PER_PAGE, ROWS_SIZE, TABLE_MAX_PAGES};
use anyhow::{bail, Ok};
use std::{
    cell::RefCell,
    fs::{File, OpenOptions},
    io::{BufReader, Read, Seek, SeekFrom, Write},
    path::Path,
    rc::Rc,
};

#[derive(Debug, Default, Clone)]
pub struct Page {
    pub meta: String,
    pub chunks: [Option<Rc<RefCell<Vec<u8>>>>; ROWS_PER_PAGE],
}

impl Page {
    fn new() -> Self {
        const INIT: Option<Rc<RefCell<Vec<u8>>>> = None;
        Self {
            chunks: [INIT; ROWS_PER_PAGE],
            meta: String::default(),
        }
    }

    pub fn get(&mut self, inx: usize) -> anyhow::Result<Rc<RefCell<Vec<u8>>>> {
        match self.chunks.get(inx) {
            Some(got) => match got {
                Some(hit) => Ok(hit.clone()),
                None => {
                    let data: Rc<RefCell<Vec<u8>>> = Rc::default();
                    self.chunks[inx] = Some(data.clone());
                    Ok(data)
                }
            },
            None => bail!("index out of range"),
        }
    }

    fn content(self) -> Vec<u8> {
        let a: Vec<u8> = self
            .chunks
            .into_iter()
            .filter(Option::is_some)
            .flat_map(|r| r.unwrap().take())
            .collect();
        a
    }
}

#[derive(Debug)]
pub struct Pager {
    f: File,
    pub file_len: usize,
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

        const INIT: Option<Rc<RefCell<Page>>> = None;

        Ok(Self {
            f,
            file_len,
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
            for (i, chunk) in buf.chunks(ROWS_SIZE).enumerate() {
                page.chunks[i] = Some(Rc::new(RefCell::new(chunk.to_vec())));
            }

            page.chunks[0] = Some(Rc::new(RefCell::new(buf)));

            page
        } else {
            Page::new()
        };

        let p = Rc::new(RefCell::new(page));
        self.pages_rc[page_num] = Some(p.clone());

        Ok(p)
    }

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
            let content = page.take().content();

            self.f.write_all(&content)?;
        }
        Ok(())
    }
}
