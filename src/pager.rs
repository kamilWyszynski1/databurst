use crate::constants::{PAGE_SIZE, ROWS_PER_PAGE, ROWS_SIZE, TABLE_MAX_PAGES};
use anyhow::{bail, Ok};
use std::{
    cell::RefCell,
    fs::{File, OpenOptions},
    io::{Read, Seek, SeekFrom, Write},
    path::Path,
};

#[derive(Debug, Default, Clone)]
pub struct Page {
    pub rows: Vec<u8>,
}

impl Page {
    pub fn is_full(&self) -> bool {
        self.rows.len() / ROWS_SIZE >= ROWS_PER_PAGE
    }

    pub fn append(&mut self, data: &mut Vec<u8>) -> anyhow::Result<()> {
        if self.rows.len() + data.len() >= PAGE_SIZE {
            bail!("too much data!")
        }
        self.rows.append(data);
        Ok(())
    }
}

impl<'a> IntoIterator for &'a Page {
    type Item = &'a [u8];
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.rows
            .chunks(ROWS_SIZE)
            .collect::<Vec<&[u8]>>()
            .into_iter()
    }
}

#[derive(Debug)]
pub struct Pager {
    f: File,
    pub file_len: usize,
    pub pages: [Option<Page>; TABLE_MAX_PAGES],
    pub pages_rc: [Option<RefCell<Page>>; TABLE_MAX_PAGES],
}

impl Pager {
    pub fn new<P: AsRef<Path>>(p: P) -> anyhow::Result<Self> {
        let f = OpenOptions::new()
            .write(true)
            .read(true)
            .create(true)
            .open(p)?;

        let file_len = f.metadata()?.len() as usize;

        const INIT: Option<Page> = None;

        const INIT2: Option<RefCell<Page>> = None;

        Ok(Self {
            f,
            file_len,
            pages: [INIT; TABLE_MAX_PAGES],
            pages_rc: [INIT2; TABLE_MAX_PAGES],
        })
    }

    pub fn insert(&mut self, page_num: usize, mut row: Vec<u8>) -> anyhow::Result<()> {
        if page_num > TABLE_MAX_PAGES {
            bail!(
                "tried to fetch pager number out of bounds: {} > {}",
                page_num,
                TABLE_MAX_PAGES
            )
        }

        if let Some(page) = self.pages.get_mut(page_num) {
            if let Some(page) = page.as_mut() {
                page.rows.append(&mut row);
                return Ok(());
            }
        }

        // not found
        let mut num_pages = self.file_len / PAGE_SIZE;

        // We might save a partial page at the end of the file
        if self.file_len % PAGE_SIZE == 1 {
            num_pages += 1;
        }

        let mut page = if num_pages >= page_num {
            // read and parse Row from the file
            let mut buf = Vec::default();

            self.f.seek(SeekFrom::Start(PAGE_SIZE.try_into()?))?;
            self.f.read(&mut buf)?;

            Page { rows: buf }
        } else {
            Page { rows: vec![] }
        };

        page.rows.append(&mut row);

        self.pages[page_num] = Some(page);
        Ok(())
    }

    pub fn get_page(&mut self, page_num: usize) -> anyhow::Result<RefCell<Page>> {
        if page_num > TABLE_MAX_PAGES {
            bail!(
                "tried to fetch pager number out of bounds: {} > {}",
                page_num,
                TABLE_MAX_PAGES
            )
        }

        if let Some(page) = self.pages_rc.get(page_num) {
            if let Some(page) = page {
                return Ok(page.clone());
            }
        }

        // not found
        let mut num_pages = self.file_len / PAGE_SIZE;

        // We might save a partial page at the end of the file
        if self.file_len % PAGE_SIZE == 1 {
            num_pages += 1;
        }

        let page = if num_pages >= page_num {
            // read and parse Row from the file
            let mut buf = Vec::with_capacity(PAGE_SIZE);

            dbg!("seek", page_num * PAGE_SIZE);
            self.f
                .seek(SeekFrom::Start((page_num * PAGE_SIZE).try_into()?))?;
            self.f.read_to_end(&mut buf)?;

            dbg!(&buf);

            Page { rows: buf }
        } else {
            Page { rows: vec![] }
        };

        let p = RefCell::new(page);
        self.pages_rc[page_num] = Some(p.clone());
        Ok(p)
    }

    pub fn flush(mut self) -> anyhow::Result<()> {
        for (i, page) in self
            .pages
            .into_iter()
            .enumerate()
            .filter(|(_, p)| p.is_some())
            .map(|(i, p)| (i, p.unwrap()))
        {
            // go into proper place in file
            self.f.seek(SeekFrom::Start((i * PAGE_SIZE).try_into()?))?;
            // write content
            self.f.write_all(&page.rows)?;
        }
        Ok(())
    }
}

impl<'a> IntoIterator for &'a Pager {
    type Item = &'a Page;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.pages
            .iter()
            .filter(|p| p.is_some())
            .map(|page| page.as_ref().unwrap())
            .collect::<Vec<&Page>>()
            .into_iter()
    }
}

#[cfg(test)]
mod test {
    use anyhow::Ok;
    use std::{borrow::BorrowMut, fs::File, io::Write};
    use tempdir::TempDir;

    use crate::table::{str_as_bytes, vector_to_array, Row};

    use super::Pager;

    #[test]
    fn test_rc() -> anyhow::Result<()> {
        let tmp_dir = TempDir::new("databurst")?;
        let file_path = tmp_dir.path().join("my.db");
        let mut file = File::create(&file_path)?;

        file.write_all(
            &Row {
                id: 1,
                username: vector_to_array(str_as_bytes("a".repeat(2).as_str())).unwrap(),
                email: vector_to_array(str_as_bytes("b".repeat(5).as_str())).unwrap(),
            }
            .serialize(),
        )?;
        file.flush()?;

        let mut pager = Pager::new(file_path)?;
        let page = pager.get_page(0)?;
        // dbg!(page);
        page.borrow_mut().rows.append(&mut vec![1, 2, 3, 4, 5]);
        dbg!(page);

        Ok(())
    }
}
