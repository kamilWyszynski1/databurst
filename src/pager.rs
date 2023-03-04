use crate::constants::{ROWS_PER_PAGE, ROWS_SIZE};
use anyhow::Ok;
use std::{
    fs::{File, OpenOptions},
    path::Path,
};

#[derive(Debug, Default)]
pub struct Page {
    pub rows: Vec<u8>,
}

impl Page {
    pub fn is_full(&self) -> bool {
        self.rows.len() / ROWS_SIZE >= ROWS_PER_PAGE
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
    file_len: u64,
    pages: Vec<Page>,
}

impl Pager {
    fn new<P: AsRef<Path>>(p: P) -> anyhow::Result<Self> {
        let f = OpenOptions::new()
            .write(true)
            .read(true)
            .create_new(true)
            .open(p)?;

        let file_len = f.metadata()?.len();
        Ok(Self {
            f,
            file_len,
            pages: vec![],
        })
    }
}
