use anyhow::{bail, Context};
use std::{fmt::Debug, str::from_utf8};

macro_rules! field_size {
    ($t:ident :: $field:ident) => {{
        let m = core::mem::MaybeUninit::<$t>::uninit();
        // According to https://doc.rust-lang.org/stable/std/ptr/macro.addr_of_mut.html#examples,
        // you can dereference an uninitialized MaybeUninit pointer in addr_of!
        // Raw pointer deref in const contexts is stabilized in 1.58:
        // https://github.com/rust-lang/rust/pull/89551
        let p = unsafe { core::ptr::addr_of!((*(&m as *const _ as *const $t)).$field) };

        const fn size_of_raw<T>(_: *const T) -> usize {
            core::mem::size_of::<T>()
        }
        size_of_raw(p)
    }};
}

const ID_SIZE: usize = field_size!(Row::id);
const USERNAME_SIZE: usize = field_size!(Row::username);
const EMAIL_SIZE: usize = field_size!(Row::email);

const ID_OFFSET: usize = 0;
const USERNAME_OFFSET: usize = ID_OFFSET + ID_SIZE;
const EMAIL_OFFSET: usize = USERNAME_OFFSET + USERNAME_SIZE;
const ROWS_SIZE: usize = ID_SIZE + USERNAME_SIZE + EMAIL_SIZE;

struct Row {
    id: u32,
    username: [u8; 32],
    email: [u8; 255],
}

impl PartialEq for Row {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id && self.username == other.username && self.email == other.email
    }
}

impl Debug for Row {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let binding = self.username.to_vec();
        let username = from_utf8(&binding).unwrap();

        let binding = self.email.to_vec();
        let email = from_utf8(&binding).unwrap();

        f.debug_struct("Row")
            .field("id", &self.id)
            .field("username", &username)
            .field("email", &email)
            .finish()
    }
}

impl Row {
    fn serialize(&self) -> Vec<u8> {
        let mut buffer = vec![];
        buffer.append(&mut self.id.to_be_bytes().to_vec());
        buffer.append(&mut self.username.to_vec());
        buffer.append(&mut self.email.to_vec());

        buffer
    }

    fn deserialize(data: &[u8]) -> anyhow::Result<Row> {
        if data.len() < ROWS_SIZE {
            bail!("data size is too small")
        }

        let id_bytes = &data[ID_OFFSET..ID_SIZE];
        let username_bytes = &data[USERNAME_OFFSET..USERNAME_OFFSET + USERNAME_SIZE];
        let email_bytes = &data[EMAIL_OFFSET..EMAIL_OFFSET + EMAIL_SIZE];

        let id: u32 = u32::from_be_bytes(
            id_bytes
                .try_into()
                .context("cannot convert id_bytes to array")?,
        );

        Ok(Self {
            id,
            email: email_bytes
                .try_into()
                .context("cannot convert email_bytes to array")?,
            username: username_bytes
                .try_into()
                .context("cannot convert username_bytes to array")?,
        })
    }
}

const TABLE_MAX_PAGES: usize = 100;
const PAGE_SIZE: usize = 4096; // 4KB
const ROWS_PER_PAGE: usize = PAGE_SIZE / ROWS_SIZE;
const TABLE_MAX_ROWS: usize = ROWS_PER_PAGE * TABLE_MAX_PAGES;

#[derive(Debug, Default)]
struct Page {
    rows: Vec<u8>,
}

impl Page {
    fn is_full(&self) -> bool {
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

#[derive(Debug, Default)]
struct Table {
    num_rows: usize,
    pages: Vec<Page>,
}

impl Table {
    fn insert(&mut self, r: &Row) -> anyhow::Result<()> {
        if self.pages.len() >= TABLE_MAX_ROWS {
            bail!("table is full")
        }

        let mut bytes = r.serialize();

        match self.pages.last_mut() {
            Some(last_page) => {
                if last_page.is_full() {
                    // create new page
                    self.pages.push(Page { rows: bytes });
                } else {
                    last_page.rows.append(&mut bytes);
                }
            }
            None => self.pages = vec![Page { rows: bytes }],
        }

        self.num_rows += 1;

        Ok(())
    }

    fn select(&mut self) -> anyhow::Result<()> {
        self.pages.iter().for_each(|page| {
            page.into_iter().for_each(|bytes| {
                Row::deserialize(bytes).unwrap();
            })
        });
        Ok(())
    }
}

/// Goes through all saved rows, deserialize them.
impl<'a> IntoIterator for &'a Table {
    type Item = Row;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.pages
            .iter()
            .flat_map(|page| {
                let rows: Vec<Row> = page
                    .into_iter()
                    .map(|bytes| Row::deserialize(bytes).unwrap())
                    .collect();
                rows
            })
            .collect::<Vec<Row>>()
            .into_iter()
    }
}

#[cfg(test)]
mod tests {
    use crate::table::ROWS_SIZE;

    use super::{Row, Table};
    use std::io::Write;

    #[test]
    fn test_row_size() {
        assert_eq!(291, ROWS_SIZE);
    }

    fn str_as_bytes(s: &str) -> Vec<u8> {
        let mut buffer = vec![];
        buffer.write_all(s.as_bytes()).unwrap();

        buffer.to_vec()
    }

    use std::convert::TryInto;

    fn demo<T, const N: usize>(mut v: Vec<T>) -> [T; N]
    where
        T: Default,
    {
        let missing = N - v.len();

        v.append(&mut (0..missing).map(|_| T::default()).collect());

        v.try_into().unwrap_or_else(|v: Vec<T>| {
            panic!("Expected a Vec of length {} but it was {}", N, v.len())
        })
    }

    #[test]
    fn test_serialize() {
        let r = Row {
            id: 1,
            username: demo(str_as_bytes("elo")),
            email: demo(str_as_bytes("asdasdkpoqkwepoqkwepoqw")),
        };
        let b1 = r.serialize();
        let b2 = r.serialize();

        assert_eq!(b1, b2)
    }

    #[test]
    fn test_deserialize() -> anyhow::Result<()> {
        let r = Row {
            id: 1,
            username: demo(str_as_bytes("elo")),
            email: demo(str_as_bytes("asdasdkpoqkwepoqkwepoqw")),
        };
        let b1 = r.serialize();
        let b2 = r.serialize();

        let r1 = Row::deserialize(&b1)?;
        let r2 = Row::deserialize(&b2)?;

        assert_eq!(r, r1);
        assert_eq!(r, r2);

        Ok(())
    }

    #[test]
    fn test() {
        let a = [0; 255];
        let v = a.to_vec();

        assert_eq!(a.len(), 255);
        assert_eq!(v.len(), 255);
    }

    #[test]
    fn test_table() -> anyhow::Result<()> {
        let r = Row {
            id: 1,
            username: demo(str_as_bytes("elo")),
            email: demo(str_as_bytes("asdasdkpoqkwepoqkwepoqw")),
        };
        let r2 = Row {
            id: 2,
            username: demo(str_as_bytes("elo2")),
            email: demo(str_as_bytes("asdasdkpoqkwepoqkwepoqw2")),
        };
        let r3 = Row {
            id: 3,
            username: demo(str_as_bytes("elo3")),
            email: demo(str_as_bytes("asdasdkpoqkwepoqkwepoqw3")),
        };
        let mut table = Table::default();
        table.insert(&r)?;
        table.insert(&r2)?;
        table.insert(&r3)?;

        table.into_iter().for_each(|r| {
            dbg!(&r);
        });

        let mut table = Table::default();
        // check pages
        for _ in 0..100 {
            table.insert(&r)?;
        }
        assert_eq!(table.num_rows, 100);
        assert_eq!(table.pages.len(), 8);

        Ok(())
    }
}
