use anyhow::{anyhow, bail, Context};
use std::{cell::RefCell, fmt::Debug, path::Path, rc::Rc, str::from_utf8};

use crate::{
    constants::{
        EMAIL_OFFSET, ID_OFFSET, ROWS_PER_PAGE, ROWS_SIZE, TABLE_MAX_ROWS, USERNAME_OFFSET,
    },
    pager::Pager,
};

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

pub const ID_SIZE: usize = field_size!(Row::id);
pub const USERNAME_SIZE: usize = field_size!(Row::username);
pub const EMAIL_SIZE: usize = field_size!(Row::email);

#[derive(PartialOrd, Clone)]
pub struct Row {
    pub id: u32,
    pub username: [u8; 32],
    pub email: [u8; 255],
}

impl TryFrom<Vec<&str>> for Row {
    type Error = anyhow::Error;

    fn try_from(value: Vec<&str>) -> Result<Self, Self::Error> {
        if value.len() != 3 {
            bail!("require 3 element")
        }

        let id: u32 = value[0].parse().context("could not parse id")?;
        let username: [u8; 32] =
            vector_to_array(value[1].into()).context("could not parse username")?;
        let email: [u8; 255] = vector_to_array(value[2].into()).context("could not parse email")?;

        Ok(Self {
            id,
            username,
            email,
        })
    }
}

impl TryFrom<(u32, String, String)> for Row {
    type Error = anyhow::Error;

    fn try_from(value: (u32, String, String)) -> Result<Self, Self::Error> {
        let (id, username, email) = value;

        let username: [u8; 32] =
            vector_to_array(username.into()).context("could not parse username")?;
        let email: [u8; 255] = vector_to_array(email.into()).context("could not parse email")?;

        Ok(Self {
            id,
            username,
            email,
        })
    }
}

impl PartialEq for Row {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id && self.username == other.username && self.email == other.email
    }
}

impl Debug for Row {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let binding = self.username.to_vec();
        let username = from_utf8(&binding).unwrap().replace('\0', "");

        let binding = self.email.to_vec();
        let email = from_utf8(&binding).unwrap().replace('\0', "");

        f.debug_struct("Row")
            .field("id", &self.id)
            .field("username", &username)
            .field("email", &email)
            .finish()
    }
}

impl Row {
    pub fn serialize(&self) -> Vec<u8> {
        let mut buffer = vec![];
        buffer.append(&mut self.id.to_be_bytes().to_vec());
        buffer.append(&mut self.username.to_vec());
        buffer.append(&mut self.email.to_vec());

        assert_eq!(buffer.len(), ROWS_SIZE);

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

#[derive(Debug)]
pub struct Table {
    num_rows: usize,
    // pages: Vec<Page>,
    pager: Pager,
}

impl Table {
    pub fn db_open<P: AsRef<Path>>(p: P) -> anyhow::Result<Self> {
        let pager = Pager::new(p)?;
        Ok(Self {
            num_rows: pager.file_len / ROWS_SIZE,
            pager,
        })
    }

    /// Consumes Table and saves all content to file.
    pub fn close(self) -> anyhow::Result<()> {
        self.pager.flush()
    }

    fn row_slot(&mut self, row_num: usize) -> anyhow::Result<Option<Rc<RefCell<Vec<u8>>>>> {
        let page_num = row_num / ROWS_PER_PAGE;
        let page = self.pager.get_page(page_num)?;

        let x = Ok(Some(page.try_borrow_mut()?.get(row_num % ROWS_PER_PAGE)?));
        x
    }

    pub fn insert(&mut self, r: &Row) -> anyhow::Result<()> {
        if self.num_rows >= TABLE_MAX_ROWS {
            bail!("table is full")
        }

        let mut data = r.serialize();
        match self.row_slot(self.num_rows)? {
            Some(place) => {
                place.try_borrow_mut()?.append(&mut data);
                println!("saved");
            }
            None => bail!("could not find place to save row"),
        }

        self.num_rows += 1;

        Ok(())
    }

    #[cfg(test)]
    fn collect(&mut self) -> anyhow::Result<Vec<Row>> {
        let mut rows = vec![];
        for i in 0..self.num_rows {
            match self.row_slot(i)? {
                Some(place) => {
                    let row = Row::deserialize(&place.borrow().clone())?;
                    rows.push(row);
                }
                None => bail!("could not find row in saved content"),
            }
        }
        Ok(rows)
    }

    pub fn select(&mut self) -> anyhow::Result<()> {
        for i in 0..self.num_rows {
            match self.row_slot(i)? {
                Some(place) => {
                    let row = Row::deserialize(&place.borrow().clone())?;

                    println!("row {}, {:?}", i, row)
                }
                None => bail!("could not find row in saved content"),
            }
        }
        Ok(())
    }
}

pub fn vector_to_array<T, const N: usize>(mut v: Vec<T>) -> anyhow::Result<[T; N]>
where
    T: Default,
{
    let missing = N
        .checked_sub(v.len())
        .ok_or_else(|| anyhow!("invalid len of input"))?;

    v.append(&mut (0..missing).map(|_| T::default()).collect());

    let t: Result<[T; N], _> = v.try_into();

    match t {
        Ok(t) => Ok(t),
        Err(_) => bail!("could not convert vector to array"),
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Ok;
    use tempdir::TempDir;

    use super::{vector_to_array, Row, Table};
    use crate::table::ROWS_SIZE;
    use std::{fs::File, io::Write};

    pub fn str_as_bytes(s: &str) -> Vec<u8> {
        let mut buffer = vec![];
        buffer.write_all(s.as_bytes()).unwrap();

        buffer.to_vec()
    }

    #[test]
    fn test_row_size() {
        assert_eq!(291, ROWS_SIZE);
    }

    #[test]
    fn test_serialize() {
        let r = Row {
            id: 1,
            username: vector_to_array(str_as_bytes("elo")).unwrap(),
            email: vector_to_array(str_as_bytes("asdasdkpoqkwepoqkwepoqw")).unwrap(),
        };
        let b1 = r.serialize();
        let b2 = r.serialize();

        assert_eq!(b1, b2)
    }

    #[test]
    fn test_deserialize() -> anyhow::Result<()> {
        let r = Row {
            id: 1,
            username: vector_to_array(str_as_bytes("elo")).unwrap(),
            email: vector_to_array(str_as_bytes("asdasdkpoqkwepoqkwepoqw")).unwrap(),
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
    fn test_table() -> anyhow::Result<()> {
        let r1 = Row {
            id: 1,
            username: vector_to_array(str_as_bytes("a".repeat(32).as_str())).unwrap(),
            email: vector_to_array(str_as_bytes("a".repeat(255).as_str())).unwrap(),
        };
        let r2 = Row {
            id: 2,
            username: vector_to_array(str_as_bytes("elo2")).unwrap(),
            email: vector_to_array(str_as_bytes("asdasdkpoqkwepoqkwepoqw2")).unwrap(),
        };
        let r3 = Row {
            id: 3,
            username: vector_to_array(str_as_bytes("elo3")).unwrap(),
            email: vector_to_array(str_as_bytes("asdasdkpoqkwepoqkwepoqw3")).unwrap(),
        };

        let tmp_dir = TempDir::new("databurst")?;
        let file_path = tmp_dir.path().join("my.db");
        File::create(&file_path)?;

        let mut db = Table::db_open(&file_path)?;

        let wanted = vec![r1.clone(), r2.clone(), r3.clone()];

        db.insert(&r1)?;
        db.insert(&r2)?;
        db.insert(&r3)?;

        let mut got = db.collect()?;
        got.sort_by_key(|r| r.id);
        assert_eq!(wanted, got);

        db.close()?;
        let mut db = Table::db_open(&file_path)?;

        let mut got = db.collect()?;
        got.sort_by_key(|r| r.id);
        assert_eq!(wanted, got);

        Ok(())
    }

    #[test]
    fn test_table_multiple_inserts() -> anyhow::Result<()> {
        let mut rows = vec![];
        for i in 0..1000 {
            rows.push(Row {
                id: i,
                username: vector_to_array(str_as_bytes("a".repeat(i as usize % 32).as_str()))
                    .unwrap(),
                email: vector_to_array(str_as_bytes("b".repeat(i as usize % 255).as_str()))
                    .unwrap(),
            })
        }

        let tmp_dir = TempDir::new("databurst")?;
        let file_path = tmp_dir.path().join("my.db");
        File::create(&file_path)?;

        let mut db = Table::db_open(&file_path)?;

        for row in &rows {
            db.insert(row)?;
        }

        let mut got = db.collect()?;
        got.sort_by_key(|r| r.id);
        assert_eq!(rows, got);

        db.close()?;
        let mut db = Table::db_open(&file_path)?;

        let mut got = db.collect()?;
        got.sort_by_key(|r| r.id);
        assert_eq!(rows, got);

        Ok(())
    }
}
