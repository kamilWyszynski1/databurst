use anyhow::{anyhow, bail, Context};
use std::{
    cell::RefCell, collections::HashMap, fmt::Debug, marker::PhantomData, path::Path, rc::Rc,
    str::from_utf8,
};

use crate::{
    constants::{EMAIL_OFFSET, ID_OFFSET, ROWS_SIZE, USERNAME_OFFSET},
    cursor::{Cursor, OperationInfo},
    node::{Key, Node, NodeType},
    pager::Pager,
    row::{Column, ColumnType, TableDefinition},
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

pub trait Serialize {
    fn serialize(&self) -> Vec<u8>;
}

pub trait Deserialize: Sized {
    fn deserialize(data: &[u8]) -> anyhow::Result<Self>;
}

#[derive(PartialOrd, Clone)]
pub struct Row {
    pub id: u32,
    pub username: [u8; 32],
    pub email: [u8; 240],
}

impl From<Row> for HashMap<String, Vec<u8>> {
    fn from(val: Row) -> Self {
        HashMap::from([
            ("id".to_string(), val.id.to_be_bytes().to_vec()),
            ("username".to_string(), val.username.to_vec()),
            ("email".to_string(), val.email.to_vec()),
        ])
    }
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
        let email: [u8; 240] = vector_to_array(value[2].into()).context("could not parse email")?;

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
        let email: [u8; 240] = vector_to_array(email.into()).context("could not parse email")?;

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

impl Serialize for Row {
    fn serialize(&self) -> Vec<u8> {
        let mut buffer = vec![];
        buffer.append(&mut self.id.to_be_bytes().to_vec());
        buffer.append(&mut self.username.to_vec());
        buffer.append(&mut self.email.to_vec());

        assert_eq!(buffer.len(), ROWS_SIZE);

        buffer
    }
}

impl Deserialize for Row {
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

#[derive(Debug, Default, Clone, Copy)]
pub struct RowID {
    pub page_num: u32,
    pub cell_num: u32,
}

impl Serialize for RowID {
    fn serialize(&self) -> Vec<u8> {
        let mut buffer = vec![];
        buffer.append(&mut self.page_num.to_be_bytes().to_vec());
        buffer.append(&mut self.cell_num.to_be_bytes().to_vec());

        buffer
    }
}

impl Deserialize for RowID {
    fn deserialize(data: &[u8]) -> anyhow::Result<Self> {
        let page_num_bytes = &data[0..4];
        let cell_num_bytes = &data[4..8];

        let page_num: u32 = u32::from_be_bytes(
            page_num_bytes
                .try_into()
                .context("cannot convert id_bytes to array")?,
        );
        let cell_num: u32 = u32::from_be_bytes(
            cell_num_bytes
                .try_into()
                .context("cannot convert id_bytes to array")?,
        );

        Ok(Self { page_num, cell_num })
    }
}

#[derive(Debug)]
pub struct Table<K, V> {
    pub root_page_num: u32,
    pub root_index_num: u32,
    pub pager: Rc<RefCell<Pager>>,

    /// Describes table's schema.
    pub table_definition: Option<TableDefinition>,

    marker: PhantomData<(K, V)>,
}

impl<K, V> Table<K, V> {
    pub fn db_open<P: AsRef<Path>>(p: P) -> anyhow::Result<Self> {
        let mut pager = Pager::new(p)?;

        if pager.num_pages == 0 {
            // new database, need to initialize
            {
                let root = pager.get_page(0)?;
                let node = Node::new(
                    NodeType::Leaf {
                        kvs: vec![],
                        next_leaf: None,
                    },
                    true,
                    false,
                    None,
                );
                root.borrow_mut().data = node.try_into()?;
            }

            {
                let index_root = pager.get_page(1)?;
                let node = Node::new(
                    NodeType::Leaf {
                        kvs: vec![],
                        next_leaf: None,
                    },
                    true,
                    true,
                    None,
                );
                index_root.borrow_mut().data = node.try_into()?;
            }
        }

        let table_definition = pager.read_table_definition()?;

        Ok(Self {
            root_page_num: 0,
            root_index_num: 1,
            pager: Rc::new(RefCell::new(pager)),
            marker: PhantomData,
            table_definition,
        })
    }

    fn update_index_for_node(&mut self, page_num: u32, node: Node) -> anyhow::Result<()> {
        match node.node_type {
            NodeType::Internal {
                right_child: _,
                child_pointer_pairs: _,
            } => {
                bail!("could not update index for Interal node");
            }
            NodeType::Leaf { kvs, next_leaf: _ } => {
                for (cell_num, (Key(key), _)) in kvs.into_iter().enumerate() {
                    let row_id = RowID {
                        page_num,
                        cell_num: cell_num as u32,
                    };
                    let cursor = self.cursor_find(self.root_index_num, key)?;
                    cursor.insert(key, &row_id.serialize())?;
                }
            }
        }
        Ok(())
    }

    /// Consumes Table and saves all content to file.
    pub fn close(self) -> anyhow::Result<()> {
        Rc::try_unwrap(self.pager)
            .unwrap()
            .into_inner()
            .flush(self.table_definition)
    }

    pub fn cursor_start(&mut self) -> anyhow::Result<Cursor> {
        let page_num = self.root_page_num;
        let cell_num = 0;

        Ok(Cursor::new(self.pager.clone(), page_num, cell_num))
    }

    /// Return the position of the given key.
    /// If the key is not present, return the position where it should be inserted.
    fn cursor_find(&mut self, page_num: u32, key: u32) -> anyhow::Result<Cursor> {
        let root_page = self.pager.borrow_mut().get_page(page_num)?;
        let root_node = Node::try_from(root_page.borrow().clone())?;
        let mut cursor = Cursor::new(self.pager.clone(), page_num, 0);

        match root_node.node_type {
            NodeType::Internal {
                right_child,
                child_pointer_pairs,
            } => {
                let inx = child_pointer_pairs
                    .binary_search_by_key(&key, |(_, k)| k.0)
                    .unwrap_or_else(|x| x);

                if inx == child_pointer_pairs.len() {
                    self.cursor_find(right_child.0, key)
                } else {
                    self.cursor_find(
                        child_pointer_pairs
                            .get(inx)
                            .context("could not get value by index after binary search")?
                            .0
                             .0,
                        key,
                    )
                }
            }
            NodeType::Leaf { kvs, next_leaf: _ } => {
                let inx = kvs
                    .binary_search_by_key(&key, |(k, _)| k.0)
                    .unwrap_or_else(|x| x);
                cursor.cell_num = inx as u32;
                Ok(cursor)
            }
        }
    }
}

impl<K, V> Table<K, V>
where
    V: Deserialize + Debug,
{
    pub fn select(&mut self) -> anyhow::Result<()> {
        self.collect()?
            .into_iter()
            .for_each(|r| println!("{:?}", r));

        Ok(())
    }
}

impl<K, V> Table<K, V>
where
    V: Deserialize,
{
    /// Searches for particular saved row.
    pub fn search(&mut self, id: u32) -> anyhow::Result<Option<V>> {
        let index_cursor = self.cursor_find(self.root_index_num, id)?;
        let row_cursor = match index_cursor.data()? {
            Some(data) => {
                let index = RowID::deserialize(&data)?;
                Cursor::new(self.pager.clone(), index.page_num, index.cell_num)
            }
            None => self.cursor_find(self.root_page_num, id)?,
        };

        Ok(match row_cursor.data()? {
            Some(data) => Some(V::deserialize(&data)?),
            None => None,
        })
    }

    pub fn collect(&mut self) -> anyhow::Result<Vec<V>> {
        let mut cursor = self.cursor_start()?;

        let data = cursor.select()?;

        Ok(data
            .into_iter()
            .map(|bytes| V::deserialize(&bytes).unwrap())
            .collect())
    }

    #[cfg(test)]
    fn print(&self, page_num: u32, ident: String) -> anyhow::Result<()> {
        use crate::node::Pointer;

        let node = Node::try_from(self.pager.borrow_mut().get_page(page_num)?)?;

        match node.node_type {
            NodeType::Internal {
                right_child,
                child_pointer_pairs,
            } => {
                println!(
                    "{ident}({page_num}) internal [root: {}, inx: {}, parent: {}] ({:?}, key {:?})",
                    node.is_root,
                    node.is_index,
                    node.parent.map(|x| x.to_string()).unwrap_or_default(),
                    child_pointer_pairs
                        .iter()
                        .map(|(Pointer(pointer), Key(key))| (*pointer, *key))
                        .collect::<Vec<(u32, u32)>>(),
                    right_child
                );
                for (pointer, _) in child_pointer_pairs {
                    self.print(pointer.0, format!(" {}", ident))?;
                }
                self.print(right_child.0, format!(" {}", ident))?;
            }
            NodeType::Leaf { kvs, next_leaf } => {
                if node.is_index {
                    println!(
                        "{ident}({page_num}) leaf: [parent: {}, inx: {}](kvs: {:?}, next_leaf: {:?})",
                        node.parent.map(|x| x.to_string()).unwrap_or_default(),
                        node.is_index,
                        kvs.iter().map(|(Key(key), data)| (key, RowID::deserialize(data).unwrap())).map(|(key, row_id)| format!("{} -> ({}, {})", key, row_id.page_num, row_id.cell_num)).collect::<Vec<String>>(),
                        next_leaf,
                    )
                } else {
                    println!(
                        "{ident}({page_num}) leaf: [parent: {}, inx: {}](kvs: {:?}, next_leaf: {:?})",
                        node.parent.map(|x| x.to_string()).unwrap_or_default(),
                        node.is_index,
                        kvs.iter().map(|(key, _)| key.0).collect::<Vec<u32>>(),
                        next_leaf,
                    )
                }
            }
        }
        Ok(())
    }
}

impl<K, V> Table<K, V>
where
    V: Serialize,
{
    /// Inserts new row.
    pub fn insert(&mut self, values: HashMap<String, Vec<u8>>) -> anyhow::Result<()> {
        // ===== CHECK DATA ===== //
        self.check_data_type_coercion(&values)?;

        let key = {
            let id_value: Vec<u8> = values
                .get("id")
                .context("every table has to have 'id' column")?
                .clone();
            u32::from_be_bytes(id_value[0..4].try_into()?)
        };

        // ===== PREPARE DATA ===== //
        let mut data = vec![];
        for Column {
            name,
            column_type: _,
        } in self.table_definition.clone().unwrap().columns
        {
            data.append(&mut values.get(&name).unwrap().clone())
        }

        // ===== INSERT DATA ===== //
        let page = self
            .pager
            .borrow_mut()
            .get_page(self.root_page_num)
            .with_context(|| format!("could not read {} page", self.root_page_num))?;
        let node =
            Node::try_from(page.borrow().clone()).context("could not create Node from Page")?;

        let num_cells = node.num_cells();
        let cursor = self.cursor_find(self.root_page_num, key)?;

        if cursor.cell_num < num_cells {
            if let Some(key_at_index) = node.leaf_node_key(cursor.cell_num)? {
                if key_at_index == key {
                    bail!("duplicate key!")
                }
            }
        }
        // cursor.insert(key, &data)?;
        match cursor.insert(key, &data)? {
            OperationInfo::Insert {
                split_occurred,
                metadata,
            } => {
                if split_occurred {
                    let metadata = metadata.context("SplitMetadata should be filled")?;
                    let left_node =
                        Node::try_from(self.pager.borrow_mut().get_page(metadata.new_left)?)?;
                    self.update_index_for_node(metadata.new_left, left_node)?;

                    let right_node =
                        Node::try_from(self.pager.borrow_mut().get_page(metadata.new_right)?)?;
                    self.update_index_for_node(metadata.new_right, right_node)?;
                } else {
                    let row_id = RowID {
                        page_num: cursor.page_num,
                        cell_num: cursor.cell_num,
                    };
                    self.cursor_find(self.root_index_num, key)?
                        .insert(key, &row_id.serialize())?;
                }
            }
            OperationInfo::Replace => {}
        }

        Ok(())
    }

    /// Checks mapping with table definition and verifies if type casting can be performed.
    fn check_data_type_coercion(&self, values: &HashMap<String, Vec<u8>>) -> anyhow::Result<()> {
        let td = self.table_definition.clone().unwrap();

        let columns: HashMap<String, ColumnType> = td
            .columns
            .into_iter()
            .map(|c| (c.name, c.column_type))
            .collect();

        for (k, value) in values.iter() {
            let column_type = columns
                .get(k)
                .with_context(|| format!("{} key not found in table definition", k))?;

            match column_type {
                ColumnType::Integer => {
                    assert_eq!(4, value.len());
                    i32::from_be_bytes(value[0..4].try_into()?);
                }
                ColumnType::Text { size } => {
                    dbg!(size);
                    dbg!(value.len());
                    assert!(*size as usize >= value.len());
                    String::from_utf8(value.to_vec())?;
                }
                ColumnType::Bool => {
                    assert_eq!(1, value.len());
                    assert!(value[0] == 0 || value[1] == 1)
                }
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
    dbg!(missing);
    v.append(&mut (0..missing).map(|_| T::default()).collect());

    let t: Result<[T; N], _> = v.try_into();

    match t {
        Ok(t) => Ok(t),
        Err(_) => bail!("could not convert vector to array"),
    }
}

#[cfg(test)]
mod tests {
    use anyhow::{Context, Ok};
    use tempdir::TempDir;

    use super::{vector_to_array, Row, Table};
    use crate::{
        row::{Column, ColumnType, TableDefinition},
        table::{Deserialize, Serialize},
    };
    use std::{fs::File, io::Write};

    pub fn str_as_bytes(s: &str) -> Vec<u8> {
        let mut buffer = vec![];
        buffer.write_all(s.as_bytes()).unwrap();

        buffer.to_vec()
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
            email: vector_to_array(str_as_bytes("a".repeat(239).as_str())).unwrap(),
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

        let mut db: Table<u32, Row> = Table::db_open(&file_path)?;
        db.table_definition = Some(TableDefinition {
            name: "test".to_string(),
            columns: vec![
                Column::new("id", ColumnType::Integer)?,
                Column::new("username", ColumnType::Text { size: 32 })?,
                Column::new("email", ColumnType::Text { size: 240 })?,
            ],
        });

        let wanted = vec![r1.clone(), r2.clone(), r3.clone()];

        db.insert(r1.into()).context("could not insert r1")?;
        db.insert(r3.into())?;
        db.insert(r2.into())?;

        let got = db.collect()?;
        assert_eq!(wanted, got);

        db.close()?;
        let mut db: Table<u32, Row> = Table::db_open(&file_path)?;

        let got = db.collect()?;
        assert_eq!(wanted, got);

        Ok(())
    }

    #[test]
    fn test_insert_dupliacate() -> anyhow::Result<()> {
        let r1 = Row {
            id: 1,
            username: vector_to_array(str_as_bytes("a".repeat(32).as_str())).unwrap(),
            email: vector_to_array(str_as_bytes("a".repeat(240).as_str())).unwrap(),
        };

        let tmp_dir = TempDir::new("databurst")?;
        let file_path = tmp_dir.path().join("my.db");
        File::create(&file_path)?;

        let mut db: Table<u32, Row> = Table::db_open(&file_path)?;
        db.table_definition = Some(TableDefinition {
            name: "test".to_string(),
            columns: vec![
                Column::new("id", ColumnType::Integer)?,
                Column::new("username", ColumnType::Text { size: 32 })?,
                Column::new("email", ColumnType::Text { size: 240 })?,
            ],
        });

        db.insert(r1.clone().into())?;

        assert!(db
            .insert(r1.into())
            .unwrap_err()
            .to_string()
            .contains("duplicate key!"));

        Ok(())
    }

    #[test]
    fn test_table_multiple_inserts() -> anyhow::Result<()> {
        let mut rows = vec![];
        for i in 1..=50 {
            rows.push(Row {
                id: i,
                username: vector_to_array(str_as_bytes("a".repeat(i as usize % 32).as_str()))
                    .unwrap(),
                email: vector_to_array(str_as_bytes("b".repeat(i as usize % 240).as_str()))
                    .unwrap(),
            })
        }

        let tmp_dir = TempDir::new("databurst")?;
        let file_path = tmp_dir.path().join("my.db");
        File::create(&file_path)?;

        let mut db: Table<u32, Row> = Table::db_open(&file_path)?;
        db.table_definition = Some(TableDefinition {
            name: "test".to_string(),
            columns: vec![
                Column::new("id", ColumnType::Integer)?,
                Column::new("username", ColumnType::Text { size: 32 })?,
                Column::new("email", ColumnType::Text { size: 240 })?,
            ],
        });

        for row in rows {
            db.insert(row.into())?;
        }

        db.print(db.root_page_num, "".to_string())?;
        println!();
        db.print(db.root_index_num, "".to_string())?;

        let rows = db.collect()?;
        assert_eq!(rows.len(), 50);

        let row = db.search(10)?.unwrap();
        assert_eq!(
            row.email,
            vector_to_array(str_as_bytes("b".repeat(10).as_str()))?
        );
        assert_eq!(
            row.username,
            vector_to_array(str_as_bytes("a".repeat(10).as_str()))?
        );

        let row = db.search(100)?;
        assert!(row.is_none());

        let row = db.search(50)?;
        assert!(row.is_some());

        db.close()?;

        Ok(())
    }

    #[test]
    fn test_table_definition() -> anyhow::Result<()> {
        let tmp_dir = TempDir::new("databurst")?;
        let file_path = tmp_dir.path().join("my.db");
        dbg!(&file_path);
        File::create(&file_path)?;

        let td = TableDefinition {
            name: "test".to_string(),
            columns: vec![
                Column::new("column", ColumnType::Integer)?,
                Column::new("column2", ColumnType::Bool)?,
                Column::new("column3", ColumnType::Integer)?,
                Column::new("column4", ColumnType::Text { size: 200 })?,
                Column::new("column4", ColumnType::Text { size: 240 })?,
            ],
        };

        let mut db: Table<u32, Row> = Table::db_open(&file_path)?;
        db.table_definition = Some(td.clone());
        db.close()?;

        let db2: Table<u32, Row> = Table::db_open(&file_path)?;
        assert_eq!(td, db2.table_definition.unwrap());

        Ok(())
    }
}
