use anyhow::{anyhow, bail, Context};
use std::{
    cell::RefCell, collections::HashMap, fmt::Debug, marker::PhantomData, path::Path, rc::Rc,
    str::from_utf8,
};

use crate::{
    constants::{
        EMAIL_OFFSET, ID_OFFSET, LEAF_INDEX_NODE_CELL_SIZE, LEAF_NODE_KEY_SIZE, USERNAME_OFFSET,
    },
    cursor::{Cursor, OperationInfo},
    node::{Key, Node, NodeType, Pointer},
    pager::Pager,
    row::{Column, ColumnType, TableDefinition},
    statements::WhereStmt,
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

impl Serialize for Vec<u8> {
    fn serialize(&self) -> Vec<u8> {
        self.clone()
    }
}

pub trait Deserialize: Sized {
    fn deserialize(data: &[u8]) -> anyhow::Result<Self>;
    fn deserialize_key(data: &[u8]) -> String;
}

impl Deserialize for Vec<u8> {
    fn deserialize(data: &[u8]) -> anyhow::Result<Self> {
        Ok(data.to_vec())
    }
    fn deserialize_key(data: &[u8]) -> String {
        format!("{:?}", data)
    }
}

#[derive(PartialOrd, Clone)]
pub struct Row {
    pub id: u32,
    pub username: [u8; 32],
    pub email: [u8; 240],
}

impl Row {
    const fn size() -> usize {
        ID_SIZE + USERNAME_SIZE + EMAIL_SIZE
    }
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

        assert_eq!(buffer.len(), Self::size());

        buffer
    }
}

impl Deserialize for Row {
    fn deserialize(data: &[u8]) -> anyhow::Result<Row> {
        if data.len() < Self::size() {
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
    fn deserialize_key(data: &[u8]) -> String {
        match String::from_utf8(data.to_vec()) {
            Ok(r) => r.replace('\0', ""),
            Err(_) => format!("{:?}", data),
        }
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
    fn deserialize_key(data: &[u8]) -> String {
        match Self::deserialize(data) {
            Ok(r) => format!("{}:{}", r.page_num, r.cell_num),
            Err(_) => format!("{:?}", data),
        }
    }
}

type SafePager = Rc<RefCell<Pager>>;

// TODO: these should be stored somehow
#[derive(Debug)]
pub struct Indexes {
    /// Set of columns names to be indexed and their page numbers.
    pub columns: HashMap<String, u32>,
}

impl Default for Indexes {
    fn default() -> Self {
        Self {
            columns: HashMap::from([("id".to_string(), 1)]),
        }
    }
}

#[derive(Debug)]
pub struct Table<K, V> {
    pub root_page_num: u32,
    pub pager: SafePager,

    /// Describes table's schema.
    //TODO: add in constructor and validate if definition has 'id' column.
    pub table_definition: TableDefinition,

    indexes: Indexes,

    marker: PhantomData<(K, V)>,
}

impl<K, V> Table<K, V> {
    pub fn new<P: AsRef<Path>>(p: P, table_definition: TableDefinition) -> anyhow::Result<Self> {
        let mut pager = Pager::new(p)?;

        if pager.num_pages == 0 {
            // new database, need to initialize
            {
                let root = pager.get_page(0, LEAF_NODE_KEY_SIZE, table_definition.size())?;
                let node = Node::new(
                    NodeType::Leaf {
                        kvs: vec![],
                        next_leaf: None,
                    },
                    true,
                    false,
                    None,
                    LEAF_NODE_KEY_SIZE,
                    table_definition.size(),
                );
                root.borrow_mut().data = node.try_into()?;
            }

            {
                // TODO: share writer to a file, do not open another one
                // index root page num is saved in Indexes as default for 'id' column
                let index_root =
                    pager.get_page(1, LEAF_NODE_KEY_SIZE, LEAF_INDEX_NODE_CELL_SIZE)?;
                let node = Node::new(
                    NodeType::Leaf {
                        kvs: vec![],
                        next_leaf: None,
                    },
                    true,
                    true,
                    None,
                    LEAF_NODE_KEY_SIZE,
                    LEAF_INDEX_NODE_CELL_SIZE,
                );
                index_root.borrow_mut().data = node.try_into()?;
            }
        }

        Ok(Self {
            root_page_num: 0,
            pager: Rc::new(RefCell::new(pager)),
            marker: PhantomData,
            table_definition,
            indexes: Indexes::default(),
        })
    }

    /// Reads table definition, root and index page from file.
    pub fn db_open<P: AsRef<Path> + Clone>(p: P) -> anyhow::Result<Self> {
        let mut pager = Pager::new(p.clone())?;

        let table_definition = pager
            .read_table_definition()?
            .context("table definition not persisted")?;

        Self::new(p, table_definition)
    }

    fn column_byte_size(&self, column: &str) -> Option<usize> {
        self.table_definition
            .columns
            .iter()
            .find(|c| c.name == column)
            .map(|c| c.column_type.byte_size())
    }

    // TODO: implement updating index when data already exist.
    fn add_indexed_column(&mut self, column: String) -> anyhow::Result<()> {
        if self.indexes.columns.contains_key(&column) {
            return Ok(());
        }
        let column_size = self
            .column_byte_size(&column)
            .context("could not find column in TableDefinition")?;

        let index_page_num = self.pager.borrow_mut().get_unused_page_num();
        let index_page = self.pager.borrow_mut().get_page(
            index_page_num,
            column_size,
            LEAF_INDEX_NODE_CELL_SIZE,
        )?;
        let node = Node::new(
            NodeType::Leaf {
                kvs: vec![],
                next_leaf: None,
            },
            true,
            true,
            None,
            column_size,
            LEAF_INDEX_NODE_CELL_SIZE,
        );
        index_page.borrow_mut().data = node.try_into()?;

        self.indexes.columns.insert(column, index_page_num);

        Ok(())
    }

    fn update_index_for_node(
        &mut self,
        old_page_num: u32,
        page_num: u32,
        node: Node,
    ) -> anyhow::Result<()> {
        match node.node_type {
            NodeType::Internal {
                child_pointer_pairs: _,
            } => {
                bail!("could not update index for Interal node");
            }
            NodeType::Leaf { kvs, next_leaf: _ } => {
                // TODO: if there are indexes on different columns that 'id' we need to divide
                // data bytes into proper 'keys' to use them in indexing
                for (cell_num, (key, data)) in kvs.into_iter().enumerate() {
                    let row_id = RowID {
                        page_num,
                        cell_num: cell_num as u32,
                    };

                    let index_columns = self.indexes.columns.clone(); // TODO: refactor
                    for (index_column, index_page_num) in index_columns {
                        let index_key: Key = if index_column == "id" {
                            key.clone()
                        } else {
                            extract_column_bytes_from_data(
                                &data,
                                &index_column,
                                &self.table_definition,
                            )?
                            .into()
                        };

                        let cursor =
                            self.cursor_find(index_page_num, &index_key, LEAF_NODE_KEY_SIZE)?;
                        cursor.insert(index_key, &row_id.serialize())?;
                    }
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
    fn cursor_find(&mut self, page_num: u32, key: &Key, row_size: usize) -> anyhow::Result<Cursor> {
        let root_page = self
            .pager
            .borrow_mut()
            .get_page(page_num, key.0.len(), row_size)?;
        let root_node = Node::try_from(root_page.borrow().clone())?;
        let mut cursor = Cursor::new(self.pager.clone(), page_num, 0);

        match root_node.node_type {
            NodeType::Internal {
                child_pointer_pairs,
            } => {
                let mut inx = child_pointer_pairs
                    .binary_search_by_key(&key, |(_, k)| k)
                    .unwrap_or_else(|x| x);

                if inx >= child_pointer_pairs.len() {
                    inx = child_pointer_pairs.len() - 1;
                }
                let page_from_child = child_pointer_pairs
                    .get(inx)
                    .context("could not get value by index after binary search")?
                    .0
                     .0;
                self.cursor_find(page_from_child, key, row_size)
            }
            NodeType::Leaf { kvs, next_leaf: _ } => {
                let inx = kvs
                    .binary_search_by_key(&key, |(k, _)| k)
                    .unwrap_or_else(|x| x);
                cursor.cell_num = inx as u32;

                Ok(cursor)
            }
        }
    }

    // Extended version on cursor_find that should be used when searching through index.
    fn multiple_cursor_find(
        &mut self,
        page_num: u32,
        key: &Key,
        row_size: usize,
    ) -> anyhow::Result<Vec<Cursor>> {
        let root_page = self
            .pager
            .borrow_mut()
            .get_page(page_num, key.0.len(), row_size)?;
        let root_node = Node::try_from(root_page.borrow().clone())?;

        match root_node.node_type {
            NodeType::Internal {
                child_pointer_pairs,
            } => {
                let inx = child_pointer_pairs
                    .binary_search_by_key(&key, |(_, k)| k)
                    .unwrap_or_else(|x| x);

                let page_from_child = child_pointer_pairs
                    .get(inx)
                    .context("could not get value by index after binary search")?
                    .0
                     .0;
                self.multiple_cursor_find(page_from_child, key, row_size)
            }
            NodeType::Leaf { kvs, next_leaf: _ } => {
                let cells: Vec<usize> = kvs
                    .into_iter()
                    .enumerate()
                    .map(|(inx, (k, _))| (inx, k))
                    .filter(|(_, k)| k == key)
                    .map(|(inx, _)| inx)
                    .collect();

                let mut cursors = vec![];
                for cell in cells {
                    cursors.push(Cursor::new(self.pager.clone(), page_num, cell as u32));
                }
                Ok(cursors)
            }
        }
    }
}

fn extract_column_bytes_from_data(
    data: &[u8],
    column: &str,
    td: &TableDefinition,
) -> anyhow::Result<Vec<u8>> {
    let (from, to) = td.column_byte_range(column)?;
    Ok(data[from..to].to_vec())
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
    pub fn search_with_where(&mut self, where_stmt: WhereStmt) -> anyhow::Result<Option<Vec<V>>> {
        let key_size = self
            .column_byte_size(&where_stmt.column)
            .context("column size not found")?;

        // TODO: refactor - we can simply find first cursor on the very bottom, then
        // go to the right till key differs, this way we will get all of needed RowIDs
        let mut cursors: Vec<Cursor> = match self.column_index(&where_stmt.column) {
            Some(page_num) => {
                // prepare where_stmt value

                let mut where_value = where_stmt.value.clone();
                where_value.append(&mut vec![0u8; key_size - where_stmt.value.len()]);

                let mut index_cursor = Cursor::new(self.pager.clone(), page_num, 0);

                // // indexed column
                // let index_cursor =
                //     self.cursor_find(page_num, &where_value.into(), LEAF_INDEX_NODE_CELL_SIZE)?;
                // let key_size = self
                //     .column_byte_size(&where_stmt.column)
                //     .context("could not get column byte size")?;

                // // try to use index
                // match self.index_cursor_to_row_cursor(index_cursor, key_size)? {
                //     Some(cursor) => cursor,
                //     None => self.cursor_start()?, // sequential scan
                // }
                index_cursor
                    .select_by_key(
                        |key: &Vec<u8>| -> bool {
                            {
                                key == &where_value
                            }
                        },
                        where_value.len(),
                        LEAF_INDEX_NODE_CELL_SIZE,
                    )?
                    .into_iter()
                    .map(|v| RowID::deserialize(&v).unwrap())
                    .map(|r| Cursor::new(self.pager.clone(), r.page_num, r.cell_num))
                    .collect()
            }
            None => {
                // sequential scan
                // vec![self.cursor_start()?]
                let data = self.cursor_start()?.select_by(
                    where_stmt.get_cmp(&self.table_definition)?,
                    LEAF_NODE_KEY_SIZE,
                    self.table_definition.size(),
                )?;
                if data.is_empty() {
                    return Ok(None);
                }
                let parsed: Vec<V> = data
                    .into_iter()
                    .map(|v| V::deserialize(&v).unwrap())
                    .collect();
                return Ok(Some(parsed));
            }
        };

        let mut rows: Vec<V> = vec![];
        for cursor in cursors {
            match cursor.data(key_size, self.table_definition.size())? {
                Some(data) => rows.push(V::deserialize(&data)?),
                None => eprintln!("could not find"),
            }
        }
        Ok(Some(rows))
    }

    /// Searches for particular saved row.
    pub fn search(&mut self, key: Key) -> anyhow::Result<Option<V>> {
        let index_cursor = self.cursor_find(1, &key, LEAF_INDEX_NODE_CELL_SIZE)?;
        let row_cursor = match self.index_cursor_to_row_cursor(index_cursor, key.0.len())? {
            Some(cursor) => cursor,
            None => self.cursor_find(self.root_page_num, &key, self.table_definition.size())?,
        };

        Ok(
            match row_cursor.data(key.0.len(), self.table_definition.size())? {
                Some(data) => Some(V::deserialize(&data)?),
                None => None,
            },
        )
    }

    /// Converts index cursor to row cursor by extracting saved RowID.
    fn index_cursor_to_row_cursor(
        &mut self,
        index_cursor: Cursor,
        key_size: usize,
    ) -> anyhow::Result<Option<Cursor>> {
        match index_cursor.data(key_size, LEAF_INDEX_NODE_CELL_SIZE)? {
            Some(data) => {
                let index = RowID::deserialize(&data)?;
                Ok(Some(Cursor::new(
                    self.pager.clone(),
                    index.page_num,
                    index.cell_num,
                )))
            }
            None => Ok(None),
        }
    }

    /// Converts index cursor to row cursor by extracting saved RowID.
    fn index_cursors_to_row_cursor(
        &mut self,
        index_cursor: Vec<Cursor>,
        key_size: usize,
    ) -> anyhow::Result<Option<Vec<Cursor>>> {
        let mut results = vec![];
        for cursor in index_cursor {
            match cursor.data(key_size, LEAF_INDEX_NODE_CELL_SIZE)? {
                Some(data) => {
                    let index = RowID::deserialize(&data)?;
                    results.push(Cursor::new(
                        self.pager.clone(),
                        index.page_num,
                        index.cell_num,
                    ));
                }
                None => {
                    panic!("should not happen")
                }
            }
        }
        Ok(Some(results))
    }

    fn column_index(&self, column: &str) -> Option<u32> {
        self.indexes.columns.get(column).copied()
    }

    pub fn collect(&mut self) -> anyhow::Result<Vec<V>> {
        let mut cursor = self.cursor_start()?;

        // TODO: refactor
        let data = cursor.select(LEAF_NODE_KEY_SIZE, self.table_definition.size())?;

        Ok(data
            .into_iter()
            .map(|bytes| V::deserialize(&bytes).unwrap())
            .collect())
    }

    #[cfg(test)]
    fn print_short(&self, page_num: u32, ident: String) -> anyhow::Result<()> {
        let node = Node::try_from(self.pager.borrow_mut().get_page(
            page_num,
            LEAF_NODE_KEY_SIZE,
            self.table_definition.size(),
        )?)?;
        print!(
            "{ident}({page_num}) internal [root: {}, inx: {}, parent: {}]",
            node.is_root,
            node.is_index,
            node.parent.map(|x| x.to_string()).unwrap_or_default()
        );

        match node.node_type {
            NodeType::Internal {
                child_pointer_pairs,
            } => {
                print!(
                    " ({:?})",
                    child_pointer_pairs
                        .iter()
                        .map(|(Pointer(pointer), key)| (*pointer, V::deserialize_key(&key.0)))
                        .collect::<Vec<(u32, String)>>(),
                );
            }
            NodeType::Leaf { kvs, next_leaf } => {
                if !kvs.is_empty() {
                    if kvs[0].0 .0.len() == 4 {
                        let keys: Vec<u32> = kvs
                            .into_iter()
                            .map(|(Key(key), _)| u32::from_be_bytes(key[0..4].try_into().unwrap()))
                            .collect();
                        print!("({:?})", keys);
                    } else if kvs[0].0 .0.len() == 32 {
                        let keys: Vec<String> = kvs
                            .into_iter()
                            .map(|(Key(key), _)| String::from_utf8(key).unwrap().replace('\0', ""))
                            .collect();
                        print!("({:?})", keys);
                    }
                }
                print!("({:?})", next_leaf)
            }
        }
        println!();
        Ok(())
    }

    #[cfg(test)]
    fn print(&self, page_num: u32, ident: String) -> anyhow::Result<()> {
        let node = Node::try_from(self.pager.borrow_mut().get_page(
            page_num,
            LEAF_NODE_KEY_SIZE,
            self.table_definition.size(),
        )?)?;

        match node.node_type {
            NodeType::Internal {
                mut child_pointer_pairs,
            } => {
                child_pointer_pairs.sort_by_key(|(_, k)| k.clone());
                println!(
                    "{ident}({page_num}) internal [root: {}, inx: {}, parent: {}] ({:?})",
                    node.is_root,
                    node.is_index,
                    node.parent.map(|x| x.to_string()).unwrap_or_default(),
                    child_pointer_pairs
                        .iter()
                        .map(|(Pointer(pointer), key)| (*pointer, V::deserialize_key(&key.0)))
                        .collect::<Vec<(u32, String)>>(),
                );
                for (pointer, _) in child_pointer_pairs {
                    self.print(pointer.0, format!(" {}", ident))?;
                }
            }
            NodeType::Leaf { kvs, next_leaf } => {
                if node.is_index {
                    println!(
                        "{ident}({page_num}) leaf: [parent: {}, inx: {}](kvs: {:?} next_leaf: {:?})",
                        node.parent.map(|x| x.to_string()).unwrap_or_default(),
                        node.is_index,
                        kvs.iter().map(|(Key(key), data)| (V::deserialize_key(key), RowID::deserialize(data).unwrap())).map(|(key, row_id)| format!("{:?} -> ({}, {})", key, row_id.page_num, row_id.cell_num)).collect::<Vec<String>>(),
                        next_leaf,
                    )
                } else {
                    println!(
                        "{ident}({page_num}) leaf: [parent: {}, inx: {}]({:?} next_leaf: {:?})",
                        node.parent.map(|x| x.to_string()).unwrap_or_default(),
                        node.is_index,
                        kvs.iter().map(|(key, _)| key.clone()).collect::<Vec<Key>>(),
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

        let key: Key = values
            .get("id")
            .context("every table has to have 'id' column")?
            .clone()
            .into();

        // ===== PREPARE DATA ===== //
        let mut data = vec![];
        for Column { name, column_type } in self.table_definition.columns.clone() {
            let mut bytes = values
                .get(&name)
                .with_context(|| format!("missing '{}' column value", name))?
                .clone();

            if let ColumnType::Text { size } = column_type {
                bytes.append(&mut vec![0u8; size as usize - bytes.len()]); // fill to column's size
            };
            data.append(&mut bytes)
        }

        // ===== INSERT DATA ===== //
        let cursor = self.cursor_find(self.root_page_num, &key, data.len())?;

        match cursor.insert(key.clone(), &data)? {
            OperationInfo::Insert {
                split_occurred,
                metadata,
            } => {
                if split_occurred {
                    let metadata = metadata.context("SplitMetadata should be filled")?;

                    // We need to go through all of left nodes key-values and *update* indexes.
                    // We will find every index's value of given key/value from new node,
                    // and update it with new page+cell values using metadata and order from new nodes.

                    let left_node = Node::try_from(self.pager.borrow_mut().get_page(
                        metadata.new_left,
                        key.0.len(),
                        data.len(),
                    )?)?;
                    self.update_index_for_node(metadata.old, metadata.new_left, left_node)?;

                    let right_node = Node::try_from(self.pager.borrow_mut().get_page(
                        metadata.new_right,
                        key.0.len(),
                        data.len(),
                    )?)?;
                    self.update_index_for_node(metadata.old, metadata.new_right, right_node)?;
                } else {
                    let row_id = RowID {
                        page_num: cursor.page_num,
                        cell_num: cursor.cell_num,
                    };

                    let index_columns = self.indexes.columns.clone(); //TODO: refactor
                    for (index_column, index_page_num) in index_columns {
                        let indexed_key: Key = values
                            .get(&index_column)
                            .context("there's no indexed column in values")?
                            .clone()
                            .into();

                        let c = self.cursor_find(
                            index_page_num,
                            &indexed_key,
                            LEAF_INDEX_NODE_CELL_SIZE,
                        )?;
                        c.insert(indexed_key, &row_id.serialize())?;
                    }
                }
            }
            OperationInfo::Replace => {}
        }

        Ok(())
    }

    /// Checks mapping with table definition and verifies if type casting can be performed.
    fn check_data_type_coercion(&self, values: &HashMap<String, Vec<u8>>) -> anyhow::Result<()> {
        let td = self.table_definition.clone();

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
                    assert!(*size as usize >= value.len());
                    String::from_utf8(value.to_vec())?;
                }
                ColumnType::Bool => {
                    assert_eq!(1, value.len());
                    assert!(value[0] == 0 || value[0] == 1)
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
    v.append(&mut (0..missing).map(|_| T::default()).collect());

    let t: Result<[T; N], _> = v.try_into();

    match t {
        Ok(t) => Ok(t),
        Err(_) => bail!("could not convert vector to array"),
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Context;
    use tempdir::TempDir;

    use super::{vector_to_array, Row, Table};
    use crate::{
        row::{Column, ColumnType, TableDefinition},
        statements::WhereStmt,
        table::{Deserialize, Serialize},
    };
    use std::{collections::HashMap, fs::File, io::Write};

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

        let mut db: Table<u32, Row> = Table::new(
            &file_path,
            TableDefinition {
                name: "test".to_string(),
                columns: vec![
                    Column::new("id", ColumnType::Integer)?,
                    Column::new("username", ColumnType::Text { size: 32 })?,
                    Column::new("email", ColumnType::Text { size: 240 })?,
                ],
            },
        )?;

        let wanted = vec![r1.clone(), r2.clone(), r3.clone()];

        db.insert(r1.into()).context("could not insert r1")?;
        db.insert(r3.into())?;
        db.insert(r2.into())?;

        db.print(1, "".to_string())?;

        let got = db.collect()?;
        assert_eq!(wanted, got);

        db.close()?;
        let mut db: Table<u32, Row> = Table::db_open(&file_path)?;

        let got = db.collect()?;
        assert_eq!(wanted, got);

        Ok(())
    }

    #[test]
    fn test_insert_duplicate() -> anyhow::Result<()> {
        let r1 = Row {
            id: 1,
            username: vector_to_array(str_as_bytes("a".repeat(32).as_str())).unwrap(),
            email: vector_to_array(str_as_bytes("a".repeat(240).as_str())).unwrap(),
        };

        let tmp_dir = TempDir::new("databurst")?;
        let file_path = tmp_dir.path().join("my.db");
        File::create(&file_path)?;

        let td = TableDefinition {
            name: "test".to_string(),
            columns: vec![
                Column::new("id", ColumnType::Integer)?,
                Column::new("username", ColumnType::Text { size: 32 })?,
                Column::new("email", ColumnType::Text { size: 240 })?,
            ],
        };

        let mut db: Table<u32, Row> = Table::new(&file_path, td)?;

        db.insert(r1.clone().into())?;
        db.insert(r1.into())?;

        db.select()?;

        db.print(0, "".to_string())?;
        //
        // assert!(db
        //     .insert(r1.into())
        //     .unwrap_err()
        //     .to_string()
        //     .contains("duplicate key!"));

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

        let mut db: Table<u32, Row> = Table::new(
            &file_path,
            TableDefinition {
                name: "test".to_string(),
                columns: vec![
                    Column::new("id", ColumnType::Integer)?,
                    Column::new("username", ColumnType::Text { size: 32 })?,
                    Column::new("email", ColumnType::Text { size: 240 })?,
                ],
            },
        )?;

        for row in rows {
            db.insert(row.into())?;
        }

        db.print(db.root_page_num, "".to_string())?;
        println!();
        db.print(1, "".to_string())?;

        let rows = db.collect()?;
        assert_eq!(rows.len(), 50);

        let row = db.search(10.into())?.unwrap();
        assert_eq!(
            row.email,
            vector_to_array(str_as_bytes("b".repeat(10).as_str()))?
        );
        assert_eq!(
            row.username,
            vector_to_array(str_as_bytes("a".repeat(10).as_str()))?
        );

        let row = db.search(100.into())?;
        assert!(row.is_none());

        let row = db.search(50.into())?;
        assert!(row.is_some());

        db.close()?;

        Ok(())
    }

    #[test]
    fn test_table_definition() -> anyhow::Result<()> {
        let tmp_dir = TempDir::new("databurst")?;
        let file_path = tmp_dir.path().join("my.db");

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

        let db: Table<u32, Row> = Table::new(&file_path, td.clone())?;
        db.close()?;

        let db2: Table<u32, Row> = Table::db_open(&file_path)?;
        assert_eq!(td, db2.table_definition);

        Ok(())
    }

    #[test]
    fn test_table_invalid_insert() -> anyhow::Result<()> {
        let tmp_dir = TempDir::new("databurst")?;
        let file_path = tmp_dir.path().join("my.db");

        File::create(&file_path)?;

        let td = TableDefinition {
            name: "test".to_string(),
            columns: vec![Column::new("column", ColumnType::Integer)?],
        };

        let mut db: Table<u32, Row> = Table::new(&file_path, td)?;

        let err = db.insert(HashMap::from([("lol".to_string(), vec![0u8, 14u8])]));

        assert_eq!(
            "lol key not found in table definition".to_string(),
            err.err().unwrap().to_string()
        );

        assert_eq!(
            "every table has to have 'id' column".to_string(),
            db.insert(HashMap::from([(
                "column".to_string(),
                vec![0u8, 14u8, 14u8, 14u8],
            )]))
            .err()
            .unwrap()
            .to_string()
        );

        db.table_definition = TableDefinition {
            name: "test".to_string(),
            columns: vec![
                Column::new("id", ColumnType::Integer)?,
                Column::new("column", ColumnType::Integer)?,
            ],
        };

        assert_eq!(
            "missing 'column' column value".to_string(),
            db.insert(HashMap::from([(
                "id".to_string(),
                vec![0u8, 14u8, 14u8, 14u8],
            )]))
            .err()
            .unwrap()
            .to_string()
        );
        Ok(())
    }

    #[test]
    fn test_insert_generic_row() -> anyhow::Result<()> {
        let tmp_dir = TempDir::new("databurst")?;
        let file_path = tmp_dir.path().join("my.db");

        File::create(&file_path)?;

        let td = TableDefinition {
            name: "test".to_string(),
            columns: vec![
                Column::new("id", ColumnType::Integer)?,
                Column::new("text", ColumnType::Text { size: 32 })?,
                Column::new("bool", ColumnType::Bool)?,
            ],
        };

        let mut db: Table<u32, Vec<u8>> = Table::new(&file_path, td)?;

        let text = "lorem ipsum";
        db.insert(HashMap::from([
            ("id".to_string(), vec![0u8, 0u8, 0u8, 1u8]),
            ("text".to_string(), text.as_bytes().to_vec()),
            ("bool".to_string(), vec![1u8]),
        ]))?;

        {
            let data = db.search(1.into())?.context("inserted data not found")?;

            let read_id = i32::from_be_bytes(data[0..4].try_into()?);
            let read_text = String::from_utf8(data[4..36].to_vec())?;
            let read_bool = data[36] == 1;

            assert_eq!(read_id, 1);
            assert_eq!(read_text.replace('\0', ""), text);
            assert!(read_bool);
        }
        {
            let data = db
                .search_with_where(WhereStmt {
                    column: "id".to_string(),
                    value: vec![0u8, 0u8, 0u8, 1u8],
                })?
                .context("inserted data not found")?;
            assert_eq!(1, data.len());

            let row = data[0].clone();
            let read_id = i32::from_be_bytes(row[0..4].try_into()?);
            let read_text = String::from_utf8(row[4..36].to_vec())?;
            let read_bool = row[36] == 1;

            assert_eq!(read_id, 1);
            assert_eq!(read_text.replace('\0', ""), text);
            assert!(read_bool);
        }

        Ok(())
    }

    #[test]
    fn test_search_with_where() -> anyhow::Result<()> {
        let mut rows = vec![];
        for i in 1..=128 {
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

        let mut db: Table<u32, Row> = Table::new(
            &file_path,
            TableDefinition {
                name: "test".to_string(),
                columns: vec![
                    Column::new("id", ColumnType::Integer)?,
                    Column::new("username", ColumnType::Text { size: 32 })?,
                    Column::new("email", ColumnType::Text { size: 240 })?,
                ],
            },
        )?;

        for (i, row) in rows.into_iter().enumerate() {
            if i == 15 {
                dbg!(i);
            }
            db.insert(row.into())?;
        }
        db.print_short(0, "".to_string())?;

        let rows = db
            .search_with_where(WhereStmt {
                column: "username".to_string(),
                value: str_as_bytes("a".repeat(4).as_str()),
            })?
            .context("rows should be found")?;
        assert_eq!(4, rows.len());

        db.close()?;

        Ok(())
    }

    #[test]
    fn test_search_with_where_many() -> anyhow::Result<()> {
        let mut rows = vec![];
        for i in 1..=400 {
            rows.push(Row {
                id: i,
                username: vector_to_array(str_as_bytes("a".repeat(i as usize % 20).as_str()))
                    .unwrap(),
                email: vector_to_array(str_as_bytes("b".repeat(i as usize % 240).as_str()))
                    .unwrap(),
            })
        }

        let tmp_dir = TempDir::new("databurst")?;
        let file_path = tmp_dir.path().join("my.db");
        File::create(&file_path)?;

        let mut db: Table<u32, Row> = Table::new(
            &file_path,
            TableDefinition {
                name: "test".to_string(),
                columns: vec![
                    Column::new("id", ColumnType::Integer)?,
                    Column::new("username", ColumnType::Text { size: 32 })?,
                    Column::new("email", ColumnType::Text { size: 240 })?,
                ],
            },
        )?;
        db.add_indexed_column("username".to_string())?;

        for (i, row) in rows.into_iter().enumerate() {
            db.insert(row.into())?;
        }

        db.print_short(1, "".to_string())?;

        let rows = db
            .search_with_where(WhereStmt {
                column: "username".to_string(),
                value: str_as_bytes("a".repeat(4).as_str()),
            })?
            .context("rows should be found")?;

        assert_eq!(20, rows.len());

        db.close()?;

        Ok(())
    }
}
