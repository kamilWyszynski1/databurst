use std::{any, cell::RefCell, rc::Rc};

use crate::{
    constants::{
        IS_ROOT_OFFSET, LEAF_INDEX_NODE_CELL_SIZE, LEAF_NODE_HEADER_SIZE,
        LEAF_NODE_NUM_CELLS_OFFSET, LEAF_NODE_NUM_CELLS_SIZE, NODE_TYPE_OFFSET, PAGE_SIZE,
        PARENT_POINTER_OFFSET, PARENT_POINTER_SIZE,
    },
    pager::{Page, Pager},
};
use anyhow::{bail, Context, Ok};

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Pointer(pub u32);

impl From<u32> for Pointer {
    fn from(value: u32) -> Self {
        Self(value)
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Key(pub Vec<u8>);

impl From<u32> for Key {
    fn from(value: u32) -> Self {
        Self(value.to_be_bytes().to_vec())
    }
}

impl From<Vec<u8>> for Key {
    fn from(value: Vec<u8>) -> Self {
        Self(value)
    }
}

impl From<&str> for Key {
    fn from(value: &str) -> Self {
        Self(value.as_bytes().to_vec())
    }
}

#[derive(Debug, Clone)]
pub enum InternalNodeType {
    /// Internal nodes contain a vector of pointers to their children and a vector of keys.
    Internal {
        child_pointer_pairs: Vec<(Pointer, Key)>,
        is_index: bool,
    },

    Leaf {
        /// Key - Value vector of serialized data. Key is Row's ID field value.
        kvs: Vec<(Key, Vec<u8>)>,

        /// Optional pointer to right next leaf. Enables robust select;
        next_leaf: Option<Pointer>,

        is_index: bool,
    },
}

/// The one-byte flag at offset 0 indicating the b-tree page type.
///     * A value of 2 (0x02) means the page is an interior index b-tree page.
///     * A value of 5 (0x05) means the page is an interior table b-tree page.
///     * A value of 10 (0x0a) means the page is a leaf index b-tree page.
///     * A value of 13 (0x0d) means the page is a leaf table b-tree page.
impl TryFrom<u8> for InternalNodeType {
    type Error = anyhow::Error;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        Ok(match value {
            0x02 => Self::Internal {
                child_pointer_pairs: Vec::new(),
                is_index: true,
            },
            0x05 => Self::Internal {
                child_pointer_pairs: Vec::new(),
                is_index: true,
            },
            0x0a => Self::Leaf {
                kvs: vec![],
                next_leaf: None,
                is_index: true,
            },
            0x0d => Self::Leaf {
                kvs: vec![],
                next_leaf: None,
                is_index: false,
            },
            _ => bail!("invalid node type: {}", value),
        })
    }
}

impl From<&InternalNodeType> for u8 {
    fn from(val: &InternalNodeType) -> Self {
        match val {
            InternalNodeType::Internal {
                child_pointer_pairs: _,
                is_index,
            } => {
                if *is_index {
                    0x02
                } else {
                    0x05
                }
            }
            InternalNodeType::Leaf {
                kvs: _,
                next_leaf: _,
                is_index,
            } => {
                if *is_index {
                    0x0a
                } else {
                    0x0d
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum NodeType {
    /// Internal nodes contain a vector of pointers to their children and a vector of keys.
    Internal {
        children: Vec<Pointer>,
        keys: Vec<Key>,
    },

    Leaf {
        /// Key - Value vector of serialized data. Key is Row's ID field value.
        kvs: Vec<(Key, Vec<u8>)>,

        /// Optional pointer to right next leaf. Enables robust select;
        next_leaf: Option<Pointer>,
    },
}

#[derive(Debug, Clone)]
pub struct Node {
    pub node_type: NodeType,
    pub is_root: bool,
    pub is_index: bool,
    pub parent: Option<u32>, // parent offset

    /// Amount of bytes that row's key takes. It is dynamical because indexes' keys can be arbitrary values like strings.
    pub key_size: usize,
    /// Amount of bytes that row "body" takes.
    pub row_size: usize,
}

impl From<&Node> for u8 {
    fn from(val: &Node) -> Self {
        match val.node_type {
            NodeType::Internal {
                keys: _,
                children: _,
            } => {
                if val.is_index {
                    0x02
                } else {
                    0x05
                }
            }
            NodeType::Leaf {
                kvs: _,
                next_leaf: _,
            } => {
                if val.is_index {
                    0x0a
                } else {
                    0x0d
                }
            }
        }
    }
}

impl Node {
    pub fn new(
        node_type: NodeType,
        is_root: bool,
        is_index: bool,
        parent: Option<u32>,
        key_size: usize,
        row_size: usize,
    ) -> Self {
        Self {
            node_type,
            is_root,
            is_index,
            parent,
            key_size,
            row_size,
        }
    }

    pub fn save(
        self,
        page_num: u32,
        pager: Rc<RefCell<Pager>>,
        key_size: usize,
        row_size: usize,
    ) -> anyhow::Result<()> {
        pager
            .borrow_mut()
            .get_page(page_num, key_size, row_size)?
            .borrow_mut()
            .data = self.try_into()?;
        Ok(())
    }

    pub fn is_leaf_node(&self) -> bool {
        match self.node_type {
            NodeType::Internal {
                children: _,
                keys: _,
            } => false,
            NodeType::Leaf {
                kvs: _,
                next_leaf: _,
            } => true,
        }
    }

    pub fn leaf_node_value(&self, cell_num: u32) -> anyhow::Result<Option<Vec<u8>>> {
        match self.node_type {
            NodeType::Internal {
                children: _,
                keys: _,
            } => Ok(None),
            NodeType::Leaf {
                ref kvs,
                next_leaf: _,
            } => Ok(Some(
                kvs.get(cell_num as usize)
                    .context("could not get value by cell_num")?
                    .clone()
                    .1,
            )),
        }
    }

    pub fn leaf_node_key(&self, cell_num: u32) -> anyhow::Result<Option<Key>> {
        match self.node_type {
            NodeType::Internal {
                children: _,
                keys: _,
            } => Ok(None),
            NodeType::Leaf {
                ref kvs,
                next_leaf: _,
            } => Ok(Some(
                kvs.get(cell_num as usize)
                    .context("could not get value by cell_num")?
                    .clone()
                    .0,
            )),
        }
    }

    pub fn num_cells(&self) -> u32 {
        match &self.node_type {
            NodeType::Internal { children, keys: _ } => children.len() as u32,
            NodeType::Leaf { kvs, next_leaf: _ } => kvs.len() as u32,
        }
    }

    pub fn max_key(&self) -> Key {
        match &self.node_type {
            NodeType::Internal { children: _, keys } => keys
                .iter()
                .map(|key| key.clone())
                .last()
                .unwrap_or_default(),
            NodeType::Leaf { kvs, next_leaf: _ } => kvs
                .iter()
                .map(|(key, _)| key.clone())
                .last()
                .unwrap_or_default(),
        }
    }

    pub fn pop(&mut self) {
        match &mut self.node_type {
            NodeType::Internal { children, keys } => {
                keys.pop();
                children.pop();
            }
            NodeType::Leaf { kvs, next_leaf: _ } => {
                kvs.pop();
            }
        }
    }

    fn is_internal(&self) -> bool {
        match self.node_type {
            NodeType::Internal {
                children: _,
                keys: _,
            } => true,
            NodeType::Leaf {
                kvs: _,
                next_leaf: _,
            } => false,
        }
    }

    /// Goes through all children and sets their parent as current node/page.
    pub fn update_children_parent(
        &self,
        self_page_num: u32,
        pager: Rc<RefCell<Pager>>,
        key_size: usize,
        row_size: usize,
    ) -> anyhow::Result<()> {
        for Pointer(pointer) in self.children_pointers()? {
            let pointer_page = pager.borrow_mut().get_page(pointer, key_size, row_size)?;
            let mut node = Node::try_from(pointer_page.clone())?;
            node.parent = Some(self_page_num);
            pointer_page.borrow_mut().data = node.try_into()?;
        }
        Ok(())
    }

    /// Returns internal's node children. Returns error when node's a Leaf.
    pub fn children_pointers(&self) -> anyhow::Result<Vec<Pointer>> {
        match &self.node_type {
            NodeType::Internal { children, keys: _ } => {
                let pointers: Vec<Pointer> = children.to_vec();

                Ok(pointers)
            }
            NodeType::Leaf {
                kvs: _,
                next_leaf: _,
            } => bail!("children_pointers called on Leaf node"),
        }
    }

    pub fn contains(&self, wanted: &Key) -> bool {
        match &self.node_type {
            NodeType::Internal { children: _, keys } => keys.contains(wanted),
            NodeType::Leaf { kvs, next_leaf: _ } => {
                for (key, _) in kvs {
                    if key == wanted {
                        return true;
                    }
                }
                false
            }
        }
    }

    /// split creates a sibling node from a given node by splitting the node in two around a median.
    /// split will split the child at b leaving the [0, b-1] keys
    /// while moving the set of [b, 2b-1] keys to the sibling.
    pub fn split(&mut self, b: usize, sibling_page_num: u32) -> anyhow::Result<(Key, Self)> {
        match self.node_type {
            NodeType::Internal {
                ref mut children,
                ref mut keys,
            } => {
                // Populate siblings keys.
                let mut sibling_keys = keys.split_off(b - 1);
                // Pop median key - to be added to the parent..
                let median_key = sibling_keys.remove(0);
                // Populate siblings children.
                let sibling_children = children.split_off(b);
                Ok((
                    median_key,
                    Node::new(
                        NodeType::Internal {
                            children: sibling_children,
                            keys: sibling_keys,
                        },
                        false,
                        self.is_index,
                        self.parent.clone(),
                        self.key_size,
                        self.row_size,
                    ),
                ))
            }
            NodeType::Leaf {
                ref mut kvs,
                ref mut next_leaf,
            } => {
                // Populate siblings pairs.
                let sibling_kvs = kvs.split_off(b);
                // Pop median key.
                let median_pair = kvs.get(b - 1).context("could not get median_pair")?.clone();

                let sibling_node_type = NodeType::Leaf {
                    kvs: sibling_kvs,
                    next_leaf: next_leaf.clone(),
                };
                *next_leaf = Some(Pointer(sibling_page_num)); // we should point to newly created leaf
                Ok((
                    median_pair.0,
                    Node::new(
                        sibling_node_type,
                        false,
                        self.is_index,
                        self.parent.clone(),
                        self.key_size,
                        self.row_size,
                    ),
                ))
            }
        }
    }
}

const POINTER_SIZE: usize = 4;

impl TryFrom<Page> for Node {
    type Error = anyhow::Error;

    fn try_from(value: Page) -> anyhow::Result<Self, Self::Error> {
        let data = value.data;

        let node_type = InternalNodeType::try_from(data[NODE_TYPE_OFFSET])
            .context("could not parse NodeType")?;
        let is_root: bool = data[IS_ROOT_OFFSET] == 1;
        let parent: Option<u32> = if is_root {
            None
        } else {
            Some(
                pointer_from_bytes(&data, PARENT_POINTER_OFFSET)
                    .context("could not parse parent pointer")?,
            )
        };
        let num_cells = pointer_from_bytes(&data, LEAF_NODE_NUM_CELLS_OFFSET)
            .context("could not parse num_cells")?;

        let mut offset = LEAF_NODE_HEADER_SIZE;
        match node_type {
            InternalNodeType::Internal {
                child_pointer_pairs: _,
                is_index,
            } => {
                let mut children = vec![];
                let mut keys = vec![];
                for _ in 0..num_cells {
                    let pointer = Pointer(
                        pointer_from_bytes(&data, offset)
                            .context("could not parse child pointer")?,
                    );
                    offset += POINTER_SIZE;
                    children.push(pointer);
                }

                for _ in 0..num_cells - 1 {
                    let key = Key(data[offset..offset + value.key_size].to_vec());
                    offset += value.key_size;
                    keys.push(key);
                }

                Ok(Self::new(
                    NodeType::Internal { children, keys },
                    is_root,
                    is_index,
                    parent,
                    value.key_size,
                    value.row_size,
                ))
            }
            InternalNodeType::Leaf {
                mut kvs,
                mut next_leaf,
                is_index,
            } => {
                next_leaf =
                    match pointer_from_bytes(&data, offset).context("could not parse next_leaf")? {
                        0 => None,
                        value => Some(Pointer(value)),
                    };

                offset += POINTER_SIZE;

                let row_size = if is_index {
                    LEAF_INDEX_NODE_CELL_SIZE
                } else {
                    value.row_size
                };
                for _ in 0..num_cells {
                    let key = data[offset..offset + value.key_size].to_vec();
                    offset += value.key_size;
                    let data = value.get_ptr_from_offset(offset, row_size);
                    offset += row_size;
                    kvs.push((Key(key), data.to_vec()));
                }

                Ok(Self::new(
                    NodeType::Leaf { kvs, next_leaf },
                    is_root,
                    is_index,
                    parent,
                    value.key_size,
                    value.row_size,
                ))
            }
        }
    }
}

impl TryFrom<Rc<RefCell<Page>>> for Node {
    type Error = anyhow::Error;

    fn try_from(value: Rc<RefCell<Page>>) -> anyhow::Result<Self, Self::Error> {
        Node::try_from(value.borrow().clone())
    }
}

impl TryFrom<Node> for [u8; PAGE_SIZE] {
    type Error = anyhow::Error;

    fn try_from(val: Node) -> anyhow::Result<Self, Self::Error> {
        let mut buf = [0u8; PAGE_SIZE];

        buf[NODE_TYPE_OFFSET] = (&val).into();
        buf[IS_ROOT_OFFSET] = val.is_root.into();
        buf[PARENT_POINTER_OFFSET..PARENT_POINTER_OFFSET + PARENT_POINTER_SIZE]
            .copy_from_slice(&val.parent.unwrap_or_default().to_be_bytes());
        let num_cells = val.num_cells();
        buf[LEAF_NODE_NUM_CELLS_OFFSET..LEAF_NODE_NUM_CELLS_OFFSET + LEAF_NODE_NUM_CELLS_SIZE]
            .copy_from_slice(&num_cells.to_be_bytes());

        let mut offset = LEAF_NODE_HEADER_SIZE;

        match val.node_type {
            NodeType::Internal { children, keys } => {
                for Pointer(child) in children {
                    buf[offset..offset + POINTER_SIZE].copy_from_slice(&child.to_be_bytes());
                    offset += POINTER_SIZE;
                }
                for Key(key) in keys {
                    buf[offset..offset + val.key_size].copy_from_slice(&key);
                    offset += val.key_size;
                }
            }
            NodeType::Leaf { kvs, next_leaf } => {
                buf[offset..offset + POINTER_SIZE]
                    .copy_from_slice(&next_leaf.unwrap_or_default().0.to_be_bytes());
                offset += POINTER_SIZE;

                let row_size = if val.is_index {
                    LEAF_INDEX_NODE_CELL_SIZE
                } else {
                    val.row_size
                };

                // dbg!(&kvs.len());
                for (Key(key), v) in kvs {
                    copy_from_slice(&mut buf[offset..offset + val.key_size], &key)?;
                    // buf[offset..offset + val.key_size].copy_from_slice(&key);
                    offset += val.key_size;
                    copy_from_slice(&mut buf[offset..offset + val.row_size], &v)?;
                    // buf[offset..offset + row_size].copy_from_slice(&v);
                    offset += row_size;
                }
            }
        }

        Ok(buf)
    }
}

fn copy_from_slice(buffer: &mut [u8], v: &Vec<u8>) -> anyhow::Result<()> {
    if buffer.len() != v.len() {
        bail!(
            "buffer {} and vector {}{:?} len does not match",
            buffer.len(),
            v.len(),
            String::from_utf8(v.to_vec())?
        );
    }
    buffer.copy_from_slice(v);
    Ok(())
}

fn pointer_from_bytes(data: &[u8], offset: usize) -> anyhow::Result<u32> {
    let value = u32::from_be_bytes(
        data[offset..offset + POINTER_SIZE]
            .try_into()
            .with_context(|| {
                format!(
                    "could not convert bytes to u32, offset: {offset}, data len: {}",
                    data.len()
                )
            })?,
    );
    Ok(value)
}
