use std::{cell::RefCell, rc::Rc};

use crate::{
    constants::{
        IS_ROOT_OFFSET, LEAF_INDEX_NODE_CELL_SIZE, LEAF_NODE_HEADER_SIZE, LEAF_NODE_KEY_SIZE,
        LEAF_NODE_NUM_CELLS_OFFSET, LEAF_NODE_NUM_CELLS_SIZE, NODE_TYPE_OFFSET, PAGE_SIZE,
        PARENT_POINTER_OFFSET, PARENT_POINTER_SIZE, ROWS_SIZE,
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

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Key(pub u32);

impl From<u32> for Key {
    fn from(value: u32) -> Self {
        Self(value)
    }
}

#[derive(Debug, Clone)]
pub enum InternalNodeType {
    /// Internal nodes contain a vector of pointers to their children and a vector of keys.
    Internal {
        right_child: Pointer,
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
                right_child: Pointer(0),
                child_pointer_pairs: Vec::new(),
                is_index: true,
            },
            0x05 => Self::Internal {
                right_child: Pointer(0),
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
                right_child: _,
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
        right_child: Pointer,
        child_pointer_pairs: Vec<(Pointer, Key)>,
    },

    Leaf {
        /// Key - Value vector of serialized data. Key is Row's ID field value.
        kvs: Vec<(Key, Vec<u8>)>,

        /// Optional pointer to right next leaf. Enables robust select;
        next_leaf: Option<Pointer>,
    },
}

#[derive(Debug)]
pub struct Node {
    pub node_type: NodeType,
    pub is_root: bool,
    pub is_index: bool,
    pub parent: Option<u32>, // parent offset
}

impl From<&Node> for u8 {
    fn from(val: &Node) -> Self {
        match val.node_type {
            NodeType::Internal {
                right_child: _,
                child_pointer_pairs: _,
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
    pub fn new(node_type: NodeType, is_root: bool, is_index: bool, parent: Option<u32>) -> Self {
        Self {
            node_type,
            is_root,
            is_index,
            parent,
        }
    }

    pub fn save(self, page_num: u32, pager: Rc<RefCell<Pager>>) -> anyhow::Result<()> {
        pager.borrow_mut().get_page(page_num)?.borrow_mut().data = self.try_into()?;
        Ok(())
    }

    pub fn is_leaf_node(&self) -> bool {
        match self.node_type {
            NodeType::Internal {
                right_child: _,
                child_pointer_pairs: _,
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
                right_child: _,
                child_pointer_pairs: _,
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

    pub fn leaf_node_key(&self, cell_num: u32) -> anyhow::Result<Option<u32>> {
        match self.node_type {
            NodeType::Internal {
                right_child: _,
                child_pointer_pairs: _,
            } => Ok(None),
            NodeType::Leaf {
                ref kvs,
                next_leaf: _,
            } => Ok(Some(
                kvs.get(cell_num as usize)
                    .context("could not get value by cell_num")?
                    .clone()
                    .0
                     .0,
            )),
        }
    }

    pub fn num_cells(&self) -> u32 {
        match &self.node_type {
            NodeType::Internal {
                right_child: _,
                child_pointer_pairs,
            } => child_pointer_pairs.len() as u32,
            NodeType::Leaf { kvs, next_leaf: _ } => kvs.len() as u32,
        }
    }

    pub fn max_key(&self) -> u32 {
        match &self.node_type {
            NodeType::Internal {
                right_child: _,
                child_pointer_pairs,
            } => {
                child_pointer_pairs
                    .iter()
                    .map(|(_, key)| *key)
                    .last()
                    .unwrap_or_default()
                    .0
            }
            NodeType::Leaf { kvs, next_leaf: _ } => {
                kvs.iter().map(|(key, _)| *key).last().unwrap_or_default().0
            }
        }
    }

    pub fn internal_right_pointer(&self) -> anyhow::Result<Pointer> {
        match &self.node_type {
            NodeType::Internal {
                right_child,
                child_pointer_pairs: _,
            } => Ok(*right_child),
            NodeType::Leaf {
                kvs: _,
                next_leaf: _,
            } => {
                bail!("internal_right_pointer called on Leaf node")
            }
        }
    }

    pub fn pop(&mut self) {
        match &mut self.node_type {
            NodeType::Internal {
                right_child: _,
                child_pointer_pairs,
            } => {
                child_pointer_pairs.pop();
            }
            NodeType::Leaf { kvs, next_leaf: _ } => {
                kvs.pop();
            }
        }
    }

    fn is_internal(&self) -> bool {
        match self.node_type {
            NodeType::Internal {
                right_child: _,
                child_pointer_pairs: _,
            } => true,
            NodeType::Leaf {
                kvs: _,
                next_leaf: _,
            } => false,
        }
    }

    /// Can be run only on internal page, it checks if 'right_pointer' and max from 'child_pointer_pairs' are the same,
    /// if so, value is deleted from  'child_pointer_pairs'.
    /// Returns 'true' when there was overriding pointers.
    pub fn remove_overriding_pointers(
        &mut self,
        pager: Rc<RefCell<Pager>>,
    ) -> anyhow::Result<bool> {
        if !self.is_internal() {
            bail!("remove_overriding_pointers called on Leaf node")
        }
        let right_pointer_key = Node::try_from(
            pager
                .borrow_mut()
                .get_page(self.internal_right_pointer()?.0)?,
        )?
        .max_key();
        if self.max_key() == right_pointer_key {
            self.pop();
            return Ok(true);
        }
        Ok(false)
    }

    /// Goes through all children and sets their parent as current node/page.
    pub fn update_children_parent(
        &self,
        self_page_num: u32,
        pager: Rc<RefCell<Pager>>,
    ) -> anyhow::Result<()> {
        for Pointer(pointer) in self.children_pointers()? {
            let pointer_page = pager.borrow_mut().get_page(pointer)?;
            let mut node = Node::try_from(pointer_page.clone())?;
            node.parent = Some(self_page_num);
            pointer_page.borrow_mut().data = node.try_into()?;
        }
        Ok(())
    }

    /// Returns internal's node children. Returns error when node's a Leaf.
    pub fn children_pointers(&self) -> anyhow::Result<Vec<Pointer>> {
        match &self.node_type {
            NodeType::Internal {
                right_child,
                child_pointer_pairs,
            } => {
                let mut pointers: Vec<Pointer> =
                    child_pointer_pairs.iter().map(|(p, _)| *p).collect();
                pointers.push(*right_child);

                Ok(pointers)
            }
            NodeType::Leaf {
                kvs: _,
                next_leaf: _,
            } => bail!("children_pointers called on Leaf node"),
        }
    }
}

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
                mut right_child,
                mut child_pointer_pairs,
                is_index,
            } => {
                right_child = Pointer(
                    pointer_from_bytes(&data, offset).context("could not right_child pointer")?,
                );
                offset += LEAF_NODE_KEY_SIZE;

                for _ in 0..num_cells {
                    let pointer = Pointer(
                        pointer_from_bytes(&data, offset)
                            .context("could not parse child pointer")?,
                    );
                    offset += LEAF_NODE_KEY_SIZE;
                    let key = pointer_from_bytes(&data, offset).context("could not parse key")?;
                    offset += LEAF_NODE_KEY_SIZE;

                    child_pointer_pairs.push((pointer, Key(key)));
                }

                Ok(Self::new(
                    NodeType::Internal {
                        right_child,
                        child_pointer_pairs,
                    },
                    is_root,
                    is_index,
                    parent,
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

                offset += LEAF_NODE_KEY_SIZE;

                let row_size = if is_index {
                    LEAF_INDEX_NODE_CELL_SIZE
                } else {
                    ROWS_SIZE
                };
                for _ in 0..num_cells {
                    let key = pointer_from_bytes(&data, offset).context("could not parse key")?;
                    offset += LEAF_NODE_KEY_SIZE;
                    let data = value.get_ptr_from_offset(offset, row_size);
                    offset += row_size;
                    kvs.push((Key(key), data.to_vec()));
                }

                Ok(Self::new(
                    NodeType::Leaf { kvs, next_leaf },
                    is_root,
                    is_index,
                    parent,
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
            NodeType::Internal {
                right_child,
                child_pointer_pairs,
            } => {
                buf[offset..offset + LEAF_NODE_KEY_SIZE]
                    .copy_from_slice(&right_child.0.to_be_bytes());
                offset += LEAF_NODE_KEY_SIZE;

                for (pointer, key) in child_pointer_pairs {
                    buf[offset..offset + LEAF_NODE_KEY_SIZE]
                        .copy_from_slice(&pointer.0.to_be_bytes());
                    offset += LEAF_NODE_KEY_SIZE;
                    buf[offset..offset + LEAF_NODE_KEY_SIZE].copy_from_slice(&key.0.to_be_bytes());
                    offset += LEAF_NODE_KEY_SIZE;
                }
            }
            NodeType::Leaf { kvs, next_leaf } => {
                buf[offset..offset + LEAF_NODE_KEY_SIZE]
                    .copy_from_slice(&next_leaf.unwrap_or_default().0.to_be_bytes());
                offset += LEAF_NODE_KEY_SIZE;

                let row_size = if val.is_index {
                    LEAF_INDEX_NODE_CELL_SIZE
                } else {
                    ROWS_SIZE
                };

                for (Key(key), v) in kvs {
                    buf[offset..offset + LEAF_NODE_KEY_SIZE].copy_from_slice(&key.to_be_bytes());
                    offset += LEAF_NODE_KEY_SIZE;
                    buf[offset..offset + row_size].copy_from_slice(&v);
                    offset += row_size;
                }
            }
        }

        Ok(buf)
    }
}

fn pointer_from_bytes(data: &[u8], offset: usize) -> anyhow::Result<u32> {
    let value = u32::from_be_bytes(
        data[offset..offset + LEAF_NODE_KEY_SIZE]
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
