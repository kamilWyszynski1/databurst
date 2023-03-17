use crate::{
    constants::{
        IS_ROOT_OFFSET, LEAF_NODE_HEADER_SIZE, LEAF_NODE_KEY_SIZE, LEAF_NODE_NUM_CELLS_OFFSET,
        LEAF_NODE_NUM_CELLS_SIZE, NODE_TYPE_OFFSET, PAGE_SIZE, PARENT_POINTER_OFFSET,
        PARENT_POINTER_SIZE, ROWS_SIZE,
    },
    pager::Page,
};
use anyhow::{bail, Context};

pub enum NodeType {
    /// Internal nodes contain a vector of pointers to their children and a vector of keys.
    Internal(Vec<usize>, Vec<Vec<u8>>),

    Leaf(Vec<(u32, Vec<u8>)>),
}

impl TryFrom<u8> for NodeType {
    type Error = anyhow::Error;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        Ok(match value {
            0x00 => NodeType::Leaf(vec![]),
            0x01 => Self::Internal(vec![], vec![]),
            _ => bail!("invalid node type: {}", value),
        })
    }
}

impl From<&NodeType> for u8 {
    fn from(val: &NodeType) -> Self {
        match val {
            NodeType::Leaf(_) => 0x00,
            NodeType::Internal(_, _) => 0x01,
        }
    }
}

pub struct Node {
    pub node_type: NodeType,
    pub is_root: bool,
    parent: Option<u32>, // parent offset
}

impl Node {
    fn new(node_type: NodeType, is_root: bool, parent: Option<u32>) -> Self {
        Self {
            node_type,
            is_root,
            parent,
        }
    }

    pub fn leaf_node_value(&self, cell_num: usize) -> anyhow::Result<Vec<u8>> {
        match self.node_type {
            NodeType::Internal(_, _) => bail!("leaf_node_value called for Internal"),
            NodeType::Leaf(ref values) => Ok(values
                .get(cell_num)
                .context("could not get value by cell_num")?
                .clone()
                .1),
        }
    }

    pub fn leaf_node_key(&self, cell_num: usize) -> anyhow::Result<u32> {
        match self.node_type {
            NodeType::Internal(_, _) => bail!("leaf_node_key called for Internal"),
            NodeType::Leaf(ref values) => Ok(values
                .get(cell_num)
                .context("could not get value by cell_num")?
                .clone()
                .0),
        }
    }

    pub fn num_cells(&self) -> u32 {
        match &self.node_type {
            NodeType::Internal(_, _) => todo!(),
            NodeType::Leaf(values) => values.len() as u32,
        }
    }
}

impl TryFrom<Page> for Node {
    type Error = anyhow::Error;

    fn try_from(value: Page) -> Result<Self, Self::Error> {
        let data = value.data;

        let node_type =
            NodeType::try_from(data[NODE_TYPE_OFFSET]).context("could not parse NodeType")?;
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

        match node_type {
            NodeType::Internal(_, _) => todo!(),
            NodeType::Leaf(mut pairs) => {
                let mut offset = LEAF_NODE_HEADER_SIZE;

                for _ in 0..num_cells {
                    let key = pointer_from_bytes(&data, offset).context("could not parse key")?;
                    offset += LEAF_NODE_KEY_SIZE;
                    let data = value.get_ptr_from_offset(offset, ROWS_SIZE);
                    offset += ROWS_SIZE;
                    pairs.push((key, data.to_vec()));
                }

                Ok(Self::new(NodeType::Leaf(pairs), is_root, parent))
            }
        }
    }
}

impl TryFrom<Node> for [u8; PAGE_SIZE] {
    type Error = anyhow::Error;

    fn try_from(val: Node) -> anyhow::Result<Self, Self::Error> {
        let mut buf = [0u8; PAGE_SIZE];

        buf[NODE_TYPE_OFFSET] = (&val.node_type).into();
        buf[IS_ROOT_OFFSET] = val.is_root.into();
        buf[PARENT_POINTER_OFFSET..PARENT_POINTER_OFFSET + PARENT_POINTER_SIZE]
            .copy_from_slice(&val.parent.unwrap_or_default().to_be_bytes());
        let num_cells = val.num_cells();
        buf[LEAF_NODE_NUM_CELLS_OFFSET..LEAF_NODE_NUM_CELLS_OFFSET + LEAF_NODE_NUM_CELLS_SIZE]
            .copy_from_slice(&num_cells.to_be_bytes());

        match val.node_type {
            NodeType::Internal(_, _) => todo!(),
            NodeType::Leaf(kvs) => {
                let mut offset = LEAF_NODE_HEADER_SIZE;

                for (k, v) in kvs {
                    buf[offset..offset + LEAF_NODE_KEY_SIZE].copy_from_slice(&k.to_be_bytes());
                    offset += LEAF_NODE_KEY_SIZE;
                    buf[offset..offset + ROWS_SIZE].copy_from_slice(&v);
                    offset += ROWS_SIZE;
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
                    "could not convert bytes to usize, offset: {offset}, data len: {}",
                    data.len()
                )
            })?,
    );
    Ok(value)
}
