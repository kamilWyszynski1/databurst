use crate::table::{EMAIL_SIZE, ID_SIZE, USERNAME_SIZE};

pub const ID_OFFSET: usize = 0;
pub const USERNAME_OFFSET: usize = ID_OFFSET + ID_SIZE;
pub const EMAIL_OFFSET: usize = USERNAME_OFFSET + USERNAME_SIZE;
// pub const ROWS_SIZE: usize = ID_SIZE + USERNAME_SIZE + EMAIL_SIZE;

pub const TABLE_MAX_PAGES: usize = 100;
pub const PAGE_SIZE: usize = 4096; // 4KB

// Common node header layout
pub const NODE_TYPE_SIZE: usize = 1;
pub const NODE_TYPE_OFFSET: usize = 0;
pub const IS_ROOT_SIZE: usize = 1;
pub const IS_ROOT_OFFSET: usize = NODE_TYPE_SIZE;
pub const PARENT_POINTER_SIZE: usize = 4;
pub const PARENT_POINTER_OFFSET: usize = IS_ROOT_OFFSET + IS_ROOT_SIZE;
pub const COMMON_NODE_HEADER_SIZE: usize = NODE_TYPE_SIZE + IS_ROOT_SIZE + PARENT_POINTER_SIZE;

// Leaf node header layout
pub const LEAF_NODE_NUM_CELLS_SIZE: usize = 4;
pub const LEAF_NODE_NUM_CELLS_OFFSET: usize = COMMON_NODE_HEADER_SIZE;
pub const LEAF_NODE_HEADER_SIZE: usize = COMMON_NODE_HEADER_SIZE + LEAF_NODE_NUM_CELLS_SIZE;

// Leaf node body layout
pub const LEAF_NODE_KEY_SIZE: usize = 4;
// pub const LEAF_NODE_VALUE_SIZE: usize = ROWS_SIZE;
// pub const LEAF_NODE_CELL_SIZE: usize = LEAF_NODE_KEY_SIZE + LEAF_NODE_VALUE_SIZE;
pub const LEAF_NODE_SPACE_FOR_CELLS: usize = PAGE_SIZE - LEAF_NODE_HEADER_SIZE;
// pub const LEAF_NODE_MAX_CELLS: usize = LEAF_NODE_SPACE_FOR_CELLS / LEAF_NODE_CELL_SIZE;

// Leaf node body layout
pub const LEAF_INDEX_NODE_KEY_SIZE: usize = 4;
pub const LEAF_INDEX_NODE_VALUE_SIZE: usize = 4;
pub const LEAF_INDEX_NODE_CELL_SIZE: usize = LEAF_INDEX_NODE_KEY_SIZE + LEAF_INDEX_NODE_VALUE_SIZE;
pub const LEAF_INDEX_NODE_SPACE_FOR_CELLS: usize = PAGE_SIZE - LEAF_NODE_HEADER_SIZE;
pub const LEAF_INDEX_NODE_MAX_CELLS: usize =
    LEAF_INDEX_NODE_SPACE_FOR_CELLS / LEAF_INDEX_NODE_CELL_SIZE;
