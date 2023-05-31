use std::{cell::RefCell, rc::Rc};

use anyhow::{bail, Context, Ok};

use crate::{
    constants::LEAF_NODE_SPACE_FOR_CELLS,
    node::{Key, Node, NodeType, Pointer},
    pager::Pager,
};

pub struct SplitMetadata {
    pub new_left: u32,
    pub new_right: u32,
}

/// Metadata about various, database operations.
pub enum OperationInfo {
    Insert {
        split_occurred: bool,
        metadata: Option<SplitMetadata>,
    },
    Replace,
}

#[derive(Clone)]
pub struct Cursor {
    pager: Rc<RefCell<Pager>>,
    pub page_num: u32,
    pub cell_num: u32,
}

impl std::fmt::Debug for Cursor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Cursor")
            .field("page_num", &self.page_num)
            .field("cell_num", &self.cell_num)
            .finish()
    }
}

impl Cursor {
    pub fn new(pager: Rc<RefCell<Pager>>, page_num: u32, cell_num: u32) -> Self {
        Self {
            pager,
            cell_num,
            page_num,
        }
    }

    pub fn insert(&self, key: Key, data: &[u8]) -> anyhow::Result<OperationInfo> {
        let page = self
            .pager
            .try_borrow_mut()?
            .get_page(self.page_num, key.0.len(), data.len())?;

        // turn page's bytes into readable node
        let mut node = Node::try_from(page.borrow().clone())?;

        let leaf_node_max_cells = {
            let leaf_node_cells_size = key.0.len() + data.len();
            LEAF_NODE_SPACE_FOR_CELLS / leaf_node_cells_size
        };

        // // check if cell_num is already occupied, if key matches, replace value
        // if let NodeType::Leaf { kvs, next_leaf: _ } = &mut node.node_type {
        //     if let Some((existing_key, existing_data)) = kvs.get_mut(self.cell_num as usize) {
        //         if *existing_key == key {
        //             // replace and return
        //             *existing_data = data.to_vec();
        //             // turn node back into bytes
        //             page.borrow_mut().data = node.try_into()?;
        //             return Ok(OperationInfo::Replace);
        //         }
        //     }
        // }

        let num_cells = node.num_cells() as usize;

        // check if split is needed
        let index_need_split = node.is_index && num_cells >= leaf_node_max_cells;
        let non_index_need_split = !node.is_index && num_cells >= leaf_node_max_cells;
        if index_need_split || non_index_need_split {
            let metadata = self.leaf_node_split_and_insert(key, data)?;
            return Ok(OperationInfo::Insert {
                split_occurred: true,
                metadata: Some(metadata),
            });
        }

        // insert value
        match &mut node.node_type {
            NodeType::Internal {
                child_pointer_pairs: _,
            } => bail!("could not insert into Internal Node"),
            NodeType::Leaf { kvs, next_leaf: _ } => {
                // cell_num was set by binary search, it will be inserted in order
                kvs.insert(self.cell_num as usize, (key, data.to_vec()));
            }
        }

        // turn node back into bytes
        page.borrow_mut().data = node.try_into()?;

        Ok(OperationInfo::Insert {
            split_occurred: false,
            metadata: None,
        })
    }

    /// Create a new node and move half the cells over.
    /// Insert the new value in one of the two nodes.
    /// Update parent or create a new parent.
    pub fn leaf_node_split_and_insert(
        &self,
        key: Key,
        data: &[u8],
    ) -> anyhow::Result<SplitMetadata> {
        let mut left_page_num = self.page_num;

        let left_page = self
            .pager
            .borrow_mut()
            .get_page(left_page_num, key.0.len(), data.len())?;
        let left_node = Node::try_from(left_page.clone())?;

        let key_size = left_node.key_size;
        let row_size = left_node.row_size;

        let right_page_num = self.pager.borrow().get_unused_page_num();
        self.pager
            .borrow_mut()
            .get_page(right_page_num, key_size, row_size)?; // allocate page

        let is_root = left_node.is_root;
        let is_index = left_node.is_index;

        {
            // All existing keys plus new key should be divided evenly between old (left) and new (right) nodes.
            if let NodeType::Leaf { mut kvs, next_leaf } = left_node.node_type {
                kvs.insert(self.cell_num as usize, (key, data.to_vec()));

                let split_inx = find_index_to_split_by_key(&kvs)?;
                let siblings_kvs = kvs.split_off(split_inx);

                let mut left_node = Node::new(
                    NodeType::Leaf {
                        kvs,
                        next_leaf: Some(Pointer(right_page_num)),
                    },
                    false,
                    is_index,
                    left_node.parent,
                    key_size,
                    row_size,
                );
                let left_node_max_key = left_node.max_key();
                let mut right_node = Node::new(
                    NodeType::Leaf {
                        kvs: siblings_kvs,
                        next_leaf,
                    },
                    false,
                    is_index,
                    left_node.parent,
                    key_size,
                    row_size,
                );

                let max_key = right_node.max_key();
                if is_root {
                    // root page has to stay as it was, because of that we need to allocate another page
                    // copy content and change that page data
                    let new_left_page_num = self.pager.borrow().get_unused_page_num();
                    let new_left_page =
                        self.pager
                            .borrow_mut()
                            .get_page(new_left_page_num, key_size, row_size)?;
                    new_left_page.borrow_mut().data = left_node.clone().try_into()?; // clone data

                    // split the root
                    let root = Node::new(
                        NodeType::Internal {
                            child_pointer_pairs: vec![
                                (Pointer(new_left_page_num), left_node_max_key),
                                (Pointer(right_page_num), right_node.max_key()),
                            ],
                        },
                        true,
                        is_index,
                        None,
                        key_size,
                        row_size,
                    );
                    left_page.borrow_mut().data = root.try_into()?; // rewrite root

                    left_node.parent = Some(left_page_num);
                    right_node.parent = Some(left_page_num);

                    left_node.save(new_left_page_num, self.pager.clone(), key_size, row_size)?;
                    right_node.save(right_page_num, self.pager.clone(), key_size, row_size)?;

                    left_page_num = new_left_page_num; // change for SplitMetadata
                } else {
                    // update leaf's parent
                    let page_num = left_node.parent.context("no parent")?;

                    left_node.save(left_page_num, self.pager.clone(), key_size, row_size)?;
                    right_node.save(right_page_num, self.pager.clone(), key_size, row_size)?;

                    dbg!(right_page_num, &max_key, left_page_num, &left_node_max_key);
                    self.insert_into_internal(
                        page_num,
                        right_page_num,
                        max_key,
                        Some((left_page_num, left_node_max_key)),
                        data.len(),
                    )?;
                }
            } else {
                panic!("node is not a Leaf")
            }
        }

        Ok(SplitMetadata {
            new_left: left_page_num,
            new_right: right_page_num,
        })
    }

    /// Takes key and ownership of some previously allocated stuff and inserts it into internal key.
    /// We need to handle situations when:
    ///  there's only insert, without splitting
    ///  there's insert with split, we need to update further parent
    ///  there's insert, split and parent node can be split as well and so on.
    fn insert_into_internal(
        &self,
        page_num: u32,
        right_child_num: u32,
        key: Key,
        child_to_update: Option<(u32, Key)>,
        row_size: usize,
    ) -> anyhow::Result<()> {
        let key_size = key.0.len();

        let page = self
            .pager
            .borrow_mut()
            .get_page(page_num, key_size, row_size)?;
        let node = Node::try_from(page.clone())?;
        let is_index = node.is_index;

        let leaf_node_max_cells = {
            let leaf_node_cells_size = key.0.len() + row_size;
            LEAF_NODE_SPACE_FOR_CELLS / leaf_node_cells_size
        };

        match node.node_type {
            NodeType::Internal {
                mut child_pointer_pairs,
            } => {
                let pointers_len = child_pointer_pairs.len();

                if let Some((old_page_num, new_key)) = child_to_update {
                    if let Some(old) = child_pointer_pairs
                        .iter_mut()
                        .find(|(Pointer(p), _)| &old_page_num == p)
                    {
                        *old = (Pointer(old_page_num), new_key);
                    }
                }

                let index_max_cells = is_index && pointers_len == leaf_node_max_cells;
                let non_index_max_cells = !is_index && pointers_len == leaf_node_max_cells;
                if index_max_cells || non_index_max_cells {
                    // find place to insert key

                    // TODO: shift pointers here if we insert in the front or middle, take a look here
                    // it should be : ([(10, "aaaa"), (17, "aaaaaaaa"), (9, "aaaaaaaaaaaaaa")], key Pointer(15))
                    /*
                    83(2) internal [root: true, inx: true, parent: ] ([(17, "aaaa"), (10, "aaaaaaaa"), (9, "aaaaaaaaaaaaaa")], key Pointer(15))
                        (17) leaf: [parent: 2, inx: true](kvs: ["\"aaaa\" -> (16, 13)", "\"aaaa\" -> (6, 2)", "\"aaaa\" -> (11, 1)", "\"aaaa\" -> (6, 2)", "\"aaaa\" -> (5, 9)", "\"aaaa\" -> (4, 3)", "\"aaaa\" -> (0, 3)", "\"aaaaa\" -> (5, 10)", "\"aaaaa\" -> (6, 3)", "\"aaaaa\" -> (11, 2)", "\"aaaaa\" -> (13, 8)", "\"aaaaa\" -> (14, 1)", "\"aaaaa\" -> (8, 9)", "\"aaaaa\" -> (14, 1)", "\"aaaaa\" -> (11, 2)", "\"aaaaa\" -> (6, 3)", "\"aaaaa\" -> (4, 4)", "\"aaaaa\" -> (0, 4)", "\"aaaaaa\" -> (4, 5)", "\"aaaaaa\" -> (6, 4)", "\"aaaaaa\" -> (6, 4)", "\"aaaaaa\" -> (8, 10)", "\"aaaaaa\" -> (11, 3)", "\"aaaaaa\" -> (13, 9)", "\"aaaaaa\" -> (14, 2)", "\"aaaaaa\" -> (14, 2)", "\"aaaaaa\" -> (11, 3)", "\"aaaaaa\" -> (5, 11)", "\"aaaaaa\" -> (0, 5)", "\"aaaaaaa\" -> (4, 6)", "\"aaaaaaa\" -> (5, 12)", "\"aaaaaaa\" -> (8, 11)", "\"aaaaaaa\" -> (11, 4)", "\"aaaaaaa\" -> (6, 5)", "\"aaaaaaa\" -> (6, 5)", "\"aaaaaaa\" -> (11, 4)", "\"aaaaaaa\" -> (13, 10)", "\"aaaaaaa\" -> (14, 3)", "\"aaaaaaa\" -> (14, 3)", "\"aaaaaaa\" -> (0, 6)", "\"aaaaaaaa\" -> (11, 5)", "\"aaaaaaaa\" -> (5, 13)", "\"aaaaaaaa\" -> (3, 0)", "\"aaaaaaaa\" -> (6, 6)", "\"aaaaaaaa\" -> (13, 11)", "\"aaaaaaaa\" -> (14, 4)", "\"aaaaaaaa\" -> (14, 4)", "\"aaaaaaaa\" -> (11, 5)", "\"aaaaaaaa\" -> (8, 12)", "\"aaaaaaaa\" -> (6, 6)", "\"aaaaaaaa\" -> (3, 0)", "\"aaaaaaaa\" -> (0, 7)"] next_leaf: Some(Pointer(9)))
                        (10) leaf: [parent: 2, inx: true](kvs: ["\"\" -> (5, 5)", "\"\" -> (5, 5)", "\"\" -> (8, 4)", "\"\" -> (8, 4)", "\"\" -> (13, 3)", "\"\" -> (13, 3)", "\"\" -> (16, 9)", "\"\" -> (12, 10)", "\"\" -> (7, 11)", "\"\" -> (3, 12)", "\"a\" -> (5, 6)", "\"a\" -> (13, 4)", "\"a\" -> (16, 10)", "\"a\" -> (13, 4)", "\"a\" -> (8, 5)", "\"a\" -> (12, 11)", "\"a\" -> (8, 5)", "\"a\" -> (4, 0)", "\"a\" -> (7, 12)", "\"a\" -> (5, 6)", "\"a\" -> (3, 13)", "\"a\" -> (0, 0)", "\"aa\" -> (8, 6)", "\"aa\" -> (13, 5)", "\"aa\" -> (13, 5)", "\"aa\" -> (16, 11)", "\"aa\" -> (8, 6)", "\"aa\" -> (12, 12)", "\"aa\" -> (5, 7)", "\"aa\" -> (6, 0)", "\"aa\" -> (7, 13)", "\"aa\" -> (6, 0)", "\"aa\" -> (4, 1)", "\"aa\" -> (0, 1)", "\"aaa\" -> (11, 0)", "\"aaa\" -> (13, 6)", "\"aaa\" -> (13, 6)", "\"aaa\" -> (8, 7)", "\"aaa\" -> (16, 12)", "\"aaa\" -> (11, 0)", "\"aaa\" -> (12, 13)", "\"aaa\" -> (6, 1)", "\"aaa\" -> (6, 1)", "\"aaa\" -> (5, 8)", "\"aaa\" -> (4, 2)", "\"aaa\" -> (0, 2)", "\"aaaa\" -> (8, 8)", "\"aaaa\" -> (13, 7)", "\"aaaa\" -> (14, 0)", "\"aaaa\" -> (11, 1)", "\"aaaa\" -> (14, 0)"] next_leaf: Some(Pointer(17)))
                        (9) leaf: [parent: 2, inx: true](kvs: ["\"aaaaaaaaa\" -> (3, 1)", "\"aaaaaaaaa\" -> (7, 0)", "\"aaaaaaaaa\" -> (7, 0)", "\"aaaaaaaaa\" -> (8, 13)", "\"aaaaaaaaa\" -> (11, 6)", "\"aaaaaaaaa\" -> (11, 6)", "\"aaaaaaaaa\" -> (14, 5)", "\"aaaaaaaaa\" -> (14, 5)", "\"aaaaaaaaa\" -> (13, 12)", "\"aaaaaaaaa\" -> (6, 7)", "\"aaaaaaaaa\" -> (3, 1)", "\"aaaaaaaaa\" -> (0, 8)", "\"aaaaaaaaaa\" -> (12, 0)", "\"aaaaaaaaaa\" -> (14, 6)", "\"aaaaaaaaaa\" -> (14, 6)", "\"aaaaaaaaaa\" -> (12, 0)", "\"aaaaaaaaaa\" -> (13, 13)", "\"aaaaaaaaaa\" -> (11, 7)", "\"aaaaaaaaaa\" -> (3, 2)", "\"aaaaaaaaaa\" -> (6, 8)", "\"aaaaaaaaaa\" -> (7, 1)", "\"aaaaaaaaaa\" -> (7, 1)", "\"aaaaaaaaaa\" -> (3, 2)", "\"aaaaaaaaaa\" -> (0, 9)", "\"aaaaaaaaaaa\" -> (7, 2)", "\"aaaaaaaaaaa\" -> (6, 9)", "\"aaaaaaaaaaa\" -> (12, 1)", "\"aaaaaaaaaaa\" -> (14, 7)", "\"aaaaaaaaaaa\" -> (16, 0)", "\"aaaaaaaaaaa\" -> (12, 1)", "\"aaaaaaaaaaa\" -> (11, 8)", "\"aaaaaaaaaaa\" -> (3, 3)", "\"aaaaaaaaaaa\" -> (3, 3)", "\"aaaaaaaaaaa\" -> (7, 2)", "\"aaaaaaaaaaa\" -> (0, 10)", "\"aaaaaaaaaaaa\" -> (3, 4)", "\"aaaaaaaaaaaa\" -> (7, 3)", "\"aaaaaaaaaaaa\" -> (7, 3)", "\"aaaaaaaaaaaa\" -> (3, 4)", "\"aaaaaaaaaaaa\" -> (12, 2)", "\"aaaaaaaaaaaa\" -> (11, 9)", "\"aaaaaaaaaaaa\" -> (12, 2)", "\"aaaaaaaaaaaa\" -> (14, 8)", "\"aaaaaaaaaaaa\" -> (6, 10)", "\"aaaaaaaaaaaa\" -> (16, 1)", "\"aaaaaaaaaaaa\" -> (0, 11)", "\"aaaaaaaaaaaaa\" -> (7, 4)", "\"aaaaaaaaaaaaa\" -> (3, 5)", "\"aaaaaaaaaaaaa\" -> (11, 10)", "\"aaaaaaaaaaaaa\" -> (12, 3)", "\"aaaaaaaaaaaaa\" -> (6, 11)", "\"aaaaaaaaaaaaa\" -> (14, 9)", "\"aaaaaaaaaaaaa\" -> (16, 2)", "\"aaaaaaaaaaaaa\" -> (7, 4)", "\"aaaaaaaaaaaaa\" -> (3, 5)", "\"aaaaaaaaaaaaa\" -> (12, 3)", "\"aaaaaaaaaaaaa\" -> (0, 12)", "\"aaaaaaaaaaaaaa\" -> (16, 3)", "\"aaaaaaaaaaaaaa\" -> (12, 4)", "\"aaaaaaaaaaaaaa\" -> (14, 10)", "\"aaaaaaaaaaaaaa\" -> (11, 11)"] next_leaf: Some(Pointer(15)))
                        (15) leaf: [parent: 2, inx: true](kvs: ["\"aaaaaaaaaaaaaa\" -> (3, 6)", "\"aaaaaaaaaaaaaa\" -> (7, 5)", "\"aaaaaaaaaaaaaa\" -> (7, 5)", "\"aaaaaaaaaaaaaa\" -> (12, 4)", "\"aaaaaaaaaaaaaa\" -> (3, 6)", "\"aaaaaaaaaaaaaa\" -> (6, 12)", "\"aaaaaaaaaaaaaa\" -> (0, 13)", "\"aaaaaaaaaaaaaaa\" -> (7, 6)", "\"aaaaaaaaaaaaaaa\" -> (7, 6)", "\"aaaaaaaaaaaaaaa\" -> (12, 5)", "\"aaaaaaaaaaaaaaa\" -> (12, 5)", "\"aaaaaaaaaaaaaaa\" -> (5, 0)", "\"aaaaaaaaaaaaaaa\" -> (11, 12)", "\"aaaaaaaaaaaaaaa\" -> (16, 4)", "\"aaaaaaaaaaaaaaa\" -> (14, 11)", "\"aaaaaaaaaaaaaaa\" -> (6, 13)", "\"aaaaaaaaaaaaaaa\" -> (5, 0)", "\"aaaaaaaaaaaaaaa\" -> (3, 7)", "\"aaaaaaaaaaaaaaaa\" -> (5, 1)", "\"aaaaaaaaaaaaaaaa\" -> (7, 7)", "\"aaaaaaaaaaaaaaaa\" -> (11, 13)", "\"aaaaaaaaaaaaaaaa\" -> (16, 5)", "\"aaaaaaaaaaaaaaaa\" -> (14, 12)", "\"aaaaaaaaaaaaaaaa\" -> (8, 0)", "\"aaaaaaaaaaaaaaaa\" -> (5, 1)", "\"aaaaaaaaaaaaaaaa\" -> (12, 6)", "\"aaaaaaaaaaaaaaaa\" -> (12, 6)", "\"aaaaaaaaaaaaaaaa\" -> (8, 0)", "\"aaaaaaaaaaaaaaaa\" -> (3, 8)", "\"aaaaaaaaaaaaaaaaa\" -> (14, 13)", "\"aaaaaaaaaaaaaaaaa\" -> (13, 0)", "\"aaaaaaaaaaaaaaaaa\" -> (5, 2)", "\"aaaaaaaaaaaaaaaaa\" -> (8, 1)", "\"aaaaaaaaaaaaaaaaa\" -> (7, 8)", "\"aaaaaaaaaaaaaaaaa\" -> (12, 7)", "\"aaaaaaaaaaaaaaaaa\" -> (13, 0)", "\"aaaaaaaaaaaaaaaaa\" -> (16, 6)", "\"aaaaaaaaaaaaaaaaa\" -> (8, 1)", "\"aaaaaaaaaaaaaaaaa\" -> (5, 2)", "\"aaaaaaaaaaaaaaaaa\" -> (3, 9)", "\"aaaaaaaaaaaaaaaaaa\" -> (5, 3)", "\"aaaaaaaaaaaaaaaaaa\" -> (8, 2)", "\"aaaaaaaaaaaaaaaaaa\" -> (12, 8)", "\"aaaaaaaaaaaaaaaaaa\" -> (13, 1)", "\"aaaaaaaaaaaaaaaaaa\" -> (16, 7)", "\"aaaaaaaaaaaaaaaaaa\" -> (13, 1)", "\"aaaaaaaaaaaaaaaaaa\" -> (8, 2)", "\"aaaaaaaaaaaaaaaaaa\" -> (7, 9)", "\"aaaaaaaaaaaaaaaaaa\" -> (5, 3)", "\"aaaaaaaaaaaaaaaaaa\" -> (3, 10)", "\"aaaaaaaaaaaaaaaaaaa\" -> (5, 4)", "\"aaaaaaaaaaaaaaaaaaa\" -> (13, 2)", "\"aaaaaaaaaaaaaaaaaaa\" -> (16, 8)", "\"aaaaaaaaaaaaaaaaaaa\" -> (13, 2)", "\"aaaaaaaaaaaaaaaaaaa\" -> (12, 9)", "\"aaaaaaaaaaaaaaaaaaa\" -> (8, 3)", "\"aaaaaaaaaaaaaaaaaaa\" -> (8, 3)", "\"aaaaaaaaaaaaaaaaaaa\" -> (7, 10)", "\"aaaaaaaaaaaaaaaaaaa\" -> (5, 4)", "\"aaaaaaaaaaaaaaaaaaa\" -> (3, 11)"] next_leaf: None)
                    */
                    let inx = child_pointer_pairs
                        .binary_search_by_key(&&key, |(_, key)| key)
                        .unwrap_or_else(|x| x);

                    child_pointer_pairs.insert(inx, (Pointer(right_child_num), key));

                    let split_inx = find_index_to_split_by_value(&child_pointer_pairs)?;
                    // split
                    let siblings = child_pointer_pairs.split_off(split_inx);

                    let new_page_num = self.pager.borrow().get_unused_page_num();
                    let new_page =
                        self.pager
                            .borrow_mut()
                            .get_page(new_page_num, key_size, row_size)?;
                    // create and update new node

                    let new_node = Node::new(
                        NodeType::Internal {
                            child_pointer_pairs: siblings,
                        },
                        false,
                        is_index,
                        node.parent,
                        key_size,
                        row_size,
                    );
                    let new_node_max_key = new_node.max_key();
                    new_node.update_children_parent(
                        new_page_num,
                        self.pager.clone(),
                        key_size,
                        row_size,
                    )?;
                    new_page.borrow_mut().data = new_node.try_into()?;

                    // update old node

                    let old_node = Node::new(
                        NodeType::Internal {
                            child_pointer_pairs,
                        },
                        false,
                        is_index,
                        node.parent,
                        key_size,
                        row_size,
                    );
                    let old_node_max_key = old_node.max_key();
                    old_node.update_children_parent(
                        page_num,
                        self.pager.clone(),
                        key_size,
                        row_size,
                    )?;
                    page.borrow_mut().data = old_node.try_into()?;

                    if node.is_root {
                        // split root
                        // root page has to stay as it was, because of that we need to allocate another page
                        // copy content and change that page data
                        let new_root_left_child_page_num =
                            self.pager.borrow().get_unused_page_num();
                        let new_root_left_child_page = self.pager.borrow_mut().get_page(
                            new_root_left_child_page_num,
                            key_size,
                            row_size,
                        )?;
                        new_root_left_child_page.borrow_mut().data = page.borrow().data;

                        let node = Node::try_from(new_root_left_child_page.clone())?;
                        node.update_children_parent(
                            new_root_left_child_page_num,
                            self.pager.clone(),
                            key_size,
                            row_size,
                        )?;
                        new_root_left_child_page.borrow_mut().data = node.try_into()?;

                        // clone data
                        let root = Node::new(
                            NodeType::Internal {
                                child_pointer_pairs: vec![
                                    (Pointer(new_root_left_child_page_num), old_node_max_key),
                                    (Pointer(new_page_num), new_node_max_key),
                                ],
                            },
                            true,
                            is_index,
                            None,
                            key_size,
                            row_size,
                        );
                        page.borrow_mut().data = root.try_into()?;
                    } else {
                        // update parent
                        let parent = node
                            .parent
                            .context("internal node which is not root without parent")?;
                        dbg!(page_num, &old_node_max_key);
                        self.insert_into_internal(
                            parent,
                            new_page_num,
                            old_node_max_key,
                            None,
                            row_size,
                        )?;
                    }
                } else {
                    let inx = child_pointer_pairs
                        .binary_search_by_key(&&key, |(_, key)| key)
                        .unwrap_or_else(|x| x);
                    child_pointer_pairs.insert(inx, (Pointer(right_child_num), key));

                    // update node
                    page.borrow_mut().data = Node::new(
                        NodeType::Internal {
                            child_pointer_pairs,
                        },
                        node.is_root,
                        is_index,
                        node.parent,
                        key_size,
                        row_size,
                    )
                    .try_into()?;
                }
            }
            NodeType::Leaf {
                kvs: _,
                next_leaf: _,
            } => bail!("parent node cannot be leaf node"),
        }

        Ok(())
    }

    pub fn select_by_key<F>(
        &mut self,
        mut cmp: F,
        key_size: usize,
        row_size: usize,
    ) -> anyhow::Result<Vec<Vec<u8>>>
    where
        F: FnMut(&Vec<u8>) -> bool,
    {
        let mut data = vec![];

        select_all(
            self.pager.clone(),
            self.page_num,
            |_, _, Key(key), bytes| {
                if cmp(&key) {
                    data.push(bytes)
                }
            },
            key_size,
            row_size,
        )?;

        Ok(data)
    }

    pub fn select_by<F>(
        &mut self,
        mut cmp: F,
        key_size: usize,
        row_size: usize,
    ) -> anyhow::Result<Vec<Vec<u8>>>
    where
        F: FnMut(&Vec<u8>) -> bool,
    {
        let mut data = vec![];

        select_all(
            self.pager.clone(),
            self.page_num,
            |_, _, _, bytes| {
                if cmp(&bytes) {
                    data.push(bytes)
                }
            },
            key_size,
            row_size,
        )?;

        Ok(data)
    }

    pub fn select(&mut self, key_size: usize, row_size: usize) -> anyhow::Result<Vec<Vec<u8>>> {
        let mut data = vec![];

        select_all(
            self.pager.clone(),
            self.page_num,
            |_, _, _, bytes| data.push(bytes),
            key_size,
            row_size,
        )?;

        Ok(data)
    }

    pub fn data(&self, key_size: usize, row_size: usize) -> anyhow::Result<Option<Vec<u8>>> {
        let page = self
            .pager
            .borrow_mut()
            .get_page(self.page_num, key_size, row_size)?;
        let node = Node::try_from(page)?;
        match node.node_type {
            NodeType::Internal {
                child_pointer_pairs: _,
            } => bail!("cannot convert Internal Node into Row"),
            NodeType::Leaf { kvs, next_leaf: _ } => {
                if self.cell_num as usize >= kvs.len() {
                    // not found
                    return Ok(None);
                }

                let (_, data) = kvs.get(self.cell_num as usize).with_context(|| {
                    format!("could not get {} kv from Leaf Node", self.cell_num)
                })?;
                Ok(Some(data.clone()))
            }
        }
    }
}

/// Searches for median value first, then find first occurrence - this will be our index.
fn find_index_to_split_by_value<T, V: Clone + PartialEq>(
    values: &Vec<(T, V)>,
) -> anyhow::Result<usize> {
    let mid = values.len() / 2;
    let median_key = values
        .get(mid)
        .context("could not get median value")?
        .1
        .clone();
    let (inx, _) = values
        .iter()
        .enumerate()
        .map(|(i, (_, k))| (i, k))
        .find(|(_, k)| *k == &median_key)
        .context("could not get inx of median value")?;
    Ok(inx)
}

fn find_index_to_split_by_key<T: Clone + PartialEq, V>(
    values: &Vec<(T, V)>,
) -> anyhow::Result<usize> {
    let mid = (values.len() + 1) / 2;
    let median = values
        .get(mid)
        .context("could not get median value")?
        .0
        .clone();

    let (inx, _) = values
        .iter()
        .enumerate()
        .map(|(i, (v, _))| (i, v))
        .find(|(_, v)| *v == &median)
        .context("could not get inx of median value")?;

    if inx == 0 {
        // it means that all elements are equal
        return Ok(values.len() / 2);
    }

    Ok(inx)
}

fn select_all<F: FnMut(u32, u32, Key, Vec<u8>)>(
    pager: Rc<RefCell<Pager>>,
    page_num: u32,
    mut f: F,
    key_size: usize,
    row_size: usize,
) -> anyhow::Result<()> {
    let page = pager.borrow_mut().get_page(page_num, key_size, row_size)?;
    let node = Node::try_from(page)?;

    match node.node_type {
        NodeType::Internal {
            child_pointer_pairs,
        } => {
            let (Pointer(p), _) = child_pointer_pairs
                .iter()
                .min_by_key(|(p, key)| key)
                .context("minimum pointer could not be cound")?;
            // go to the lowest, to the left leaf, then we will use `next_leaf` field to traverse all leafs
            select_all(pager, *p, f, key_size, row_size)?;
        }
        NodeType::Leaf { kvs, next_leaf } => {
            for (inx, (key, row_bytes)) in kvs.into_iter().enumerate() {
                f(page_num, inx as u32, key, row_bytes);
            }

            if let Some(Pointer(next)) = next_leaf {
                select_all(pager, next, f, key_size, row_size)?; // go to the next leaf
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod test {
    use std::{cell::RefCell, fs::File, rc::Rc};

    use anyhow::Ok;
    use tempdir::TempDir;

    use crate::{
        node::{Node, NodeType, Pointer},
        pager::{Page, Pager},
        table::{Row, Serialize},
    };

    use super::Cursor;

    #[test]
    fn test_leaf_node_split_and_insert() -> anyhow::Result<()> {
        let tmp_dir = TempDir::new("databurst")?;
        let file_path = tmp_dir.path().join("my.db");
        let _f = File::create(&file_path)?;

        let row_bytes =
            Row::try_from((1, "username".to_string(), "email".to_string()))?.serialize();
        let key_size = 4;
        let row_size = row_bytes.len();

        let mut pager = Pager::new(file_path)?;
        pager.num_pages = 3;

        let root = Node::new(
            NodeType::Internal {
                child_pointer_pairs: vec![(Pointer(0), 1.into())],
            },
            true,
            false,
            None,
            key_size,
            row_size,
        );

        let node_1 = Node::new(
            NodeType::Leaf {
                kvs: vec![
                    (1.into(), row_bytes.clone()),
                    (2.into(), row_bytes.clone()),
                    (3.into(), row_bytes.clone()),
                    (4.into(), row_bytes.clone()),
                    (5.into(), row_bytes.clone()),
                    (6.into(), row_bytes.clone()),
                    (7.into(), row_bytes.clone()),
                    (8.into(), row_bytes.clone()),
                    (9.into(), row_bytes.clone()),
                    (10.into(), row_bytes.clone()),
                    (11.into(), row_bytes.clone()),
                    (12.into(), row_bytes.clone()),
                    (13.into(), row_bytes.clone()),
                ],
                next_leaf: Some(Pointer(2)),
            },
            false,
            false,
            Some(0),
            key_size,
            row_size,
        );
        let node_2 = Node::new(
            NodeType::Leaf {
                kvs: vec![],
                next_leaf: None,
            },
            false,
            false,
            Some(0),
            key_size,
            row_size,
        );

        let page_1 = Rc::new(RefCell::new(Page::try_from(node_1)?));
        let page_2 = Rc::new(RefCell::new(Page::try_from(node_2)?));

        pager.pages_rc[0] = Some(Rc::new(RefCell::new(Page::try_from(root)?)));
        pager.pages_rc[1] = Some(page_1.clone());
        pager.pages_rc[2] = Some(page_2);

        let pager = Rc::new(RefCell::new(pager));
        let cursor = Cursor::new(pager.clone(), 1, 0);
        cursor.leaf_node_split_and_insert(15.into(), &row_bytes)?;

        let node_1 = Node::try_from(page_1)?;

        let new_node = Node::try_from(pager.borrow_mut().get_page(3, key_size, row_size)?)?;

        match node_1.node_type {
            NodeType::Internal {
                child_pointer_pairs: _,
            } => {
                panic!("node cannot be internal");
            }
            NodeType::Leaf { kvs: _, next_leaf } => {
                assert_eq!(next_leaf.unwrap().0, 3);
            }
        };
        match new_node.node_type {
            NodeType::Internal {
                child_pointer_pairs: _,
            } => {
                panic!("node cannot be internal");
            }
            NodeType::Leaf { kvs: _, next_leaf } => {
                assert_eq!(next_leaf.unwrap().0, 2); // points to node_1, where node_0 pointed before
            }
        };

        Ok(())
    }
}
