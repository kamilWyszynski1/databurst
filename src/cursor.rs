use std::{any, cell::RefCell, rc::Rc};

use anyhow::{bail, Context, Ok};

use crate::{
    constants::LEAF_NODE_MAX_CELLS,
    node::{Key, Node, NodeType, Pointer},
    pager::Pager,
};

pub struct Cursor {
    pager: Rc<RefCell<Pager>>,
    pub end_of_table: bool,

    page_num: u32,
    pub cell_num: u32,
}

impl Cursor {
    pub fn new(
        pager: Rc<RefCell<Pager>>,
        page_num: u32,
        cell_num: u32,
        end_of_table: bool,
    ) -> Self {
        Self {
            pager,
            cell_num,
            page_num,
            end_of_table,
        }
    }

    pub fn insert(&self, key: u32, data: &[u8]) -> anyhow::Result<()> {
        let page = self.pager.try_borrow_mut()?.get_page(self.page_num)?;

        // turn page's bytes into readable node
        let mut node = Node::try_from(page.borrow().clone())?;

        if node.num_cells() as usize >= LEAF_NODE_MAX_CELLS {
            return self.leaf_node_split_and_insert(key, data);
        }

        // insert value
        match &mut node.node_type {
            crate::node::NodeType::Internal {
                right_child: _,
                child_pointer_pairs: _,
            } => todo!(),
            crate::node::NodeType::Leaf { kvs, next_leaf: _ } => {
                // cell_num was set by binary search, it will be inserted in order
                kvs.insert(self.cell_num as usize, (key.into(), data.to_vec()));
            }
        }

        // turn node back into bytes
        page.borrow_mut().data = node.try_into()?;

        Ok(())
    }

    /// Create a new node and move half the cells over.
    /// Insert the new value in one of the two nodes.
    /// Update parent or create a new parent.
    pub fn leaf_node_split_and_insert(&self, key: u32, data: &[u8]) -> anyhow::Result<()> {
        let left_page = self.pager.borrow_mut().get_page(self.page_num)?;
        let left_node = Node::try_from(left_page.clone())?;

        let right_page_num = self.pager.borrow().get_unused_page_num();

        {
            let right_page = self.pager.borrow_mut().get_page(right_page_num)?;

            // All existing keys plus new key should be divided evenly between old (left) and new (right) nodes.
            if let NodeType::Leaf { mut kvs, next_leaf } = left_node.node_type.clone() {
                kvs.insert(self.cell_num as usize, (key.into(), data.to_vec()));
                let siblings_kvs = kvs.split_off((kvs.len() + 1) / 2);

                left_page.borrow_mut().data = Node::new(
                    NodeType::Leaf {
                        kvs,
                        next_leaf: Some(Pointer(right_page_num)),
                    },
                    false,
                    left_node.parent,
                )
                .try_into()?;
                right_page.borrow_mut().data = Node::new(
                    NodeType::Leaf {
                        kvs: siblings_kvs,
                        next_leaf,
                    },
                    false,
                    left_node.parent,
                )
                .try_into()?;
            } else {
                panic!("node is not a Leaf")
            }
        }

        let left_child_max_key = Node::try_from(left_page.clone())?.max_key();
        if left_node.is_root {
            // root page has to stay as it was, because of that we need to allocate another page
            // copy content and change that page data
            let new_left_page_num = self.pager.borrow().get_unused_page_num();
            let new_left_page = self.pager.borrow_mut().get_page(new_left_page_num)?;
            new_left_page.borrow_mut().data = left_page.borrow().data; // clone data

            // split the root
            let root = Node::new(
                NodeType::Internal {
                    right_child: Pointer(right_page_num),
                    child_pointer_pairs: vec![(
                        Pointer(new_left_page_num),
                        left_child_max_key.into(),
                    )],
                },
                true,
                None,
            );
            left_page.borrow_mut().data = root.try_into()?; // rewrite root
        } else {
            // update leaf's parent
            let page_num = left_node.parent.context("no parent")?;
            self.insert_into_internal(page_num, right_page_num, left_child_max_key)?;
        }

        Ok(())
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
        key: u32,
    ) -> anyhow::Result<()> {
        let page = self.pager.borrow_mut().get_page(page_num)?;
        let node = Node::try_from(page.clone())?;

        match node.node_type {
            NodeType::Internal {
                mut right_child,
                mut child_pointer_pairs,
            } => {
                let pointers_len = child_pointer_pairs.len();
                if pointers_len == LEAF_NODE_MAX_CELLS {
                    // find place to insert key
                    let inx = child_pointer_pairs
                        .binary_search_by_key(&key, |(_, Key(key))| *key)
                        .unwrap_or_else(|x| x);
                    child_pointer_pairs.insert(inx, (Pointer(self.page_num), Key(key)));

                    // split
                    let siblings = child_pointer_pairs.split_off((pointers_len + 1) / 2);
                    // find max pointer-key pair in left child
                    let (max_pointer, max_left) = child_pointer_pairs
                        .clone()
                        .into_iter()
                        .max_by_key(|(_, Key(key))| *key)
                        .context("cannot find max")?;

                    let new_page_num = self.pager.borrow().get_unused_page_num();
                    let new_page = self.pager.borrow_mut().get_page(new_page_num)?;
                    // create and update new node
                    {
                        let new_node = Node::new(
                            NodeType::Internal {
                                right_child,
                                child_pointer_pairs: siblings,
                            },
                            false,
                            node.parent,
                        );
                        new_node.update_children_parent(new_page_num, self.pager.clone())?;
                        new_page.borrow_mut().data = new_node.try_into()?;
                    }
                    // update old node
                    {
                        let node = Node::new(
                            NodeType::Internal {
                                right_child: max_pointer,
                                child_pointer_pairs,
                            },
                            false,
                            node.parent,
                        );
                        node.update_children_parent(page_num, self.pager.clone())?;
                        page.borrow_mut().data = node.try_into()?;
                    }

                    if node.is_root {
                        // split root
                        // root page has to stay as it was, because of that we need to allocate another page
                        // copy content and change that page data
                        let new_root_left_child_page_num =
                            self.pager.borrow().get_unused_page_num();
                        let new_root_left_child_page = self
                            .pager
                            .borrow_mut()
                            .get_page(new_root_left_child_page_num)?;
                        new_root_left_child_page.borrow_mut().data = page.borrow().data;
                        {
                            let mut node = Node::try_from(new_root_left_child_page.clone())?;
                            node.update_children_parent(
                                new_root_left_child_page_num,
                                self.pager.clone(),
                            )?;
                            node.remove_overriding_pointers(self.pager.clone())?;
                            new_root_left_child_page.borrow_mut().data = node.try_into()?;
                        }

                        // clone data
                        let root = Node::new(
                            NodeType::Internal {
                                right_child: Pointer(new_page_num),
                                child_pointer_pairs: vec![(
                                    Pointer(new_root_left_child_page_num),
                                    max_left,
                                )],
                            },
                            true,
                            None,
                        );
                        page.borrow_mut().data = root.try_into()?;
                    } else {
                        // update parent
                        let parent = node
                            .parent
                            .context("internal node which is not root without parent")?;
                        self.insert_into_internal(parent, new_page_num, max_left.0)?;
                    }
                } else {
                    if key
                        >= child_pointer_pairs
                            .last()
                            .context("there's no last item")?
                            .1
                             .0
                    {
                        let right_child_key =
                            Node::try_from(self.pager.borrow_mut().get_page(right_child.0)?)?
                                .max_key();
                        child_pointer_pairs.push((right_child, Key(right_child_key)));
                        right_child = Pointer(right_child_num);
                    } else {
                        let inx = child_pointer_pairs
                            .binary_search_by_key(&key, |(_, Key(key))| *key)
                            .unwrap_or_else(|x| x);
                        child_pointer_pairs.insert(inx, (Pointer(self.page_num), Key(key)));
                    }

                    // update node
                    page.borrow_mut().data = Node::new(
                        NodeType::Internal {
                            right_child,
                            child_pointer_pairs,
                        },
                        node.is_root,
                        node.parent,
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

    pub fn select(&mut self) -> anyhow::Result<Vec<Vec<u8>>> {
        let mut data = vec![];
        self.select_all(self.page_num, &mut data)?;

        Ok(data)
    }

    fn select_all(&mut self, page_num: u32, data: &mut Vec<Vec<u8>>) -> anyhow::Result<()> {
        let page = self.pager.borrow_mut().get_page(page_num)?;
        let node = Node::try_from(page)?;

        match node.node_type {
            NodeType::Internal {
                right_child: _,
                child_pointer_pairs,
            } => {
                // go to the lowest leaf, then we will use `next_leaf` field to traverse all leafs
                self.select_all(
                    child_pointer_pairs
                        .get(0)
                        .context("could not get first child in internal node")?
                        .0
                         .0,
                    data,
                )?;
            }
            NodeType::Leaf { kvs, next_leaf } => {
                for (_, row_bytes) in kvs {
                    data.push(row_bytes);
                }

                if let Some(Pointer(next)) = next_leaf {
                    self.select_all(next, data)?; // go to the next leaf
                }
            }
        }

        Ok(())
    }

    pub fn advance(&mut self) -> anyhow::Result<()> {
        let page_num = self.page_num;
        let node = Node::try_from(self.pager.borrow_mut().get_page(page_num)?.borrow().clone())?;

        self.cell_num += 1;

        if self.cell_num >= node.num_cells() {
            self.end_of_table = true
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use std::{cell::RefCell, fs::File, rc::Rc};

    use anyhow::Ok;
    use tempdir::TempDir;

    use crate::{
        node::{Key, Node, NodeType, Pointer},
        pager::{Page, Pager},
        table::Row,
    };

    use super::Cursor;

    #[test]
    fn test_leaf_node_split_and_insert() -> anyhow::Result<()> {
        let tmp_dir = TempDir::new("databurst")?;
        let file_path = tmp_dir.path().join("my.db");
        let _f = File::create(&file_path)?;

        let mut pager = Pager::new(file_path)?;
        pager.num_pages = 3;

        let row_bytes =
            Row::try_from((1, "username".to_string(), "email".to_string()))?.serialize();

        let root = Node::new(
            NodeType::Internal {
                right_child: Pointer(1),
                child_pointer_pairs: vec![(Pointer(0), Key(1))],
            },
            true,
            None,
        );

        let node_1 = Node::new(
            NodeType::Leaf {
                kvs: vec![
                    (Key(1), row_bytes.clone()),
                    (Key(2), row_bytes.clone()),
                    (Key(3), row_bytes.clone()),
                    (Key(4), row_bytes.clone()),
                    (Key(5), row_bytes.clone()),
                    (Key(6), row_bytes.clone()),
                    (Key(7), row_bytes.clone()),
                    (Key(8), row_bytes.clone()),
                    (Key(9), row_bytes.clone()),
                    (Key(10), row_bytes.clone()),
                    (Key(11), row_bytes.clone()),
                    (Key(12), row_bytes.clone()),
                    (Key(13), row_bytes.clone()),
                ],
                next_leaf: Some(Pointer(2)),
            },
            false,
            Some(0),
        );
        let node_2 = Node::new(
            NodeType::Leaf {
                kvs: vec![],
                next_leaf: None,
            },
            false,
            Some(0),
        );

        let page_1 = Rc::new(RefCell::new(Page::try_from(node_1)?));
        let page_2 = Rc::new(RefCell::new(Page::try_from(node_2)?));

        pager.pages_rc[0] = Some(Rc::new(RefCell::new(Page::try_from(root)?)));
        pager.pages_rc[1] = Some(page_1.clone());
        pager.pages_rc[2] = Some(page_2);

        let pager = Rc::new(RefCell::new(pager));
        let cursor = Cursor::new(pager.clone(), 1, 0, false);
        cursor.leaf_node_split_and_insert(15, &row_bytes)?;

        let node_1 = Node::try_from(page_1)?;

        let new_node = Node::try_from(pager.borrow_mut().get_page(3)?)?;

        match node_1.node_type {
            NodeType::Internal {
                right_child: _,
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
                right_child: _,
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
