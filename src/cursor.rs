use std::{cell::RefCell, rc::Rc};

use anyhow::{Context, Ok};

use crate::{
    constants::LEAF_NODE_MAX_CELLS,
    node::{Node, NodeType, Pointer},
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

    pub fn cursor_value(&self) -> anyhow::Result<Option<Vec<u8>>> {
        let page = self.pager.try_borrow_mut()?.get_page(self.page_num)?;
        let node = Node::try_from(page.borrow().clone())?;

        Ok(node.leaf_node_value(self.cell_num)?)
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
            crate::node::NodeType::Leaf(ref mut kvs) => {
                // cell_num was set by binary search, it will be inserted in order
                kvs.insert(self.cell_num as usize, (key, data.to_vec()));
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
            if let NodeType::Leaf(mut kvs) = left_node.node_type {
                kvs.insert(self.cell_num as usize, (key, data.to_vec()));
                let siblings_kvs = kvs.split_off((kvs.len() + 1) / 2);

                left_page.borrow_mut().data =
                    Node::new(NodeType::Leaf(kvs), false, left_node.parent).try_into()?;
                right_page.borrow_mut().data =
                    Node::new(NodeType::Leaf(siblings_kvs), false, left_node.parent).try_into()?;
            } else {
                panic!("node is not a Leaf")
            }
        }

        if left_node.is_root {
            let left_child_max_key = Node::try_from(left_page.clone())?.max_key();
            // root page has to stay as it was, because of that we need to allocate another page
            // copy content and change that page data
            let new_left_page_num = self.pager.borrow().get_unused_page_num();
            let new_left_page = self.pager.borrow_mut().get_page(new_left_page_num)?;
            new_left_page.borrow_mut().data = left_page.borrow().data; // clone data

            // split the root
            let root = Node::new(
                NodeType::Internal {
                    right_child: Pointer(right_page_num as u32),
                    child_pointer_pairs: vec![(
                        Pointer(new_left_page_num as u32),
                        left_child_max_key,
                    )],
                },
                true,
                None,
            );
            left_page.borrow_mut().data = root.try_into()?; // rewrite root
        } else {
            unimplemented!()
        }

        Ok(())
    }

    pub fn advance(&mut self) -> anyhow::Result<()> {
        let page_num = self.page_num;
        let node = Node::try_from(self.pager.borrow_mut().get_page(page_num)?.borrow().clone())?;

        self.cell_num += 1;

        if self.cell_num >= node.num_cells() as u32 {
            self.end_of_table = true
        }

        Ok(())
    }
}
