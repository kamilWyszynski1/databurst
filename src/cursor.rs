use std::{cell::RefCell, rc::Rc};

use anyhow::Ok;

use crate::{node::Node, pager::Pager};

pub struct Cursor {
    pager: Rc<RefCell<Pager>>,
    pub end_of_table: bool,

    page_num: usize,
    pub cell_num: usize,
}

impl Cursor {
    pub fn new(
        pager: Rc<RefCell<Pager>>,
        page_num: usize,
        cell_num: usize,
        end_of_table: bool,
    ) -> Self {
        Self {
            pager,
            cell_num,
            page_num,
            end_of_table,
        }
    }

    pub fn cursor_value(&self) -> anyhow::Result<Vec<u8>> {
        let page = self.pager.try_borrow_mut()?.get_page(self.page_num)?;
        let node = Node::try_from(page.borrow().clone())?;

        Ok(node.leaf_node_value(self.cell_num)?)
    }

    pub fn insert(&self, key: u32, data: &[u8]) -> anyhow::Result<()> {
        let page = self.pager.try_borrow_mut()?.get_page(self.page_num)?;

        // turn page's bytes into readable node
        let mut node = Node::try_from(page.borrow().clone())?;

        // insert value
        match &mut node.node_type {
            crate::node::NodeType::Internal(_, _) => todo!(),
            crate::node::NodeType::Leaf(ref mut kvs) => {
                // cell_num was set by binary search, it will be inserted in order
                kvs.insert(self.cell_num, (key, data.to_vec()));
            }
        }

        // turn node back into bytes
        page.borrow_mut().data = node.try_into()?;

        Ok(())
    }
    /// Create a new node and move half the cells over.
    /// Insert the new value in one of the two nodes.
    /// Update parent or create a new parent.
    pub fn leaf_node_split_and_insert(&mut self, key: u32, data: &[u8]) -> anyhow::Result<()> {
        let old_node = Node::try_from(self.pager.borrow_mut().get_page(self.page_num)?)?;
        let new_page_num = self.pager.borrow().get_unused_page_num();

        let new_node = Node::try_from(self.pager.borrow_mut().get_page(new_page_num)?)?;

        // All existing keys plus new key should be divided
        // evenly between old (left) and new (right) nodes.
        // Starting from the right, move each key to correct position.

        todo!()
    }

    pub fn advance(&mut self) -> anyhow::Result<()> {
        let page_num = self.page_num;
        let node = Node::try_from(self.pager.borrow_mut().get_page(page_num)?.borrow().clone())?;

        self.cell_num += 1;

        if self.cell_num >= node.num_cells() as usize {
            self.end_of_table = true
        }

        Ok(())
    }
}