use std::{cell::RefCell, rc::Rc};

use crate::{constants::ROWS_PER_PAGE, pager::Pager};

pub struct Cursor {
    pager: Rc<RefCell<Pager>>,
    row_num: usize,
    pub end_of_table: bool,
}

impl Cursor {
    pub fn new(pager: Rc<RefCell<Pager>>, row_num: usize, end_of_table: bool) -> Self {
        Self {
            pager,
            row_num,
            end_of_table,
        }
    }

    pub fn cursor_value(&self) -> anyhow::Result<Option<Rc<RefCell<Vec<u8>>>>> {
        let page_num = self.row_num / ROWS_PER_PAGE;
        let page = self.pager.try_borrow_mut()?.get_page(page_num)?;

        let x = Ok(Some(
            page.try_borrow_mut()?.get(self.row_num % ROWS_PER_PAGE)?,
        ));
        x
    }

    pub fn advance(&mut self, table_rows_num: usize) {
        self.row_num += 1;
        if self.row_num >= table_rows_num {
            self.end_of_table = true
        }
    }
}
