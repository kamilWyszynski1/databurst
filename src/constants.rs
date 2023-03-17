use crate::table::{EMAIL_SIZE, ID_SIZE, USERNAME_SIZE};

pub const ID_OFFSET: usize = 0;
pub const USERNAME_OFFSET: usize = ID_OFFSET + ID_SIZE;
pub const EMAIL_OFFSET: usize = USERNAME_OFFSET + USERNAME_SIZE;
pub const ROWS_SIZE: usize = ID_SIZE + USERNAME_SIZE + EMAIL_SIZE;

pub const TABLE_MAX_PAGES: usize = 100;
pub const PAGE_SIZE: usize = 4096; // 4KB
pub const ROWS_PER_PAGE: usize = PAGE_SIZE / ROWS_SIZE;
pub const TABLE_MAX_ROWS: usize = ROWS_PER_PAGE * TABLE_MAX_PAGES;
