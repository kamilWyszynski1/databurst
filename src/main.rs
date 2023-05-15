use std::env;

use anyhow::Context;
use cli::input_loop;

use crate::table::Table;

#[allow(dead_code)]
mod cli;
mod constants;
mod cursor;
mod node;
mod pager;
mod row;
mod table;

fn main() -> anyhow::Result<()> {
    let args: Vec<String> = env::args().collect();

    let table = Table::db_open(args.get(1).context("database file path must be passed")?)?;

    input_loop(table)
}
