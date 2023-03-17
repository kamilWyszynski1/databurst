use cli::input_loop;

#[allow(dead_code)]
mod cli;
mod pager;
mod table;
mod constants;

fn main() {
    let table = table::Table::default();

    input_loop(table);
}
