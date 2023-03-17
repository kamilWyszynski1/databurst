use std::env;

use cli::input_loop;

#[allow(dead_code)]
mod cli;
mod constants;
mod pager;
mod table;

fn main() {
    let args: Vec<String> = env::args().collect();
    dbg!(args);

    // input_loop(table);
}
