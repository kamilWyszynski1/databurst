use std::io::{self, stdout, Write};

use crate::table::{Row, Table};
use anyhow::anyhow;

fn report(err: anyhow::Error) {
    eprintln!("[ERROR] {}", err);
    if let Some(cause) = err.source() {
        eprintln!();
        eprintln!("Caused by:");
        for (i, e) in std::iter::successors(Some(cause), |e| e.source()).enumerate() {
            eprintln!("   {}: {}", i, e);
        }
    }
}

pub fn input_loop(mut table: Table) {
    loop {
        print!("lipsy>: ");

        let mut input = String::new();
        match io::stdin().read_line(&mut input) {
            Ok(_) => match parse_input(input, &mut table) {
                Ok(_) => {}
                Err(err) => report(err),
            },
            Err(err) => {
                println!("error when reading input, {}", err);
                return;
            }
        }
        stdout().flush().unwrap();
    }
}

fn parse_input(input: String, table: &mut Table) -> anyhow::Result<()> {
    if let Some(query) = parse_query(input)? {
        match query {
            Query::Select => table.into_iter().for_each(|r| println!("{:?}", r)),
            Query::Insert(id, username, email) => {
                table.insert(&Row::try_from((id, username, email))?)?;
            }
        }
    }

    Ok(())
}

#[derive(Debug, PartialEq)]
enum Query {
    Select,
    Insert(u32, String, String),
}

fn parse_query<S: Into<String>>(input: S) -> anyhow::Result<Option<Query>> {
    let input = input.into();

    let mut parts = input.split_whitespace();
    match parts.next() {
        Some("select") => Ok(Some(Query::Select)),
        Some("insert") => {
            let value1 = parts
                .next()
                .ok_or_else(|| anyhow!("Missing value1"))?
                .parse()?;
            let value2 = parts
                .next()
                .ok_or_else(|| anyhow!("Missing value2"))?
                .to_string();
            let value3 = parts
                .next()
                .ok_or_else(|| anyhow!("Missing value3"))?
                .to_string();
            Ok(Some(Query::Insert(value1, value2, value3)))
        }
        _ => Ok(None),
    }
}

#[cfg(test)]
mod test {
    use super::{parse_query, Query};

    #[test]
    fn test_parse_query() {
        assert_eq!(Query::Select, parse_query("select").unwrap().unwrap());
        assert_eq!(
            Query::Insert(1, "username".to_string(), "email".to_string()),
            parse_query("insert 1 username email").unwrap().unwrap()
        )
    }
}
