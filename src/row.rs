use anyhow::{bail, Context};

use crate::table::vector_to_array;

/// If header is greater than 13 (indicator + size of text bytes) we know this will be a text.
/// Something similar is implemented in sqlite https://www.sqlite.org/fileformat2.html.
const TEXT_INDICATOR: u8 = 13;

const TEXT_SIZE: usize = 255;

const MAX_COLUMNS: u8 = 255;

#[derive(Debug, Clone, PartialEq)]
//TODO: definition does not need values inside those variatns :face-palm
enum RowType {
    Integer(i32),
    Text { text: String, size: u8 }, // max text size is 255 - 13
    Bool(bool),
}

impl Into<Vec<u8>> for &RowType {
    fn into(self) -> Vec<u8> {
        match self {
            RowType::Integer(i) => i.to_be_bytes().to_vec(),
            RowType::Text { text, size } => {
                let mut bytes = text.clone().into_bytes();
                bytes.append(&mut vec![0u8; *size as usize - bytes.len()]); // fill missing bytes
                bytes
            }
            RowType::Bool(b) => vec![*b as u8],
        }
    }
}

// header size and value
impl TryFrom<(u8, Vec<u8>)> for RowType {
    type Error = anyhow::Error;

    fn try_from(value: (u8, Vec<u8>)) -> anyhow::Result<Self, Self::Error> {
        let (header_size, bytes) = value;

        if header_size as usize != bytes.len() {
            bail!("header_size and bytes' len does not match")
        }

        if header_size == 4 {
            // integer
            let value = i32::from_be_bytes(vector_to_array(bytes)?);
            Ok(Self::Integer(value))
        } else if header_size == 1 {
            // bool
            Ok(Self::Bool(bytes[0] == 1))
        } else if header_size >= TEXT_INDICATOR {
            Ok(Self::Text {
                text: String::from_utf8(bytes)?,
                size: header_size,
            })
        } else {
            bail!("could not parse RowType from header size and bytes")
        }
    }
}

impl RowType {
    fn header_size(&self) -> u8 {
        match self {
            RowType::Integer(_) => 4,
            RowType::Bool(_) => 1,
            RowType::Text { text: _, size } => TEXT_INDICATOR + *size,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct Column {
    name: String, // max 255 characters
    row_type: RowType,
}

//TODO: prepare constructors, we need to validate sizes of strings
/// 255    + (1)           + (<255)       + (255 + 1 / 4 / >= 13)
/// name    columns amount  columns types   columns definition
#[derive(Debug, Clone, PartialEq)]
struct TableDefinition {
    name: String, // max 255 characters

    // column's name to its type mapping
    columns: Vec<Column>,
}

impl TryFrom<Vec<u8>> for TableDefinition {
    type Error = anyhow::Error;

    fn try_from(value: Vec<u8>) -> Result<Self, Self::Error> {
        if value.len() < 255 + 1 + 255 {
            // table's name and first column's name
            bail!("seems like table does not have any columns")
        }

        let mut offset: usize = 0;

        let table_name = String::from_utf8(value[offset..TEXT_SIZE].to_vec())?;
        offset += TEXT_SIZE;
        let columns_amount = value[offset];
        offset += 1;

        // take next 'columns_amount' bytes, these describes columns types
        let mut types = vec![];
        for _ in 0..columns_amount {
            types.push(value[offset] as usize);
            offset += 1;
        }

        let mut columns = vec![];
        for i in 0..(columns_amount as usize) {
            let column_name = String::from_utf8(value[offset..TEXT_SIZE].to_vec())?;
            offset += TEXT_SIZE;
            let row_type = RowType::try_from((types[i] as u8, value[offset..types[i]].to_vec()))?;
            columns.push(Column {
                name: column_name,
                row_type,
            })
        }
        Ok(TableDefinition {
            name: table_name,
            columns,
        })
    }
}

impl From<TableDefinition> for Vec<u8> {
    fn from(val: TableDefinition) -> Self {
        let mut bytes = vec![];
        let mut name_bytes = val.name.as_bytes().to_vec();
        bytes.append(&mut name_bytes);
        bytes.push(val.columns.len() as u8);

        for Column { name: _, row_type } in &val.columns {
            bytes.push(row_type.header_size())
        }

        for Column { name, ref row_type } in val.columns {
            let mut name_bytes = name.as_bytes().to_vec();
            bytes.append(&mut name_bytes);
            let mut b = row_type.into();
            bytes.append(&mut b)
        }
        bytes
    }
}

#[cfg(test)]
mod tests {
    use super::{Column, RowType, TableDefinition};

    #[test]
    fn test_table_definition() {
        let text1 = "lorem ipsum for testing".to_string();
        let text2 = "this text does not make sense lol".to_string();

        let t = TableDefinition {
            name: "my table lol".to_string(),
            columns: vec![
                Column {
                    name: "column1".to_string(),
                    row_type: RowType::Integer(123),
                },
                Column {
                    name: "column2".to_string(),
                    row_type: RowType::Integer(5000),
                },
                Column {
                    name: "column3".to_string(),
                    row_type: RowType::Bool(false),
                },
                Column {
                    name: "column4".to_string(),
                    row_type: RowType::Bool(true),
                },
                Column {
                    name: "column5".to_string(),
                    row_type: RowType::Text {
                        size: text1.len() as u8,
                        text: text1,
                    },
                },
                Column {
                    name: "column6".to_string(),
                    row_type: RowType::Text {
                        size: text2.len() as u8,
                        text: text2,
                    },
                },
            ],
        };
        let bytes: Vec<u8> = t.clone().into();
        let t_parsed = TableDefinition::try_from(bytes).unwrap();
        assert_eq!(t, t_parsed)
    }
}
