use anyhow::bail;

/// If header is greater than 13 (indicator + size of text bytes) we know this will be a text.
/// Something similar is implemented in sqlite https://www.sqlite.org/fileformat2.html.
const TEXT_INDICATOR: u8 = 13;

const TEXT_SIZE: usize = 255;
const COLUMN_TEXT_SIZE: u8 = 255 - TEXT_INDICATOR;

const MAX_COLUMNS: u8 = 16;
pub const MAX_TABLE_DEFINITION_SIZE: usize =
    TEXT_SIZE + MAX_COLUMNS as usize * (TEXT_SIZE + TEXT_SIZE);

#[derive(Debug, Clone, PartialEq)]
pub enum ColumnType {
    Integer,           // i32
    Text { size: u8 }, // max text size is 255 - 13
    Bool,
}

impl ColumnType {
    fn header_size(&self) -> u8 {
        match self {
            ColumnType::Integer => 4,
            ColumnType::Bool => 1,
            ColumnType::Text { size } => TEXT_INDICATOR + *size,
        }
    }

    pub fn byte_size(&self) -> usize {
        match self {
            ColumnType::Integer => 4,
            ColumnType::Bool => 1,
            ColumnType::Text { size } => *size as usize,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Column {
    pub name: String, // max 255 characters
    pub column_type: ColumnType,
}

impl Column {
    pub fn new<S: Into<String>>(name: S, column_type: ColumnType) -> anyhow::Result<Self> {
        let name: String = name.into();
        if name.len() > TEXT_SIZE {
            bail!("column's name too long")
        }
        if let ColumnType::Text { size } = column_type {
            if size > COLUMN_TEXT_SIZE {
                bail!("text column too long")
            }
        }
        Ok(Self { name, column_type })
    }
}

//TODO: prepare constructors, we need to validate sizes of strings
/// 255    + (1)           + (255 + 1)
/// name    columns amount  columns definition (name + type)
#[derive(Debug, Clone, PartialEq, Default)]
pub struct TableDefinition {
    pub name: String, // max 255 characters

    // column's name to its type mapping
    pub columns: Vec<Column>,
}

impl TableDefinition {
    pub fn size(&self) -> usize {
        self.columns.iter().map(|c| c.column_type.byte_size()).sum()
    }
}

impl TryFrom<Vec<u8>> for TableDefinition {
    type Error = anyhow::Error;

    fn try_from(value: Vec<u8>) -> Result<Self, Self::Error> {
        let mut offset: usize = 0;

        let table_name = String::from_utf8(value[offset..TEXT_SIZE].to_vec())?.replace('\0', "");
        offset += TEXT_SIZE;
        let columns_amount = value[offset];
        offset += 1;

        let mut columns = vec![];
        for _ in 0..(columns_amount as usize) {
            let name =
                String::from_utf8(value[offset..offset + TEXT_SIZE].to_vec())?.replace('\0', "");
            offset += TEXT_SIZE;

            let byte = value[offset];

            let row_type = if byte == 1 {
                ColumnType::Bool
            } else if byte == 4 {
                ColumnType::Integer
            } else if byte > TEXT_INDICATOR {
                ColumnType::Text {
                    size: byte - TEXT_INDICATOR,
                }
            } else {
                bail!("invalid row type")
            };
            offset += 1;

            columns.push(Column {
                name,
                column_type: row_type,
            });
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
        name_bytes.append(&mut vec![0u8; TEXT_SIZE - name_bytes.len()]); // fill to 255

        bytes.append(&mut name_bytes);
        bytes.push(val.columns.len() as u8);

        for Column {
            name,
            column_type: row_type,
        } in &val.columns
        {
            let mut name_bytes = name.as_bytes().to_vec();
            name_bytes.append(&mut vec![0u8; TEXT_SIZE - name_bytes.len()]); // fill to 255

            bytes.append(&mut name_bytes);
            bytes.push(row_type.header_size())
        }

        bytes
    }
}

#[cfg(test)]
mod tests {
    use super::{Column, ColumnType, TableDefinition};

    #[test]
    fn test_table_definition() {
        let t = TableDefinition {
            name: "my table lol".to_string(),
            columns: vec![
                Column {
                    name: "column1".to_string(),
                    column_type: ColumnType::Integer,
                },
                Column {
                    name: "column2".to_string(),
                    column_type: ColumnType::Integer,
                },
                Column {
                    name: "column3".to_string(),
                    column_type: ColumnType::Bool,
                },
                Column {
                    name: "column4".to_string(),
                    column_type: ColumnType::Bool,
                },
                Column {
                    name: "column5".to_string(),
                    column_type: ColumnType::Text { size: 20 },
                },
                Column {
                    name: "column6".to_string(),
                    column_type: ColumnType::Text { size: 200 },
                },
            ],
        };
        let bytes: Vec<u8> = t.clone().into();
        let t_parsed = TableDefinition::try_from(bytes).unwrap();
        assert_eq!(t, t_parsed)
    }
}
