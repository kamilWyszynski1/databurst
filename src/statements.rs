use anyhow::bail;

use crate::row::TableDefinition;

pub struct WhereStmt {
    pub column: String,
    pub value: Vec<u8>,
}

impl WhereStmt {
    pub fn get_cmp(
        mut self,
        td: &TableDefinition,
    ) -> anyhow::Result<Box<dyn Fn(&Vec<u8>) -> bool>> {
        let mut offset = 0;
        let mut size = 0;
        let mut found = false;

        for c in &td.columns {
            size = c.column_type.byte_size();
            if c.name == self.column {
                found = true;
                break;
            }
            offset += c.column_type.byte_size();
        }

        if !found {
            bail!(
                "invalid WhereStmt, could not find '{}' column in TableDefinition",
                self.column
            )
        }

        self.value.append(&mut vec![0u8; size - self.value.len()]);

        Ok(Box::new(move |v: &Vec<u8>| -> bool {
            let part = v[offset..offset + size].to_vec();
            part == self.value
        }))
    }
}
