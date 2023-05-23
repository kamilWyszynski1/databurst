use crate::row::TableDefinition;

#[derive(Debug, Clone)]
pub struct WhereStmt {
    pub column: String,
    pub value: Vec<u8>,
}

impl WhereStmt {
    pub fn get_cmp(
        mut self,
        td: &TableDefinition,
    ) -> anyhow::Result<Box<dyn Fn(&Vec<u8>) -> bool>> {
        let (from, to) = td.column_byte_range(&self.column)?;

        self.value
            .append(&mut vec![0u8; to - from - self.value.len()]);

        Ok(Box::new(move |v: &Vec<u8>| -> bool {
            let part = v[from..to].to_vec();
            part == self.value
        }))
    }
}
