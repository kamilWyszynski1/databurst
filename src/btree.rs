use std::{cmp, path::Path};

use anyhow::{bail, Context};

use crate::{
    node::{Key, Node, NodeType, Pointer},
    pager::{Page, Pager},
};

/// BTree struct represents an on-disk B+tree.
/// Each node is persisted in the table file, the leaf nodes contain the values.
pub struct BTree {
    pager: Pager,
    b: usize,

    pub root_page_num: u32,

    is_index: bool,

    key_size: usize,
    row_size: usize,
}

/// BtreeBuilder is a Builder for the BTree struct.
pub struct BTreeBuilder {
    /// Path to the tree file.
    path: &'static Path,
    /// The BTree parameter, an inner node contains no more than 2*b-1 keys and no less than b-1 keys
    /// and no more than 2*b children and no less than b children.
    b: usize,

    key_size: usize,
    row_size: usize,
}

impl BTreeBuilder {
    pub fn new() -> BTreeBuilder {
        BTreeBuilder {
            path: Path::new(""),
            b: 0,
            ..Default::default()
        }
    }

    pub fn path(mut self, path: &'static Path) -> BTreeBuilder {
        self.path = path;
        self
    }

    pub fn b_parameter(mut self, b: usize) -> BTreeBuilder {
        self.b = b;
        self
    }

    pub fn key_size(mut self, key_size: usize) -> BTreeBuilder {
        self.key_size = key_size;
        self
    }

    pub fn row_size(mut self, row_size: usize) -> BTreeBuilder {
        self.row_size = row_size;
        self
    }

    pub fn build(&self) -> anyhow::Result<BTree> {
        if self.path.to_string_lossy() == "" {
            bail!("path cannot be empty");
        }
        if self.b == 0 {
            bail!("b cannot be empty");
        }

        let mut pager = Pager::new(self.path)?;
        let root = Node::new(
            NodeType::Leaf {
                kvs: vec![],
                next_leaf: None,
            },
            true,
            false,
            None,
            self.key_size,
            self.row_size,
        );
        let root_offset = pager.get_unused_page_num();
        pager.write_node(root_offset, root)?;
        let parent_directory = self.path.parent().unwrap_or_else(|| Path::new("/tmp"));

        Ok(BTree {
            is_index: false,
            key_size: self.key_size,
            row_size: self.row_size,
            root_page_num: root_offset,
            pager,
            b: self.b,
        })
    }
}

impl Default for BTreeBuilder {
    // A default BTreeBuilder provides a builder with:
    // - b parameter set to 200
    // - path set to '/tmp/db'.
    fn default() -> Self {
        BTreeBuilder::new()
            .b_parameter(200)
            .path(Path::new("/tmp/db"))
    }
}

struct KeyValuePair {
    key: Key,
    value: Vec<u8>,
}

impl KeyValuePair {
    pub fn new(key: String, value: String) -> Self {
        Self {
            key: Key(key.as_bytes().to_vec()),
            value: value.as_bytes().to_vec(),
        }
    }
}

impl Into<(Key, Vec<u8>)> for KeyValuePair {
    fn into(self) -> (Key, Vec<u8>) {
        (self.key, self.value)
    }
}

impl BTree {
    fn is_node_full(&self, node: &Node) -> anyhow::Result<bool> {
        match &node.node_type {
            NodeType::Internal { children: _, keys } => Ok(keys.len() == (2 * self.b - 1)),
            NodeType::Leaf { kvs, next_leaf } => Ok(kvs.len() == (2 * self.b - 1)),
        }
    }

    fn is_node_underflow(&self, node: &Node) -> anyhow::Result<bool> {
        match &node.node_type {
            // A root cannot really be "underflowing" as it can contain less than b-1 keys / pointers.
            NodeType::Internal { children: _, keys } => {
                Ok(keys.len() < self.b - 1 && !node.is_root)
            }
            NodeType::Leaf { kvs, next_leaf } => Ok(kvs.len() < self.b - 1 && !node.is_root),
        }
    }

    fn root(&self) -> anyhow::Result<Node> {
        let root_page = self
            .pager
            .get_page(self.root_page_num, self.key_size, self.row_size)?;
        Node::try_from(root_page)
    }

    /// insert a key value pair possibly splitting nodes along the way.
    pub fn insert(&mut self, kv: KeyValuePair) -> anyhow::Result<()> {
        let mut new_root: Node;
        let mut root = self.root()?;
        if self.is_node_full(&root)? {
            // split the root creating a new root and child nodes along the way.
            new_root = Node::new(
                NodeType::Internal {
                    children: Vec::new(),
                    keys: Vec::new(),
                },
                true,
                self.is_index,
                None,
                self.key_size,
                self.row_size,
            );

            // set the old roots parent to the new root.
            root.parent = Some(self.root_page_num);
            root.is_root = false;

            // generete new page numbers for splited nodes
            let old_root_page_num = self.pager.get_unused_page_num();
            let sibling_page_num = self.pager.get_unused_page_num();

            // split the old root.
            let (median, sibling) = root.split(self.b, sibling_page_num)?;
            // write the old root with its new data to disk in a *new* location.
            self.pager.write_node(old_root_page_num, root)?;
            // write the newly created sibling to disk.
            self.pager.write_node(sibling_page_num, sibling)?;

            // update the new root with its children and key.
            new_root.node_type = NodeType::Internal {
                children: vec![Pointer(old_root_page_num), Pointer(sibling_page_num)],
                keys: vec![median],
            };
            // write the new_root to disk.
            self.pager.write_node(self.root_page_num, new_root)?;
        }
        // continue recursively.
        self.insert_non_full(&mut new_root, self.root_page_num, kv)?;
        Ok(())
    }

    /// insert_non_full (recursively) finds a node rooted at a given non-full node.
    /// to insert a given key-value pair. Here we assume the node is
    /// already a copy of an existing node in a copy-on-write root to node traversal.
    fn insert_non_full(
        &mut self,
        node: &mut Node,
        node_offset: u32,
        kv: KeyValuePair,
    ) -> anyhow::Result<()> {
        match &mut node.node_type {
            NodeType::Leaf {
                ref mut kvs,
                next_leaf: _,
            } => {
                let idx = kvs
                    .iter()
                    .map(|(k, _)| k)
                    .collect::<Vec<&Key>>()
                    .binary_search(&&kv.key)
                    .unwrap_or_else(|x| x);
                kvs.insert(idx, kv.into());
                self.pager.write_node(node_offset, *node)
            }
            NodeType::Internal {
                ref mut children,
                ref mut keys,
            } => {
                let idx = keys.binary_search(&kv.key).unwrap_or_else(|x| x);
                let child_offset = children
                    .get(idx)
                    .context("could not get child_offset")?
                    .clone();
                let child_page =
                    self.pager
                        .get_page(child_offset.0, node.key_size, node.row_size)?;
                let mut child = Node::try_from(child_page)?;

                if self.is_node_full(&child)? {
                    let sibling_page_num = self.pager.get_unused_page_num();
                    // split will split the child at b leaving the [0, b-1] keys
                    // while moving the set of [b, 2b-1] keys to the sibling.
                    let (median, mut sibling) = child.split(self.b, sibling_page_num)?;
                    self.pager.write_node(child_offset.0, child)?;
                    // Write the newly created sibling to disk.
                    self.pager.write_node(sibling_page_num, sibling)?;
                    // Siblings keys are larger than the splitted child thus need to be inserted
                    // at the next index.
                    children.insert(idx + 1, Pointer(sibling_page_num));
                    keys.insert(idx, median.clone());

                    // Write the parent page to disk.
                    self.pager.write_node(node_offset, *node)?;
                    // Continue recursively.
                    if kv.key <= median {
                        self.insert_non_full(&mut child, child_offset.0, kv)
                    } else {
                        self.insert_non_full(&mut sibling, sibling_page_num, kv)
                    }
                } else {
                    self.pager.write_node(node_offset, *node)?;
                    self.insert_non_full(&mut child, child_offset.0, kv)
                }
            }
        }
    }

    /// search searches for a specific key in the BTree.
    pub fn search(&mut self, key: Key) -> anyhow::Result<KeyValuePair> {
        self.search_node(self.root()?, &key)
    }

    /// search_node recursively searches a sub tree rooted at node for a key.
    fn search_node(&mut self, node: Node, search: &Key) -> anyhow::Result<KeyValuePair> {
        match node.node_type {
            NodeType::Internal { children, keys } => {
                let idx = keys.binary_search(search).unwrap_or_else(|x| x);
                // Retrieve child page from disk and deserialize.
                let child_offset = children.get(idx).context("could not get child_offset")?;
                let page = self
                    .pager
                    .get_page(child_offset.0, node.key_size, node.row_size)?;
                let child_node = Node::try_from(page)?;
                self.search_node(child_node, search)
            }
            NodeType::Leaf { kvs, next_leaf } => {
                if let Ok(idx) = kvs.binary_search_by_key(&search, |(key, _)| key) {
                    let (key, value) = kvs[idx];
                    return Ok(KeyValuePair { key, value });
                }
                bail!("Not found")
            }
        }
    }

    /// delete deletes a given key from the tree.
    pub fn delete(&mut self, key: Key) -> anyhow::Result<()> {
        // let root_offset = self.wal.get_root()?;
        // let root_page = self.pager.get_page(&root_offset)?;
        // // Shadow the new root and rewrite it.
        // let mut new_root = Node::try_from(root_page)?;
        // let new_root_page = Page::try_from(&new_root)?;
        // let new_root_offset = self.pager.write_page(new_root_page)?;
        // self.delete_key_from_subtree(key, &mut new_root, &new_root_offset)?;
        // self.wal.set_root(new_root_offset)

        let root = self.root()?;
        let mut new_root = root.clone();
        let new_root_offset = self.pager.get_unused_page_num();
        self.pager.write_node(new_root_offset, root)?;
        self.delete_key_from_subtree(key, &mut new_root, new_root_offset)?;
        self.root_page_num = new_root_offset;
        Ok(())
    }

    /// delete key from subtree recursively traverses a tree rooted at a node in certain offset
    /// until it finds the given key and delete the key-value pair. Here we assume the node is
    /// already a copy of an existing node in a copy-on-write root to node traversal.
    fn delete_key_from_subtree(
        &mut self,
        key: Key,
        node: &mut Node,
        node_offset: u32,
    ) -> anyhow::Result<()> {
        match &mut node.node_type {
            NodeType::Leaf { kvs, next_leaf } => {
                let key_idx = kvs
                    .binary_search_by_key(&key, |(key, _)| key.clone())
                    .unwrap();
                kvs.remove(key_idx);
                // self.pager
                //     .write_page_at_offset(Page::try_from(&*node)?, node_offset)?;
                self.pager.write_node(node_offset, *node)?;
                // Check for underflow - if it occures,
                // we need to merge with a sibling.
                // this can only occur if node is not the root (as it cannot "underflow").
                // continue recoursively up the tree.
                self.borrow_if_needed(node.to_owned(), &key)?;
            }
            NodeType::Internal { children, keys } => {
                let node_idx = keys.binary_search(&key).unwrap_or_else(|x| x);
                // Retrieve child page from disk and deserialize,
                // copy over the child page and continue recursively.
                let child_offset = children
                    .get(node_idx)
                    .context("could not get child_offset")?;
                let child_page =
                    self.pager
                        .get_page(child_offset.0, node.key_size, node.row_size)?;
                let mut child_node = Node::try_from(child_page)?;
                // Fix the parent_offset as the child node is a child of a copied parent
                // in a copy-on-write root to leaf traversal.
                // This is important for the case of a node underflow which might require a leaf to root traversal.
                child_node.parent = Some(node_offset.to_owned());
                let new_child_offset = self.pager.get_unused_page_num();
                self.pager.write_node(new_child_offset, child_node)?;
                // Assign the new pointer in the parent and continue reccoursively.
                children[node_idx] = new_child_offset.to_owned().into();
                self.pager.write_node(node_offset, *node)?;
                return self.delete_key_from_subtree(key, &mut child_node, new_child_offset);
            }
        }
        Ok(())
    }

    /// borrow_if_needed checks the node for underflow (following a removal of a key),
    /// if it underflows it is merged with a sibling node, and than called recoursively
    /// up the tree. Since the downward root-to-leaf traversal was done using the copy-on-write
    /// technique we are ensured that any merges will only be reflected in the copied parent in the path.
    fn borrow_if_needed(&mut self, node: Node, key: &Key) -> anyhow::Result<()> {
        if self.is_node_underflow(&node)? {
            // Fetch the sibling from the parent -
            // This could be quicker if we implement sibling pointers.
            let parent_offset = node.parent.clone().context("expected parent offset")?;
            let parent_page = self
                .pager
                .get_page(parent_offset, node.key_size, node.row_size)?;
            let mut parent_node = Node::try_from(parent_page)?;
            // The parent has to be an "internal" node.
            match parent_node.node_type {
                NodeType::Internal {
                    ref mut children,
                    ref mut keys,
                } => {
                    let idx = keys.binary_search(key).unwrap_or_else(|x| x);
                    // The sibling is in idx +- 1 as the above index led
                    // the downward search to node.
                    let sibling_idx;
                    match idx > 0 {
                        false => sibling_idx = idx + 1,
                        true => sibling_idx = idx - 1,
                    }

                    let sibling_offset = children
                        .get(sibling_idx)
                        .context("could not get sibling_offset")?;
                    let sibling_page =
                        self.pager
                            .get_page(sibling_offset.0, node.key_size, node.row_size)?;
                    let sibling = Node::try_from(sibling_page)?;
                    let merged_node = self.merge(node, sibling)?;
                    let merged_node_offset = self.pager.get_unused_page_num();
                    self.pager.write_node(merged_node_offset, merged_node)?;
                    let merged_node_idx = cmp::min(idx, sibling_idx);
                    // remove the old nodes.
                    children.remove(merged_node_idx);
                    // remove shifts nodes to the left.
                    children.remove(merged_node_idx);
                    // if the parent is the root, and there is a single child - the merged node -
                    // we can safely replace the root with the child.
                    if parent_node.is_root && children.is_empty() {
                        self.root_page_num = merged_node_offset;
                        return Ok(());
                    }
                    // remove the keys that separated the two nodes from each other:
                    keys.remove(idx);
                    // write the new node in place.
                    children.insert(merged_node_idx, merged_node_offset.into());
                    // write the updated parent back to disk and continue up the tree.
                    self.pager.write_node(parent_offset, parent_node)?;
                    return self.borrow_if_needed(parent_node, key);
                }
                NodeType::Leaf { kvs, next_leaf } => bail!("could not borrow in leaf node"),
            }
        }
        Ok(())
    }

    // merges two *sibling* nodes, it assumes the following:
    // 1. the two nodes are of the same type.
    // 2. the two nodes do not accumulate to an overflow,
    // i.e. |first.keys| + |second.keys| <= [2*(b-1) for keys or 2*b for offsets].
    fn merge(&self, first: Node, second: Node) -> anyhow::Result<Node> {
        match first.node_type {
            NodeType::Leaf { kvs, next_leaf } => {
                if let NodeType::Leaf {
                    kvs: second_kvs,
                    next_leaf: second_next_leaf,
                } = second.node_type
                {
                    let merged_pairs: Vec<(Key, Vec<u8>)> =
                        kvs.into_iter().chain(second_kvs.into_iter()).collect();
                    let node_type = NodeType::Leaf {
                        kvs: merged_pairs,
                        next_leaf: second_next_leaf,
                    };
                    Ok(Node::new(
                        node_type,
                        first.is_root,
                        first.is_index,
                        first.parent,
                        first.key_size,
                        first.row_size,
                    ))
                } else {
                    bail!("unexpected1")
                }
            }
            NodeType::Internal {
                children: first_offsets,
                keys: first_keys,
            } => {
                if let NodeType::Internal {
                    children: second_offsets,
                    keys: second_keys,
                } = second.node_type
                {
                    let merged_keys: Vec<Key> = first_keys
                        .into_iter()
                        .chain(second_keys.into_iter())
                        .collect();
                    let merged_offsets: Vec<Pointer> = first_offsets
                        .into_iter()
                        .chain(second_offsets.into_iter())
                        .collect();
                    let node_type = NodeType::Internal {
                        children: merged_offsets,
                        keys: merged_keys,
                    };
                    Ok(Node::new(
                        node_type,
                        first.is_root,
                        first.is_index,
                        first.parent,
                        first.key_size,
                        first.row_size,
                    ))
                } else {
                    bail!("unexpected2")
                }
            }
        }
    }

    /// print_sub_tree is a helper function for recursively printing the nodes rooted at a node given by its offset.
    fn print_sub_tree(&mut self, prefix: String, offset: u32) -> anyhow::Result<()> {
        let root = self.root()?;
        println!("{}Node at offset: {}", prefix, 0);
        let curr_prefix = format!("{}|->", prefix);
        let page = self.pager.get_page(offset, root.key_size, root.row_size)?;
        let node = Node::try_from(page)?;
        match node.node_type {
            NodeType::Internal { children, keys } => {
                println!("{}Keys: {:?}", curr_prefix, keys);
                println!("{}Children: {:?}", curr_prefix, children);
                let child_prefix = format!("{}   |  ", prefix);
                for child_offset in children {
                    self.print_sub_tree(child_prefix.clone(), child_offset.0)?;
                }
                Ok(())
            }
            NodeType::Leaf {
                kvs: pairs,
                next_leaf,
            } => {
                println!("{}Key value pairs: {:?}", curr_prefix, pairs);
                Ok(())
            }
        }
    }

    /// print is a helper for recursively printing the tree.
    pub fn print(&mut self) -> anyhow::Result<()> {
        println!();
        self.print_sub_tree("".to_string(), self.root_page_num)
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::{
        btree::{BTreeBuilder, KeyValuePair},
        node::Key,
    };

    #[test]
    fn search_works() -> anyhow::Result<()> {
        let mut btree = BTreeBuilder::new()
            .path(Path::new("/tmp/db"))
            .b_parameter(2)
            .key_size(32)
            .row_size(256)
            .build()?;
        btree.insert(KeyValuePair::new("a".to_string(), "shalom".to_string()))?;
        btree.insert(KeyValuePair::new("b".to_string(), "hello".to_string()))?;
        btree.insert(KeyValuePair::new("c".to_string(), "marhaba".to_string()))?;

        let mut kv = btree.search("b".as_bytes().to_vec().into())?;
        assert_eq!(kv.key, Key("b".as_bytes().to_vec()));
        assert_eq!(kv.value, "hello".as_bytes().to_vec());

        let mut kv = btree.search("c".as_bytes().to_vec().into())?;
        assert_eq!(kv.key, Key("c".as_bytes().to_vec()));
        assert_eq!(kv.value, "hello".as_bytes().to_vec());

        Ok(())
    }

    // #[test]
    // fn insert_works() -> anyhow::Result<()> {
    //     use crate::btree::BTreeBuilder;
    //     use crate::node_type::KeyValuePair;
    //     use std::path::Path;

    //     let mut btree = BTreeBuilder::new()
    //         .path(Path::new("/tmp/db"))
    //         .b_parameter(2)
    //         .build()?;
    //     btree.insert(KeyValuePair::new("a".to_string(), "shalom".to_string()))?;
    //     btree.insert(KeyValuePair::new("b".to_string(), "hello".to_string()))?;
    //     btree.insert(KeyValuePair::new("c".to_string(), "marhaba".to_string()))?;
    //     btree.insert(KeyValuePair::new("d".to_string(), "olah".to_string()))?;
    //     btree.insert(KeyValuePair::new("e".to_string(), "salam".to_string()))?;
    //     btree.insert(KeyValuePair::new("f".to_string(), "hallo".to_string()))?;
    //     btree.insert(KeyValuePair::new("g".to_string(), "Konnichiwa".to_string()))?;
    //     btree.insert(KeyValuePair::new("h".to_string(), "Ni hao".to_string()))?;
    //     btree.insert(KeyValuePair::new("i".to_string(), "Ciao".to_string()))?;

    //     let mut kv = btree.search("a".to_string())?;
    //     assert_eq!(kv.key, "a");
    //     assert_eq!(kv.value, "shalom");

    //     kv = btree.search("b".to_string())?;
    //     assert_eq!(kv.key, "b");
    //     assert_eq!(kv.value, "hello");

    //     kv = btree.search("c".to_string())?;
    //     assert_eq!(kv.key, "c");
    //     assert_eq!(kv.value, "marhaba");

    //     kv = btree.search("d".to_string())?;
    //     assert_eq!(kv.key, "d");
    //     assert_eq!(kv.value, "olah");

    //     kv = btree.search("e".to_string())?;
    //     assert_eq!(kv.key, "e");
    //     assert_eq!(kv.value, "salam");

    //     kv = btree.search("f".to_string())?;
    //     assert_eq!(kv.key, "f");
    //     assert_eq!(kv.value, "hallo");

    //     kv = btree.search("g".to_string())?;
    //     assert_eq!(kv.key, "g");
    //     assert_eq!(kv.value, "Konnichiwa");

    //     kv = btree.search("h".to_string())?;
    //     assert_eq!(kv.key, "h");
    //     assert_eq!(kv.value, "Ni hao");

    //     kv = btree.search("i".to_string())?;
    //     assert_eq!(kv.key, "i");
    //     assert_eq!(kv.value, "Ciao");
    //     Ok(())
    // }

    // #[test]
    // fn delete_works() -> anyhow::Result<()> {
    //     use crate::btree::BTreeBuilder;
    //     use crate::error::Error;
    //     use crate::node_type::{Key, KeyValuePair};
    //     use std::path::Path;

    //     let mut btree = BTreeBuilder::new()
    //         .path(Path::new("/tmp/db"))
    //         .b_parameter(2)
    //         .build()?;
    //     btree.insert(KeyValuePair::new("d".to_string(), "olah".to_string()))?;
    //     btree.insert(KeyValuePair::new("e".to_string(), "salam".to_string()))?;
    //     btree.insert(KeyValuePair::new("f".to_string(), "hallo".to_string()))?;
    //     btree.insert(KeyValuePair::new("a".to_string(), "shalom".to_string()))?;
    //     btree.insert(KeyValuePair::new("b".to_string(), "hello".to_string()))?;
    //     btree.insert(KeyValuePair::new("c".to_string(), "marhaba".to_string()))?;

    //     let mut kv = btree.search("c".to_string())?;
    //     assert_eq!(kv.key, "c");
    //     assert_eq!(kv.value, "marhaba");

    //     btree.delete(Key("c".to_string()))?;
    //     let mut res = btree.search("c".to_string());
    //     assert!(matches!(res, Err(Error::KeyNotFound)));

    //     kv = btree.search("d".to_string())?;
    //     assert_eq!(kv.key, "d");
    //     assert_eq!(kv.value, "olah");

    //     btree.delete(Key("d".to_string()))?;
    //     res = btree.search("d".to_string());
    //     assert!(matches!(res, Err(Error::KeyNotFound)));

    //     btree.delete(Key("e".to_string()))?;
    //     res = btree.search("e".to_string());
    //     assert!(matches!(res, Err(Error::KeyNotFound)));

    //     btree.delete(Key("f".to_string()))?;
    //     res = btree.search("f".to_string());
    //     assert!(matches!(res, Err(Error::KeyNotFound)));

    //     Ok(())
    // }
}
