extern crate derive_more;
use anyhow::{bail, Context};
use derive_more::{Display, Error};
use std::{any, cmp, path::Path};

use crate::{
    node::{InternalNodeType, Key, Node, NodeType, Pointer},
    pager::{Page, Pager},
};

#[derive(Error, Display, Debug)]
enum BtreeError {
    #[display(fmt = "{} {:?}", operation, key)]
    NotFound { operation: String, key: Vec<u8> },
}

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
            key_size: 0,
            row_size: 0,
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

#[derive(Debug)]
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
            NodeType::Leaf { kvs, next_leaf: _ } => Ok(kvs.len() == (2 * self.b - 1)),
        }
    }

    fn is_node_underflow(&self, node: &Node) -> anyhow::Result<bool> {
        match &node.node_type {
            // A root cannot really be "underflowing" as it can contain less than b-1 keys / pointers.
            NodeType::Internal { children: _, keys } => {
                Ok(keys.len() < self.b - 1 && !node.is_root)
            }
            NodeType::Leaf { kvs, next_leaf: _ } => Ok(kvs.len() < self.b - 1 && !node.is_root),
        }
    }

    fn node(&mut self, page_num: u32) -> anyhow::Result<Node> {
        Node::try_from(
            self.pager
                .get_page(page_num, self.key_size, self.row_size)?,
        )
    }

    fn root(&mut self) -> anyhow::Result<Node> {
        self.node(self.root_page_num)
    }

    /// insert a key value pair possibly splitting nodes along the way.
    pub fn insert(&mut self, kv: KeyValuePair) -> anyhow::Result<()> {
        let mut root: Node = self.root()?;

        if self.is_node_full(&root)? {
            // split the root creating a new root and child nodes along the way.
            let mut new_root = Node::new(
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
            let sibling_page_num = self.pager.get_unused_page_num() + 1;

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
            self.pager
                .write_node(self.root_page_num, new_root.clone())?;

            // continue recursively.
            self.insert_non_full(&mut new_root, self.root_page_num, kv)?;
        } else {
            // continue recursively.
            self.insert_non_full(&mut root, self.root_page_num, kv)?;
        }
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
                self.pager.write_node(node_offset, node.clone())
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
                        .get_page(child_offset.0, self.key_size, self.row_size)?;
                let mut child = Node::try_from(child_page)?;

                if self.is_node_full(&child)? {
                    let sibling_page_num = self.pager.get_unused_page_num();
                    // split will split the child at b leaving the [0, b-1] keys
                    // while moving the set of [b, 2b-1] keys to the sibling.
                    let (median, mut sibling) = child.split(self.b, sibling_page_num)?;
                    self.pager.write_node(child_offset.0, child.clone())?;
                    // Write the newly created sibling to disk.
                    self.pager.write_node(sibling_page_num, sibling.clone())?;
                    // Siblings keys are larger than the splitted child thus need to be inserted
                    // at the next index.
                    children.insert(idx + 1, Pointer(sibling_page_num));
                    keys.insert(idx, median.clone());

                    // Write the parent page to disk.
                    self.pager.write_node(node_offset, node.clone())?;
                    // Continue recursively.
                    if kv.key <= median {
                        self.insert_non_full(&mut child, child_offset.0, kv)
                    } else {
                        self.insert_non_full(&mut sibling, sibling_page_num, kv)
                    }
                } else {
                    // self.pager.write_node(node_offset, node.clone())?;
                    self.insert_non_full(&mut child, child_offset.0, kv)
                }
            }
        }
    }

    /// Searches for a specific key in the BTree.
    pub fn search(&mut self, key: Key) -> anyhow::Result<KeyValuePair> {
        let root = self.root()?;
        self.search_node(root, &key)
    }

    fn find_node(
        &mut self,
        node: Node,
        page_num: u32,
        search: &Key,
    ) -> anyhow::Result<(Node, u32)> {
        match node.node_type {
            NodeType::Internal { children, keys } => {
                let idx = keys.binary_search(search).unwrap_or_else(|x| x);

                // Retrieve child page from disk and deserialize.
                let child_offset = children
                    .get(idx)
                    .context("search_node: could not get child_offset")?;
                let page = self
                    .pager
                    .get_page(child_offset.0, self.key_size, self.row_size)?;
                let child_node = Node::try_from(page)?;
                self.find_node(child_node, child_offset.0, search)
            }
            NodeType::Leaf { kvs, next_leaf } => {
                if let Ok(idx) = kvs.binary_search_by_key(&search, |(key, _)| key) {
                    return Ok((node.clone(), page_num));
                }
                dbg!(String::from_utf8(search.0.clone())?);
                bail!(BtreeError::NotFound {
                    operation: "search_node".to_string(),
                    key: search.0.clone()
                })
            }
        }
    }

    /// Recursively searches a sub tree rooted at node for a key.
    fn search_node(&mut self, node: Node, search: &Key) -> anyhow::Result<KeyValuePair> {
        match node.node_type {
            NodeType::Internal { children, keys } => {
                let idx = keys.binary_search(search).unwrap_or_else(|x| x);

                // Retrieve child page from disk and deserialize.
                let child_offset = children
                    .get(idx)
                    .context("search_node: could not get child_offset")?;
                let page = self
                    .pager
                    .get_page(child_offset.0, self.key_size, self.row_size)?;
                let child_node = Node::try_from(page)?;
                self.search_node(child_node, search)
            }
            NodeType::Leaf { kvs, next_leaf } => {
                if let Ok(idx) = kvs.binary_search_by_key(&search, |(key, _)| key) {
                    let (key, value) = kvs.get(idx).unwrap();
                    return Ok(KeyValuePair {
                        key: key.clone(),
                        value: value.clone(),
                    });
                }
                dbg!(String::from_utf8(search.0.clone())?);
                bail!(BtreeError::NotFound {
                    operation: "search_node".to_string(),
                    key: search.0.clone()
                })
            }
        }
    }

    /// delete deletes a given key from the tree.
    pub fn delete(&mut self, key: Key) -> anyhow::Result<()> {
        dbg!("deleting {}", String::from_utf8(key.0.clone())?);
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
        self.root_page_num = new_root_offset;
        self.delete_key_from_subtree(key, &mut new_root, new_root_offset)?;
        Ok(())
    }

    // https://github.com/solangii/b-plus-tree/blob/master/BPlusTree.h#L148
    pub fn own_delete(&mut self, key: Key) -> anyhow::Result<()> {
        let root = self.root()?;
        let (mut found, found_page) = self.find_node(root, self.root_page_num, &key)?;

        // if let NodeType::Leaf { kvs, next_leaf:_ }

        // find left and right sibling indexes
        let parent = self.node(found.parent.unwrap())?;

        let (left, right) = self.find_left_right_sibling(&found, &key)?;

        if !found.contains(&key) {
            dbg!("leaf does not contain key");
            return Ok(());
        }

        if let NodeType::Leaf { kvs, next_leaf } = &mut found.node_type {
            let key_idx = kvs
                .binary_search_by_key(&key, |(key, _)| key.clone())
                .map_err(|_| {
                    println!("{:?} not found", key);
                    BtreeError::NotFound {
                        operation: "delete_key_from_subtree".to_string(),
                        key: key.0.clone(),
                    }
                })?;
            dbg!(key_idx);
            kvs.remove(key_idx);

            self.pager.write_node(found_page, found.clone())?;
        } else {
            panic!("should not happen")
        }

        if found_page == self.root_page_num {
            return Ok(());
        }

        if (found.num_cells() as usize) < (self.b / 2) {
            if let Some(left) = left {
                let mut left_sibling = self.node(left as u32)?;
                if left_sibling.num_cells() as usize > self.b / 2 {
                    // if data number is enough to use this node
                    match &mut left_sibling.node_type {
                        NodeType::Internal { children, keys } => todo!(),
                        NodeType::Leaf { kvs, next_leaf } => {
                            let last = kvs.pop().context("left sibling does not contain kvs")?;
                            match &mut found.node_type {
                                NodeType::Internal { children, keys } => {
                                    panic!("left sibling if leaf, it should be leaf")
                                }
                                NodeType::Leaf { kvs, next_leaf } => {}
                            }
                        }
                    }
                }
            }
        }

        Ok(())
    }

    fn find_left_right_sibling(
        &mut self,
        node: &Node,
        key: &Key,
    ) -> anyhow::Result<(Option<usize>, Option<usize>)> {
        let parent = self.node(node.parent.unwrap())?;

        let mut left: Option<usize> = None;
        let mut right: Option<usize> = None;
        if let NodeType::Internal { children, keys } = parent.node_type {
            let inx = keys.binary_search(&key).unwrap_or_else(|x| x);
            if inx == 0 {
                right = Some(
                    children
                        .get(inx + 1)
                        .context("could not get right sibling")?
                        .0
                        .try_into()?,
                );
            } else if inx == keys.len() - 1 {
                left = Some(
                    children
                        .get(inx - 1)
                        .context("could not get left sibling")?
                        .0
                        .try_into()?,
                );
            } else {
                right = Some(
                    children
                        .get(inx + 1)
                        .context("could not get right sibling")?
                        .0
                        .try_into()?,
                );
                left = Some(
                    children
                        .get(inx - 1)
                        .context("could not get left sibling")?
                        .0
                        .try_into()?,
                );
            }
        } else {
            panic!("should not happen")
        }
        Ok((left, right))
    }

    // fn own_delete_key_from_subtree(
    //     &mut self,
    //     key: Key,
    //     node: &mut Node,
    //     node_offset: u32,
    // ) -> anyhow::Result<()> {
    //     match &mut node.node_type {
    //         NodeType::Internal { children, keys } => todo!(),
    //         NodeType::Leaf { kvs, next_leaf } => {
    //             // Case 1
    //             let key_idx = kvs
    //                 .binary_search_by_key(&key, |(key, _)| key.clone())
    //                 .map_err(|_| {
    //                     println!("{:?} not found", key);
    //                     BtreeError::NotFound {
    //                         operation: "delete_key_from_subtree".to_string(),
    //                         key: key.0.clone(),
    //                     }
    //                 })?;
    //             dbg!(key_idx);
    //             kvs.remove(key_idx);

    //             self.pager.write_node(node_offset, node.clone())?;
    //             if kvs.len() > 2 * self.b - 1 {
    //                 dbg!("Case 1, returning");
    //                 return Ok(());
    //             }
    //         }
    //     }
    //     Ok(())
    // }

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
                    .map_err(|_| {
                        println!("{:?} not found", key);
                        BtreeError::NotFound {
                            operation: "delete_key_from_subtree".to_string(),
                            key: key.0.clone(),
                        }
                    })?;
                dbg!(key_idx);
                kvs.remove(key_idx);
                // self.pager
                //     .write_page_at_offset(Page::try_from(&node.clone())?, node_offset)?;
                self.pager.write_node(node_offset, node.clone())?;
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
                    .context("delete_key_from_subtree: could not get child_offset")?;
                let child_page =
                    self.pager
                        .get_page(child_offset.0, self.key_size, self.row_size)?;
                let mut child_node = Node::try_from(child_page)?;
                // Fix the parent_offset as the child node is a child of a copied parent
                // in a copy-on-write root to leaf traversal.
                // This is important for the case of a node underflow which might require a leaf to root traversal.
                child_node.parent = Some(node_offset.to_owned());
                let new_child_offset = self.pager.get_unused_page_num();
                self.pager
                    .write_node(new_child_offset, child_node.clone())?;
                // Assign the new pointer in the parent and continue reccoursively.
                children[node_idx] = new_child_offset.to_owned().into();
                self.pager.write_node(node_offset, node.clone())?;
                return self.delete_key_from_subtree(key, &mut child_node, new_child_offset);
            }
        }
        Ok(())
    }

    // fn borrow(&mut self, node: Node, key: &Key) -> anyhow::Result<()> {
    //     let parent: Node = Node::try_from(self.pager.get_page(
    //         node.parent.context("node's parent should be set")?,
    //         self.key_size,
    //         self.row_size,
    //     )?)?;
    //     if let NodeType::Leaf { kvs, next_leaf } = node.node_type {
    //         let sibling = Node::try_from(self.pager.get_page(
    //             next_leaf.context("next_leaf should be set")?.0,
    //             self.key_size,
    //             self.row_size,
    //         )?)?;

    //         let merged = self.merge(node, sibling);
    //     }
    //     // Case 2

    //     Ok(())
    // }

    /// borrow_if_needed checks the node for underflow (following a removal of a key),
    /// if it underflows it is merged with a sibling node, and than called recoursively
    /// up the tree. Since the downward root-to-leaf traversal was done using the copy-on-write
    /// technique we are ensured that any merges will only be reflected in the copied parent in the path.
    fn borrow_if_needed(&mut self, node: Node, key: &Key) -> anyhow::Result<()> {
        if self.is_node_underflow(&node)? {
            // Fetch the sibling from the parent -
            // This could be quicker if we implement sibling pointers.
            let parent_offset = node.parent.context("expected parent offset")?;
            let parent_page = self
                .pager
                .get_page(parent_offset, self.key_size, self.row_size)?;
            let mut parent_node = Node::try_from(parent_page)?;
            // The parent has to be an "internal" node.
            match parent_node.node_type {
                NodeType::Internal {
                    ref mut children,
                    ref mut keys,
                } => {
                    // check if right sibling can spare an item
                    let mut idx = keys.binary_search(key).unwrap_or_else(|x| x);

                    let mutright = self.node(children.get(idx + 1).unwrap().0)?;
                    match &mut right.node_type {
                        NodeType::Internal { children, keys } => todo!(),
                        NodeType::Leaf { kvs, next_leaf } => {
                            if kvs.len() - 1 > self.b / 2 - 1 {
                                let value = kvs.remove(0);
                                
                            }
                        }
                    }

                    // let mut idx = keys.binary_search(key).unwrap_or_else(|x| x);
                    // dbg!(idx);
                    // // The sibling is in idx +- 1 as the above index led
                    // // the downward search to node.
                    // let sibling_idx;
                    // match idx > 0 {
                    //     false => sibling_idx = idx + 1,
                    //     true => sibling_idx = idx - 1,
                    // }
                    // dbg!(sibling_idx);

                    // let sibling_offset = children
                    //     .get(sibling_idx)
                    //     .context("could not get sibling_offset")?;
                    // dbg!(sibling_offset);
                    // let sibling_page =
                    //     self.pager
                    //         .get_page(sibling_offset.0, self.key_size, self.row_size)?;
                    // let sibling = Node::try_from(sibling_page)?;
                    // let merged_node = self.merge(node, sibling)?;
                    // dbg!(&merged_node);
                    // // if merged_node.num_cells() >= (2 * self.b - 1) as u32 {
                    // //     // dbg!("lol");
                    // //     return Ok(());
                    // // }
                    // dbg!(String::from_utf8(key.0.clone())?);
                    // let merged_node_offset = self.pager.get_unused_page_num();
                    // self.pager.write_node(merged_node_offset, merged_node)?;
                    // let merged_node_idx = cmp::min(idx, sibling_idx);
                    // // remove the old nodes.
                    // children.remove(merged_node_idx);
                    // // remove shifts nodes to the left.
                    // children.remove(merged_node_idx);
                    // // if the parent is the root, and there is a single child - the merged node -
                    // // we can safely replace the root with the child.
                    // if parent_node.is_root && children.is_empty() {
                    //     // TODO: write root
                    //     self.root_page_num = merged_node_offset;
                    //     dbg!(self.root_page_num);
                    //     dbg!(merged_node_offset);
                    //     dbg!(&parent_node);
                    //     self.pager.write_node(merged_node_offset, parent_node)?;
                    //     return Ok(());
                    // }
                    // let ks: Vec<String> = keys
                    //     .clone()
                    //     .into_iter()
                    //     .map(|v| String::from_utf8(v.0).unwrap())
                    //     .collect();
                    // dbg!(ks);
                    // dbg!(idx);
                    // // remove the keys that separated the two nodes from each other:
                    // keys.remove(cmp::min(keys.len() - 1, idx));
                    // // write the new node in place.
                    // children.insert(merged_node_idx, merged_node_offset.into());
                    // // write the updated parent back to disk and continue up the tree.
                    // self.pager.write_node(parent_offset, parent_node.clone())?;
                    // dbg!(&parent_node);
                    // return self.borrow_if_needed(parent_node, key);
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
                        self.key_size,
                        self.row_size,
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
                        self.key_size,
                        self.row_size,
                    ))
                } else {
                    bail!("unexpected2")
                }
            }
        }
    }

    /// print_sub_tree is a helper function for recursively printing the nodes rooted at a node given by its offset.
    fn print_sub_tree(&mut self, prefix: String, offset: u32) -> anyhow::Result<()> {
        let curr_prefix = format!("{}|->", prefix);
        let page = self.pager.get_page(offset, self.key_size, self.row_size)?;
        let node = Node::try_from(page)?;
        println!(
            "{}Node at offset: {}, root: {}",
            prefix, offset, node.is_root
        );
        match node.node_type {
            NodeType::Internal { children, keys } => {
                println!(
                    "{}Keys: {:?}",
                    curr_prefix,
                    keys.into_iter()
                        .map(|k| k.0)
                        .map(|v| String::from_utf8(v).unwrap())
                        .collect::<Vec<String>>()
                );
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
                println!(
                    "{}Key value pairs: {:?}",
                    curr_prefix,
                    pairs
                        .into_iter()
                        .map(|(Key(key), data)| (
                            String::from_utf8(key).unwrap().trim().to_string(),
                            String::from_utf8(data).unwrap().trim().to_string()
                        ))
                        .collect::<Vec<(String, String)>>()
                );
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
    use std::{any, fmt::Debug, path::Path};

    use anyhow::Ok;
    use rand::{distributions::Alphanumeric, rngs::StdRng, Rng, SeedableRng};

    use crate::{
        btree::{BTreeBuilder, BtreeError, KeyValuePair},
        constants::LEAF_NODE_SPACE_FOR_CELLS,
        node::Key,
    };

    #[test]
    fn search_works() -> anyhow::Result<()> {
        let mut btree = BTreeBuilder::new()
            .path(Path::new("/tmp/db"))
            .b_parameter(2)
            .key_size(1)
            .row_size(2)
            .build()?;
        btree.insert(KeyValuePair::new("a".to_string(), "s".repeat(2)))?;
        btree.insert(KeyValuePair::new("a".to_string(), "s".repeat(2)))?;
        btree.insert(KeyValuePair::new("a".to_string(), "s".repeat(2)))?;
        btree.insert(KeyValuePair::new("a".to_string(), "s".repeat(2)))?;
        btree.insert(KeyValuePair::new("b".to_string(), "sb".to_string()))?;
        btree.insert(KeyValuePair::new("c".to_string(), "sc".to_string()))?;
        btree.insert(KeyValuePair::new("d".to_string(), "sd".to_string()))?;

        // btree.print()?;
        // btree.insert(KeyValuePair::new("a".repeat(32), "s".repeat(256)))?;
        // btree.insert(KeyValuePair::new("a".repeat(32), "s".repeat(256)))?;
        let key_a = Key("a".as_bytes().to_vec());
        let s = btree.search(key_a.clone())?;
        assert_eq!(s.key, key_a);
        assert_eq!(s.value, "s".repeat(2).as_bytes().to_vec());

        let key_b = Key("b".as_bytes().to_vec());
        let s = btree.search(key_b.clone())?;
        assert_eq!(s.key, key_b);
        assert_eq!(s.value, "sb".as_bytes().to_vec());

        let key_c = Key("c".as_bytes().to_vec());
        let s = btree.search(key_c.clone())?;
        assert_eq!(s.key, key_c);
        assert_eq!(s.value, "sc".as_bytes().to_vec());

        let key_d = Key("d".as_bytes().to_vec());
        let s = btree.search(key_d.clone())?;

        assert_eq!(s.key, key_d);
        assert_eq!(s.value, "sd".as_bytes().to_vec());

        Ok(())
    }

    fn value(value: &str, len: usize) -> String {
        if value.len() < len {
            let rest = " ".repeat(len - value.len());
            let mut new = value.to_string();
            new.push_str(&rest);
            return new;
        }
        value.to_string()
    }

    const B: usize = LEAF_NODE_SPACE_FOR_CELLS / (32 + 256);

    #[test]
    fn multiple_inserts() -> anyhow::Result<()> {
        let mut btree = BTreeBuilder::new()
            .path(Path::new("/tmp/db"))
            .b_parameter(6)
            .key_size(32)
            .row_size(256)
            .build()?;

        let mut checks = vec![];
        let mut deletes = vec![];

        for i in 0..500 {
            let mut r = StdRng::seed_from_u64(i + 2);
            let key: String = r
                .clone()
                .sample_iter(&Alphanumeric)
                .take(32)
                .map(char::from)
                .collect();
            let value: String = r
                .sample_iter(&Alphanumeric)
                .take(256)
                .map(char::from)
                .collect();
            if i % 7 == 0 {
                deletes.push(key.clone());
            }
            if i % 10 == 0 && i % 7 != 0 {
                checks.push((key.clone(), value.clone()));
            }
            if key == *"BQXetLOXEo0BZrZy3HUOCBFBl2XHfRpy" {
                dbg!(i);
            }
            btree.insert(KeyValuePair::new(key, value))?;
        }
        // for key in deletes {
        //     dbg!("delete");
        //     if key == *"zgTBBU95aE8HgsCX4L24mHsRL6s8E20B" {
        //         dbg!("here");
        //     }
        //     if key == *"7g1enWdklQEvXE6e6Qqr4qzNnfDunjX8" {
        //         dbg!("wow");
        //     }
        //     let s_key: Key = key.as_bytes().to_vec().into();
        //     let kv = btree.search(s_key.clone())?;
        //     assert_eq!(kv.key, s_key);

        //     btree.delete(s_key)?;
        // }
        for (key, value) in checks {
            dbg!("check");
            let key: Key = key.as_bytes().to_vec().into();
            let kv = btree.search(key.clone())?;
            assert_eq!(kv.key, key);
            assert_eq!(kv.value, value.as_bytes().to_vec());
        }

        Ok(())
    }

    #[test]
    fn insert_works() -> anyhow::Result<()> {
        let mut btree = BTreeBuilder::new()
            .path(Path::new("/tmp/db"))
            .b_parameter(2)
            .key_size(1)
            .row_size(32)
            .build()?;

        btree.insert(KeyValuePair::new("a".to_string(), value("shalom", 32)))?;
        btree.insert(KeyValuePair::new("b".to_string(), value("hello", 32)))?;
        btree.insert(KeyValuePair::new("c".to_string(), value("marhaba", 32)))?;
        btree.insert(KeyValuePair::new("d".to_string(), value("olah", 32)))?;
        btree.insert(KeyValuePair::new("e".to_string(), value("salam", 32)))?;
        btree.insert(KeyValuePair::new("f".to_string(), value("hallo", 32)))?;
        btree.insert(KeyValuePair::new("g".to_string(), value("Konnichiwa", 32)))?;
        btree.insert(KeyValuePair::new("h".to_string(), value("Nihao", 32)))?;
        btree.insert(KeyValuePair::new("i".to_string(), value("Ciao", 32)))?;

        btree.print()?;
        println!("===============");

        let mut search_string = |key: &str| btree.search(Key(key.as_bytes().to_vec()));

        let mut kv = search_string("a")?;
        assert_eq!(kv.key, "a".into());
        assert_eq!(kv.value, value("shalom", 32).as_bytes().to_vec());

        kv = search_string("b")?;
        assert_eq!(kv.key, "b".into());
        assert_eq!(kv.value, value("hello", 32).as_bytes().to_vec());

        kv = search_string("c")?;
        assert_eq!(kv.key, "c".into());
        assert_eq!(kv.value, value("marhaba", 32).as_bytes().to_vec());

        kv = search_string("d")?;
        assert_eq!(kv.key, "d".into());
        assert_eq!(kv.value, value("olah", 32).as_bytes().to_vec());

        kv = search_string("e")?;
        assert_eq!(kv.key, "e".into());
        assert_eq!(kv.value, value("salam", 32).as_bytes().to_vec());

        kv = search_string("f")?;
        assert_eq!(kv.key, "f".into());
        assert_eq!(kv.value, value("hallo", 32).as_bytes().to_vec());

        kv = search_string("g")?;
        assert_eq!(kv.key, "g".into());
        assert_eq!(kv.value, value("Konnichiwa", 32).as_bytes().to_vec());

        kv = search_string("h")?;
        assert_eq!(kv.key, "h".into());
        assert_eq!(kv.value, value("Nihao", 32).as_bytes().to_vec());

        kv = search_string("i")?;
        assert_eq!(kv.key, "i".into());
        assert_eq!(kv.value, value("Ciao", 32).as_bytes().to_vec());
        Ok(())
        // btree.delete("g".into())?;
        // btree.print()?;
        // btree.delete("h".into())?;
        // btree.print()?;
        // btree.delete("a".into())?;
        // btree.print()?;
        // btree.delete("b".into())?;
        // btree.print()?;
        // btree.delete("c".into())?;
        // btree.print()?;
        // btree.delete("d".into())?;
        // btree.print()?;
        // btree.delete("e".into())?;

        // let mut search_string =
        //     |key: &str| -> anyhow::Result<_> { btree.search(Key(key.as_bytes().to_vec())) };

        // check_error_not_found(search_string("a"), "a".as_bytes().to_vec());

        // // kv = search_string("b")?;
        // // assert_eq!(kv.key, "b".into());
        // // assert_eq!(kv.value, value("hello", 32).as_bytes().to_vec());

        // // kv = search_string("c")?;
        // // assert_eq!(kv.key, "c".into());
        // // assert_eq!(kv.value, value("marhaba", 32).as_bytes().to_vec());

        // // kv = search_string("d")?;
        // // assert_eq!(kv.key, "d".into());
        // // assert_eq!(kv.value, value("olah", 32).as_bytes().to_vec());

        // // kv = search_string("e")?;
        // // assert_eq!(kv.key, "e".into());
        // // assert_eq!(kv.value, value("salam", 32).as_bytes().to_vec());

        // kv = search_string("f")?;
        // assert_eq!(kv.key, "f".into());
        // assert_eq!(kv.value, value("hallo", 32).as_bytes().to_vec());

        // check_error_not_found(search_string("g"), "g".as_bytes().to_vec());
        // check_error_not_found(search_string("h"), "h".as_bytes().to_vec());

        // kv = search_string("i")?;
        // assert_eq!(kv.key, "i".into());
        // assert_eq!(kv.value, value("Ciao", 32).as_bytes().to_vec());

        // Ok(())
    }

    fn check_error_not_found<T: Debug>(r: anyhow::Result<T>, wanted_key: Vec<u8>) {
        match r.unwrap_err().downcast_ref::<BtreeError>() {
            Some(e) => match e {
                BtreeError::NotFound { operation: _, key } => (assert_eq!(key, &wanted_key)),
                _ => {
                    panic!("should be not found")
                }
            },
            None => panic!("error should be not found"),
        }
    }
}
