mod node;

use crossbeam_epoch::Guard;
use node::*;
use std::{marker::PhantomData, mem::ManuallyDrop};

pub struct Tree<V> {
    root: NodePtr,
    _phantom: PhantomData<V>,
}

impl<V> Tree<V> {
    pub fn new() -> Tree<V> {
        Tree {
            root: Node256::alloc(),
            _phantom: PhantomData,
        }
    }

    pub fn get<'a, 'g>(&'a self, key: &[u8], _guard: &'g Guard) -> Option<&'g V> {
        restart_when_needed(|| unsafe {
            let mut node = self.root;
            let mut parent_node;
            let mut version = node.read_lock()?;
            let mut level = 0;
            let mut optimistic_prefix_match = false;
            loop {
                match node.check_prefix(key, level) {
                    CheckPrefixResult::NoMatch => {
                        node.read_unlock(version)?;
                        return Ok(None);
                    }
                    CheckPrefixResult::Match {
                        optimistic,
                        next_level,
                    } => {
                        if key.len() <= next_level {
                            return Ok(None);
                        }

                        if optimistic {
                            optimistic_prefix_match = true;
                        }
                        level = next_level;
                        parent_node = node;
                        node = parent_node.get_child(key[level]);
                        parent_node.check(version)?;

                        if node.is_null() {
                            return Ok(None);
                        }
                        if node.is_leaf() {
                            parent_node.read_unlock(version)?;
                            let entry = node.get_leaf();
                            if level < key.len() - 1 || optimistic_prefix_match {
                                if entry.key() != key {
                                    return Ok(None);
                                }
                            }
                            return Ok(Some(&*entry.value_mut()));
                        }
                        level += 1;
                    }
                }
                let new_version = node.read_lock()?;
                parent_node.read_unlock(version)?;
                version = new_version;
            }
        })
    }

    pub fn insert(&self, key: &[u8], value: V, guard: &Guard) {
        let mut value = ManuallyDrop::new(value);

        // restart begin
        restart_when_needed(|| unsafe {
            let mut node = NodePtr::null();
            let mut next_node = self.root;
            let mut parent_node;
            let mut parent_key;
            let mut node_key = 0u8;
            let mut parent_version = 0u64;
            let mut level = 0usize;

            loop {
                parent_node = node;
                parent_key = node_key;
                node = next_node;
                let version = node.read_lock()?;

                match node.check_prefix_pessimistic(key, level)? {
                    CheckPrefixPessimisticResult::NoMatch {
                        next_level,
                        non_matching_key,
                        remaining_prefix,
                    } => {
                        parent_node.upgrade_to_write_lock(parent_version)?;
                        if let Err(restart) = node.upgrade_to_write_lock(version) {
                            parent_node.write_unlock();
                            return Err(restart);
                        }
                        let new_node =
                            Node4::alloc_with_prefix(node.prefix_ptr(), next_level - level);

                        Node4::insert(
                            new_node,
                            key[next_level],
                            EntryPtr::alloc(key, ManuallyDrop::take(&mut value)).into(),
                        );
                        Node4::insert(new_node, non_matching_key, node);

                        parent_node.change(parent_key, new_node);
                        parent_node.write_unlock();

                        node.set_prefix(
                            remaining_prefix.as_ptr(),
                            node.prefix_len() - ((next_level - level) + 1),
                        );
                        node.write_unlock();
                        return Ok(());
                    }
                    CheckPrefixPessimisticResult::Match { next_level } => {
                        level = next_level;
                    }
                }
                node_key = key[level];
                next_node = node.get_child(node_key);
                node.check(version)?;

                if next_node.is_null() {
                    node.insert_and_unlock::<V>(
                        version,
                        parent_node,
                        parent_version,
                        parent_key,
                        node_key,
                        EntryPtr::alloc(key, ManuallyDrop::take(&mut value)).into(),
                        &guard,
                    )?;
                    return Ok(());
                }

                if !parent_node.is_null() {
                    parent_node.read_unlock(parent_version)?;
                }

                if next_node.is_leaf() {
                    node.upgrade_to_write_lock(version)?;

                    let leaf = next_node.get_leaf();
                    let leaf_key = leaf.key();

                    level += 1;
                    let mut prefix_len = 0;
                    let mut index;
                    loop {
                        index = level + prefix_len;
                        if index < key.len()
                            && index < leaf_key.len()
                            && key[index] == leaf_key[index]
                        {
                            prefix_len += 1;
                        } else {
                            break;
                        }
                    }

                    // key == leaf_key
                    if key.len() == leaf_key.len() && index == key.len() {
                        *leaf.value_mut() = ManuallyDrop::take(&mut value);
                    } else {
                        let new_node =
                            Node4::alloc_with_prefix(key.as_ptr().wrapping_add(level), prefix_len);
                        Node4::insert(
                            new_node,
                            key[index],
                            EntryPtr::alloc(key, ManuallyDrop::take(&mut value)).into(),
                        );
                        Node4::insert(new_node, leaf_key[index], next_node);
                        node.change(key[level - 1], new_node);
                    }
                    node.write_unlock();
                    return Ok(());
                }
                level += 1;
                parent_version = version;
            }
        });
    }

    pub fn remove(&self, key: &[u8], guard: &Guard) {
        restart_when_needed(|| unsafe {
            let mut node = NodePtr::null();
            let mut next_node = self.root;
            let mut parent_node;
            let mut parent_key;
            let mut node_key = 0u8;
            let mut parent_version = 0u64;
            let mut level = 0usize;

            loop {
                parent_node = node;
                parent_key = node_key;
                node = next_node;
                let version = node.read_lock()?;

                match node.check_prefix(key, level) {
                    CheckPrefixResult::NoMatch => {
                        node.read_unlock(version)?;
                        return Ok(());
                    }
                    CheckPrefixResult::Match { next_level, .. } => {
                        level = next_level;
                        node_key = key[level];
                        next_node = node.get_child(node_key);

                        node.check(version)?;

                        if next_node.is_null() {
                            node.read_unlock(version)?;
                            return Ok(());
                        }

                        if next_node.is_leaf() {
                            let next_node = next_node.get_leaf();
                            if next_node.key() == key {
                                next_node.dealloc::<V>();
                            } else {
                                return Ok(());
                            }

                            let child_count = node.child_count();
                            assert!(parent_node.is_null() || child_count != 1);
                            if child_count == 2 && !parent_node.is_null() {
                                parent_node.upgrade_to_write_lock(parent_version)?;
                                if let Err(restart) = node.upgrade_to_write_lock(version) {
                                    parent_node.write_unlock();
                                    return Err(restart);
                                }

                                let (second_node, second_node_key) =
                                    node.get_second_child(node_key);
                                if second_node.is_leaf() {
                                    parent_node.change(parent_key, second_node);

                                    parent_node.write_unlock();
                                    node.write_unlock_obsolete();
                                    guard.defer(move || {
                                        node.dealloc();
                                    });
                                } else {
                                    if let Err(restart) = second_node.write_lock() {
                                        node.write_unlock();
                                        parent_node.write_unlock();
                                        return Err(restart);
                                    }

                                    parent_node.change(parent_key, second_node);
                                    parent_node.write_unlock();

                                    second_node.add_prefix_before(node, second_node_key);
                                    second_node.write_unlock();

                                    node.write_unlock_obsolete();
                                    guard.defer(move || {
                                        node.dealloc();
                                    });
                                }
                            } else {
                                node.remove_and_unlock(
                                    version,
                                    key[level],
                                    parent_node,
                                    parent_version,
                                    parent_key,
                                    guard,
                                )?;
                            }
                            return Ok(());
                        }
                    }
                }
                level += 1;
                parent_version = version;
            }
        });
    }
}

impl<V> Drop for Tree<V> {
    fn drop(&mut self) {
        unsafe {
            self.root.drop::<V>();
        }
    }
}

pub struct NeedRestart;

fn restart_when_needed<T>(mut f: impl FnMut() -> Result<T, NeedRestart>) -> T {
    loop {
        match f() {
            Ok(v) => return v,
            Err(_) => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crossbeam_epoch::pin;
    use rand::prelude::*;
    use std::collections::HashMap;

    #[test]
    fn single_thread() {
        let mut rng = StdRng::seed_from_u64(114514);
        let tree = Tree::new();
        let mut ans = HashMap::new();
        let mut buf = [0u8; 1024];
        for _ in 0..10_000 {
            let base = (2.0f64.ln() / 32.0).exp();
            let len = (rng.next_u32() as f64).log(base) as usize;
            rng.fill_bytes(&mut buf[..len]);
            let value = rng.next_u32();

            ans.insert(buf[..len].to_vec(), value);
            if value % 2 == 0 {
                let guard = pin();
                tree.insert(&buf[..len], value, &guard);
            }
        }

        for (key, value) in &ans {
            let guard = pin();
            let res = tree.get(key, &guard);
            if *value % 2 == 0 {
                assert_eq!(res, Some(value));
            } else {
                assert_eq!(res, None);
            }
        }

        for (key, value) in &ans {
            if *value % 4 == 0 {
                let guard = pin();
                tree.remove(key, &guard);
            }
        }

        for (key, value) in &ans {
            let guard = pin();
            let res = tree.get(key, &guard);
            if *value % 4 == 2 {
                assert_eq!(res, Some(value));
            } else {
                assert_eq!(res, None);
            }
        }

        for (key, value) in &ans {
            if *value % 4 == 3 {
                let guard = pin();
                tree.insert(key, *value, &guard);
            }
        }

        for (key, value) in &ans {
            let guard = pin();
            let res = tree.get(key, &guard);
            let rem = *value % 4;
            if rem == 2 || rem == 3 {
                assert_eq!(res, Some(value));
            } else {
                assert_eq!(res, None);
            }
        }
    }
}
