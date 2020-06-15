mod node;

use crossbeam_epoch::pin;
use node::*;
use std::marker::PhantomData;

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

    pub fn insert(&self, key: &[u8], value: V) {
        let guard = pin();

        // restart begin
        restart_when_needed(|| {
            let mut node = NodePtr::null();
            let mut next_node = self.root;
            let mut parent_node = NodePtr::null();
            let mut parent_key = 0u8;
            let mut node_key = 0u8;
            let mut parent_version = 0u64;
            let mut level = 0u32;

            loop {
                parent_node = node;
                parent_key = node_key;
                node = next_node;
                let version = unsafe { node.read_lock()? };

                let next_level = level;
                return Ok(());
            }
        });
    }
}

struct NeedRestart;

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
    #[test]
    fn it_works() {
        println!("{}", std::mem::size_of::<Box<i32>>());
    }
}
