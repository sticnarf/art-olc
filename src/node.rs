use super::NeedRestart;
use static_assertions::{assert_eq_align, assert_eq_size};
use std::{
    alloc::{self, Layout},
    mem, ptr,
    sync::atomic::{AtomicU64, Ordering::*},
};

const MAX_STORED_PREFIX_LENGTH: usize = 11;

type Prefix = [u8; MAX_STORED_PREFIX_LENGTH];

pub struct NodeMeta {
    type_version_lock_obsolete: AtomicU64,
    count: u8,
    prefix: Prefix,
    prefix_len: u32,
}

assert_eq_align!(NodeMeta, [usize; 3]);
assert_eq_size!(NodeMeta, [usize; 3]);

impl NodeMeta {
    fn new(type_bits: u64) -> NodeMeta {
        let type_version_lock_obsolete = 0b100 | type_bits;
        NodeMeta {
            type_version_lock_obsolete: AtomicU64::new(type_version_lock_obsolete),
            count: 0,
            prefix: [0; MAX_STORED_PREFIX_LENGTH],
            prefix_len: 0,
        }
    }
}

fn is_locked(type_version_lock_obsolete: u64) -> bool {
    (type_version_lock_obsolete & 0b10) == 0b10
}

fn is_obsolete(type_version_lock_obsolete: u64) -> bool {
    (type_version_lock_obsolete & 1) == 1
}

const NODE_ALIGN: usize = 8;

const MSB: usize = usize::MAX ^ (usize::MAX >> 1);

#[derive(Copy, Clone)]
pub struct NodePtr(*mut u8);

impl NodePtr {
    pub fn null() -> NodePtr {
        NodePtr(ptr::null_mut())
    }

    pub unsafe fn dealloc(self) {
        let meta = &*(self.0 as *mut NodeMeta);
        let node_size = type_bits_to_node_size(meta.type_version_lock_obsolete.load(Relaxed) >> 62);
        let layout = Layout::from_size_align_unchecked(node_size, NODE_ALIGN);
        alloc::dealloc(self.0, layout);
    }

    unsafe fn has_prefix(self) -> bool {
        let meta = &*(self.0 as *mut NodeMeta);
        meta.prefix_len > 0
    }

    fn is_leaf(self) -> bool {
        (self.0 as usize & MSB) == MSB
    }

    // returns version and need_restart
    pub unsafe fn read_lock(self) -> Result<u64, NeedRestart> {
        let meta = &*(self.0 as *mut NodeMeta);
        let type_version_lock_obsolete = meta.type_version_lock_obsolete.load(SeqCst);
        if is_locked(type_version_lock_obsolete) || is_obsolete(type_version_lock_obsolete) {
            Err(NeedRestart)
        } else {
            Ok(type_version_lock_obsolete)
        }
    }

    pub unsafe fn check_prefix_pessimistic(
        self,
        level: u32,
        key: &[u8],
    ) -> Result<CheckPrefixPessimisticResult, NeedRestart> {
        if self.has_prefix() {
            let prev_level = level;
        }
        todo!()
    }
}

struct EntryPtr(*mut u8);

enum CheckPrefixPessimisticResult {
    Match,
    NoMatch {
        next_level: u32,
        not_matching_key: u8,
        remaining_prefix: Prefix,
    },
}

pub trait Node {
    const TYPE_BITS: u64;

    fn alloc() -> NodePtr {
        unsafe {
            let ptr = alloc::alloc(Layout::from_size_align_unchecked(
                Self::node_size(),
                NODE_ALIGN,
            ));
            (ptr as *mut NodeMeta).write(NodeMeta::new(Self::TYPE_BITS));
            NodePtr(ptr)
        }
    }

    unsafe fn alloc_with_prefix(prefix: *const u8, prefix_len: u32) -> NodePtr {
        let ptr = Self::alloc();
        let meta = &mut *(ptr.0 as *mut NodeMeta);
        ptr::copy_nonoverlapping(prefix, meta.prefix.as_mut_ptr(), prefix_len as usize);
        ptr
    }

    fn node_size() -> usize {
        mem::size_of::<NodeMeta>() + mem::size_of::<Node4>()
    }
}

pub struct Node4 {
    keys: [u8; 4],
    children: [NodePtr; 4],
}

pub struct Node16 {
    keys: [u8; 16],
    children: [NodePtr; 16],
}

pub struct Node48 {
    child_index: [u8; 256],
    children: [NodePtr; 48],
}

pub struct Node256 {
    children: [NodePtr; 48],
}

impl Node for Node4 {
    const TYPE_BITS: u64 = 0;
}

impl Node for Node16 {
    const TYPE_BITS: u64 = 1 << 62;
}

impl Node for Node48 {
    const TYPE_BITS: u64 = 2 << 62;
}

impl Node for Node256 {
    const TYPE_BITS: u64 = 3 << 62;
}

fn type_bits_to_node_size(type_bits: u64) -> usize {
    match type_bits {
        Node4::TYPE_BITS => Node4::node_size(),
        Node16::TYPE_BITS => Node16::node_size(),
        Node48::TYPE_BITS => Node48::node_size(),
        Node256::TYPE_BITS => Node256::node_size(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}
