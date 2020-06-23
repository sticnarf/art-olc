use super::NeedRestart;

use crossbeam_epoch::Guard;
use std::{
    alloc::{self, Layout},
    mem, ptr, slice,
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

    #[inline]
    fn type_bits(&self) -> u64 {
        self.type_version_lock_obsolete.load(Relaxed) & (0b11 << 62)
    }

    #[inline]
    pub fn has_prefix(&self) -> bool {
        self.prefix_len > 0
    }

    #[inline]
    pub fn prefix_len(&self) -> usize {
        self.prefix_len as usize
    }

    #[inline]
    pub fn set_prefix(&mut self, prefix: &[u8], prefix_len: usize) {
        if prefix_len > 0 {
            let inline_len = usize::min(prefix_len, MAX_STORED_PREFIX_LENGTH);
            self.prefix[..inline_len].copy_from_slice(&prefix[..inline_len]);
            self.prefix_len = prefix_len as u32;
        } else {
            self.prefix_len = 0;
        }
    }

    #[inline]
    pub fn inline_prefix(&self) -> &Prefix {
        &self.prefix
    }

    #[inline]
    pub fn child_count(&self) -> usize {
        self.count as usize
    }

    #[inline]
    pub fn read_lock(&self) -> Result<u64, NeedRestart> {
        let type_version_lock_obsolete = self.type_version_lock_obsolete.load(SeqCst);
        if is_locked(type_version_lock_obsolete) || is_obsolete(type_version_lock_obsolete) {
            Err(NeedRestart)
        } else {
            Ok(type_version_lock_obsolete)
        }
    }

    #[inline]
    pub fn read_unlock(&self, version: u64) -> Result<(), NeedRestart> {
        if version == self.type_version_lock_obsolete.load(SeqCst) {
            Ok(())
        } else {
            Err(NeedRestart)
        }
    }

    #[inline]
    pub fn write_lock(&self) -> Result<(), NeedRestart> {
        let version = self.read_lock()?;
        self.upgrade_to_write_lock(version)?;
        Ok(())
    }

    #[inline]
    pub fn upgrade_to_write_lock(&self, version: u64) -> Result<u64, NeedRestart> {
        if let Ok(_) = self.type_version_lock_obsolete.compare_exchange(
            version,
            version + 0b10,
            SeqCst,
            Relaxed,
        ) {
            Ok(version + 0b10)
        } else {
            Err(NeedRestart)
        }
    }

    #[inline]
    pub fn write_unlock(&self) {
        self.type_version_lock_obsolete.fetch_add(0b10, SeqCst);
    }

    #[inline]
    pub fn write_unlock_obsolete(&self) {
        self.type_version_lock_obsolete.fetch_add(0b11, SeqCst);
    }

    #[inline]
    pub fn check_read(&self, start_read: u64) -> Result<(), NeedRestart> {
        self.read_unlock(start_read)
    }

    #[inline]
    pub unsafe fn add_prefix_before(&mut self, node: NodePtr, key: u8) {
        let prefix_copy_count = usize::min(MAX_STORED_PREFIX_LENGTH, node.meta().prefix_len() + 1);
        ptr::copy(
            self.prefix.as_ptr(),
            self.prefix.as_mut_ptr().wrapping_add(prefix_copy_count),
            usize::min(
                self.prefix_len(),
                MAX_STORED_PREFIX_LENGTH - prefix_copy_count,
            ),
        );
        ptr::copy_nonoverlapping(
            node.meta().prefix.as_ptr(),
            self.prefix.as_mut_ptr(),
            usize::min(prefix_copy_count, node.meta().prefix_len()),
        );
        if node.meta().prefix_len() < MAX_STORED_PREFIX_LENGTH {
            self.prefix
                .as_mut_ptr()
                .wrapping_add(prefix_copy_count - 1)
                .write(key);
        }
        self.prefix_len += node.meta().prefix_len + 1;
    }
}

fn is_locked(type_version_lock_obsolete: u64) -> bool {
    (type_version_lock_obsolete & 0b10) == 0b10
}

fn is_obsolete(type_version_lock_obsolete: u64) -> bool {
    (type_version_lock_obsolete & 1) == 1
}

const MSB: usize = usize::MAX ^ (usize::MAX >> 1);

#[derive(Copy, Clone, Debug)]
pub struct NodePtr(usize);

impl NodePtr {
    #[inline]
    pub fn null() -> NodePtr {
        NodePtr(0)
    }

    #[inline]
    pub fn is_null(self) -> bool {
        self.0 == 0
    }

    #[inline]
    pub unsafe fn dealloc(self) {
        debug_assert!(!self.is_null());
        match self.meta().type_bits() {
            Node4::TYPE_BITS => drop(Box::from_raw(self.0 as *mut Node4)),
            Node16::TYPE_BITS => drop(Box::from_raw(self.0 as *mut Node16)),
            Node48::TYPE_BITS => drop(Box::from_raw(self.0 as *mut Node48)),
            Node256::TYPE_BITS => drop(Box::from_raw(self.0 as *mut Node256)),
            _ => unreachable!(),
        }
    }

    #[inline]
    pub unsafe fn meta<'a>(self) -> &'a NodeMeta {
        debug_assert!(!self.is_null());
        &*(self.0 as *mut NodeMeta as *const _)
    }

    #[inline]
    pub unsafe fn meta_mut<'a>(self) -> &'a mut NodeMeta {
        debug_assert!(!self.is_null());
        &mut *(self.0 as *mut NodeMeta)
    }

    #[inline]
    pub fn is_entry(self) -> bool {
        (self.0 as usize & MSB) == MSB
    }

    #[inline]
    pub unsafe fn to_entry(self) -> EntryPtr {
        EntryPtr((self.0 as usize & !MSB) as *mut u8)
    }

    #[inline]
    pub unsafe fn node<'a, N: Node>(self) -> &'a N {
        debug_assert_eq!(self.meta().type_bits(), N::TYPE_BITS);
        &*(self.0 as *mut N as *const N)
    }

    #[inline]
    pub unsafe fn node_mut<'a, N: Node>(self) -> &'a mut N {
        debug_assert_eq!(self.meta().type_bits(), N::TYPE_BITS);
        &mut *(self.0 as *mut N)
    }

    #[inline]
    unsafe fn get_any_child_entry(self) -> Result<EntryPtr, NeedRestart> {
        let mut next_node = self;

        loop {
            let node = next_node;
            let version = node.meta().read_lock()?;

            next_node = node.get_any_child();
            node.meta().read_unlock(version)?;

            if next_node.is_entry() {
                return Ok(next_node.to_entry());
            }
        }
    }

    #[inline]
    unsafe fn get_any_child(self) -> NodePtr {
        match self.meta().type_bits() {
            Node4::TYPE_BITS => self.node::<Node4>().get_any_child(),
            Node16::TYPE_BITS => self.node::<Node16>().get_any_child(),
            Node48::TYPE_BITS => self.node::<Node48>().get_any_child(),
            Node256::TYPE_BITS => self.node::<Node256>().get_any_child(),
            _ => unreachable!(),
        }
    }

    #[inline]
    pub unsafe fn drop<V>(self) {
        if self.is_entry() {
            self.to_entry().dealloc::<V>();
            return;
        }

        match self.meta().type_bits() {
            Node4::TYPE_BITS => Box::from_raw(self.0 as *mut Node4).drop::<V>(),
            Node16::TYPE_BITS => Box::from_raw(self.0 as *mut Node16).drop::<V>(),
            Node48::TYPE_BITS => Box::from_raw(self.0 as *mut Node48).drop::<V>(),
            Node256::TYPE_BITS => Box::from_raw(self.0 as *mut Node256).drop::<V>(),
            _ => unreachable!(),
        }
    }

    #[inline]
    pub unsafe fn check_prefix(self, key: &[u8], mut level: usize) -> CheckPrefixResult {
        let meta = self.meta();
        if meta.has_prefix() {
            let prefix_len = meta.prefix_len();
            if key.len() < level + prefix_len {
                return CheckPrefixResult::NoMatch;
            }
            for i in 0..usize::min(prefix_len, MAX_STORED_PREFIX_LENGTH) {
                if meta.prefix[i] != key[level] {
                    return CheckPrefixResult::NoMatch;
                }
                level += 1;
            }
            if prefix_len > MAX_STORED_PREFIX_LENGTH {
                level = level + (prefix_len - MAX_STORED_PREFIX_LENGTH);
                return CheckPrefixResult::Match {
                    optimistic: true,
                    next_level: level,
                };
            }
        }
        CheckPrefixResult::Match {
            optimistic: false,
            next_level: level,
        }
    }

    #[inline]
    pub unsafe fn check_prefix_pessimistic(
        self,
        key: &[u8],
        mut level: usize,
    ) -> Result<CheckPrefixPessimisticResult, NeedRestart> {
        let meta = self.meta();
        if meta.has_prefix() {
            let prefix_len = meta.prefix_len();
            let prev_level = level;
            let mut kt: *const u8 = ptr::null();
            for i in 0..prefix_len {
                if i == MAX_STORED_PREFIX_LENGTH {
                    let entry = self.get_any_child_entry()?;
                    kt = entry.key().as_ptr();
                }
                let cur_key = if i >= MAX_STORED_PREFIX_LENGTH {
                    kt.wrapping_add(level).read()
                } else {
                    meta.prefix[i]
                };
                if Some(&cur_key) != key.get(level) {
                    let non_matching_key = cur_key;
                    let mut remaining_prefix = Prefix::default();
                    if prefix_len > MAX_STORED_PREFIX_LENGTH {
                        if i < MAX_STORED_PREFIX_LENGTH {
                            let entry = self.get_any_child_entry()?;
                            kt = entry.key().as_ptr();
                        }
                        ptr::copy_nonoverlapping(
                            kt.wrapping_add(level + 1),
                            remaining_prefix.as_mut_ptr(),
                            usize::min(
                                prefix_len - (level - prev_level) - 1,
                                MAX_STORED_PREFIX_LENGTH,
                            ),
                        );
                    } else {
                        ptr::copy_nonoverlapping(
                            meta.prefix.as_ptr().wrapping_add(i + 1),
                            remaining_prefix.as_mut_ptr(),
                            prefix_len - i - 1,
                        );
                    }
                    return Ok(CheckPrefixPessimisticResult::NoMatch {
                        next_level: level,
                        non_matching_key,
                        remaining_prefix,
                    });
                }
                level += 1;
            }
        }
        Ok(CheckPrefixPessimisticResult::Match { next_level: level })
    }

    #[inline]
    pub unsafe fn get_child(self, node_key: Option<u8>) -> NodePtr {
        match self.meta().type_bits() {
            Node4::TYPE_BITS => self.node::<Node4>().get_child(node_key),
            Node16::TYPE_BITS => self.node::<Node16>().get_child(node_key),
            Node48::TYPE_BITS => self.node::<Node48>().get_child(node_key),
            Node256::TYPE_BITS => self.node::<Node256>().get_child(node_key),
            _ => unreachable!(),
        }
    }

    #[inline]
    pub unsafe fn change(self, parent_key: Option<u8>, new_node: NodePtr) {
        match self.meta().type_bits() {
            Node4::TYPE_BITS => self.node_mut::<Node4>().change(parent_key, new_node),
            Node16::TYPE_BITS => self.node_mut::<Node16>().change(parent_key, new_node),
            Node48::TYPE_BITS => self.node_mut::<Node48>().change(parent_key, new_node),
            Node256::TYPE_BITS => self.node_mut::<Node256>().change(parent_key, new_node),
            _ => unreachable!(),
        }
    }

    #[inline]
    pub unsafe fn insert_and_unlock<V>(
        self,
        version: u64,
        parent_node: NodePtr,
        parent_version: u64,
        parent_key: Option<u8>,
        key: Option<u8>,
        val: NodePtr,
        guard: &Guard,
    ) -> Result<(), NeedRestart> {
        match self.meta().type_bits() {
            Node4::TYPE_BITS => self.node_mut::<Node4>().insert_grow::<Node16, V>(
                version,
                parent_node,
                parent_version,
                parent_key,
                key,
                val,
                guard,
            ),
            Node16::TYPE_BITS => self.node_mut::<Node16>().insert_grow::<Node48, V>(
                version,
                parent_node,
                parent_version,
                parent_key,
                key,
                val,
                guard,
            ),
            Node48::TYPE_BITS => self.node_mut::<Node48>().insert_grow::<Node256, V>(
                version,
                parent_node,
                parent_version,
                parent_key,
                key,
                val,
                guard,
            ),
            Node256::TYPE_BITS => self.node_mut::<Node256>().insert_grow::<Node256, V>(
                version,
                parent_node,
                parent_version,
                parent_key,
                key,
                val,
                guard,
            ),
            _ => unreachable!(),
        }
    }

    #[inline]
    pub unsafe fn remove_and_unlock(
        self,
        version: u64,
        key: Option<u8>,
        parent_node: NodePtr,
        parent_version: u64,
        parent_key: Option<u8>,
        guard: &Guard,
    ) -> Result<(), NeedRestart> {
        match self.meta().type_bits() {
            Node4::TYPE_BITS => self.node_mut::<Node4>().remove_and_shrink::<Node4>(
                version,
                parent_node,
                parent_version,
                parent_key,
                key,
                guard,
            ),
            Node16::TYPE_BITS => self.node_mut::<Node16>().remove_and_shrink::<Node4>(
                version,
                parent_node,
                parent_version,
                parent_key,
                key,
                guard,
            ),
            Node48::TYPE_BITS => self.node_mut::<Node48>().remove_and_shrink::<Node16>(
                version,
                parent_node,
                parent_version,
                parent_key,
                key,
                guard,
            ),
            Node256::TYPE_BITS => self.node_mut::<Node256>().remove_and_shrink::<Node48>(
                version,
                parent_node,
                parent_version,
                parent_key,
                key,
                guard,
            ),
            _ => unreachable!(),
        }
    }
}

impl<N: Node> From<Box<N>> for NodePtr {
    fn from(node: Box<N>) -> NodePtr {
        NodePtr(Box::into_raw(node) as usize)
    }
}

#[derive(Copy, Clone)]
pub struct EntryPtr(*mut u8);

impl EntryPtr {
    #[inline]
    pub fn alloc<V>(key: &[u8], value: V) -> EntryPtr {
        let layout = Self::layout::<V>(key.len());
        let offset = layout.size() - mem::size_of::<V>();
        unsafe {
            let ptr = alloc::alloc_zeroed(layout);
            (ptr as *mut usize).write(key.len());
            ptr.wrapping_add(mem::size_of::<usize>())
                .copy_from_nonoverlapping(key.as_ptr(), key.len());
            (ptr.wrapping_add(offset) as *mut V).write(value);
            EntryPtr(ptr)
        }
    }

    #[inline]
    pub unsafe fn dealloc<V>(self) {
        let ptr = self.0;
        let key_len = (ptr as *mut usize).read();
        let layout = Self::layout::<V>(key_len);
        alloc::dealloc(ptr, layout);
    }

    #[inline]
    pub unsafe fn key<'a>(self) -> &'a [u8] {
        let ptr = self.0;
        let key_len = (ptr as *mut usize).read();
        slice::from_raw_parts_mut(ptr.wrapping_add(mem::size_of::<usize>()), key_len)
    }

    #[inline]
    pub unsafe fn value_mut<'a, V>(self) -> &'a mut V {
        let ptr = self.0;
        let key_len = (ptr as *mut usize).read();
        let layout = Self::layout::<V>(key_len);
        let offset = layout.size() - mem::size_of::<V>();
        &mut *(ptr.wrapping_add(offset) as *mut V)
    }

    #[inline]
    fn layout<V>(key_len: usize) -> Layout {
        let align_v = mem::align_of::<V>();
        let key_space = mem::size_of::<usize>() + key_len;
        let offset = (key_space + align_v - 1) / align_v * align_v;
        let align = usize::max(mem::align_of::<usize>(), align_v);
        let size = offset + mem::size_of::<V>();
        unsafe { Layout::from_size_align_unchecked(size, align) }
    }
}

impl From<EntryPtr> for NodePtr {
    fn from(entry_ptr: EntryPtr) -> NodePtr {
        let addr = entry_ptr.0 as usize;
        NodePtr(addr | MSB)
    }
}

pub enum CheckPrefixResult {
    NoMatch,
    Match { optimistic: bool, next_level: usize },
}

pub enum CheckPrefixPessimisticResult {
    Match {
        next_level: usize,
    },
    NoMatch {
        next_level: usize,
        non_matching_key: u8,
        remaining_prefix: Prefix,
    },
}

pub trait Node: Sized {
    const TYPE_BITS: u64;

    fn new() -> Self;

    #[inline]
    fn new_with_prefix(prefix: &[u8], prefix_len: usize) -> Self {
        let mut node = Self::new();
        node.meta_mut().set_prefix(prefix, prefix_len);
        node
    }

    #[inline]
    fn node_size() -> usize {
        mem::size_of::<NodeMeta>() + mem::size_of::<Self>()
    }

    fn meta(&self) -> &NodeMeta {
        // All types that implements `Node` must be `#[repr(C)]` and
        // place `NodeMeta` as its first field. So we can transmute
        // `&self` to `&NodeMeta`.
        unsafe { &*(self as *const _ as *const NodeMeta) }
    }

    fn meta_mut(&mut self) -> &mut NodeMeta {
        // All types that implements `Node` must be `#[repr(C)]` and
        // place `NodeMeta` as its first field. So we can transmute
        // `&mut self` to `&mut NodeMeta`.
        unsafe { &mut *(self as *mut _ as *mut NodeMeta) }
    }

    fn insert(&mut self, key: Option<u8>, child: NodePtr);

    fn remove(&mut self, key: Option<u8>);

    fn drop<V>(self: Box<Self>);

    fn get_any_child(&self) -> NodePtr;

    fn get_child(&self, node_key: Option<u8>) -> NodePtr;

    // fn get_children(&self, )

    fn change(&mut self, key: Option<u8>, new_node: NodePtr);

    fn set_leaf(&mut self, leaf: NodePtr);

    fn is_full(&self) -> bool;

    fn is_under_full(&self) -> bool;

    fn copy_to<Dst: Node>(&self, dst: &mut Dst);

    #[inline]
    unsafe fn insert_grow<N: Node, V>(
        &mut self,
        version: u64,
        parent_node: NodePtr,
        parent_version: u64,
        parent_key: Option<u8>,
        key: Option<u8>,
        val: NodePtr,
        guard: &Guard,
    ) -> Result<(), NeedRestart> {
        if !self.is_full() {
            if !parent_node.is_null() {
                parent_node.meta().read_unlock(parent_version)?;
            }
            self.meta().upgrade_to_write_lock(version)?;
            self.insert(key, val);
            self.meta().write_unlock();
            return Ok(());
        }

        parent_node.meta().upgrade_to_write_lock(parent_version)?;

        if let Err(restart) = self.meta().upgrade_to_write_lock(version) {
            parent_node.meta().write_unlock();
            return Err(restart);
        }

        let mut big_node = Box::new(N::new_with_prefix(
            self.meta().inline_prefix(),
            self.meta().prefix_len(),
        ));
        self.copy_to(&mut *big_node);
        big_node.insert(key, val);

        parent_node.change(parent_key, big_node.into());

        self.meta().write_unlock_obsolete();
        guard.defer_unchecked(move || {
            drop(Box::from_raw(self as *mut Self));
        });
        parent_node.meta().write_unlock();
        Ok(())
    }

    #[inline]
    unsafe fn remove_and_shrink<N: Node>(
        &mut self,
        version: u64,
        parent_node: NodePtr,
        parent_version: u64,
        parent_key: Option<u8>,
        key: Option<u8>,
        guard: &Guard,
    ) -> Result<(), NeedRestart> {
        if !self.is_under_full() || parent_node.is_null() {
            if !parent_node.is_null() {
                parent_node.meta().read_unlock(parent_version)?;
            }
            self.meta().upgrade_to_write_lock(version)?;
            self.remove(key);
            self.meta().write_unlock();
            return Ok(());
        }

        parent_node.meta().upgrade_to_write_lock(parent_version)?;
        if let Err(restart) = self.meta().upgrade_to_write_lock(version) {
            parent_node.meta().write_unlock();
            return Err(restart);
        }

        let mut small_node = Box::new(N::new_with_prefix(
            self.meta().inline_prefix(),
            self.meta().prefix_len(),
        ));
        self.copy_to(&mut *small_node);
        small_node.remove(key);
        parent_node.change(parent_key, small_node.into());

        self.meta().write_unlock_obsolete();
        guard.defer_unchecked(move || {
            drop(Box::from_raw(self as *mut Self));
        });
        parent_node.meta().write_unlock();
        Ok(())
    }
}

#[repr(C)]
pub struct Node4 {
    meta: NodeMeta,
    leaf: NodePtr,
    keys: [u8; 4],
    children: [NodePtr; 4],
}

impl Node4 {
    #[inline]
    pub fn get_second_child(&self, key: Option<u8>) -> (NodePtr, Option<u8>) {
        if let Some(key) = key {
            if !self.leaf.is_null() {
                return (self.leaf, None);
            }
            let count = self.meta.count as usize;
            for i in 0..count {
                if self.keys[i] != key {
                    return (self.children[i], Some(self.keys[i]));
                }
            }
            unreachable!()
        } else {
            (self.children[0], Some(self.keys[0]))
        }
    }
}

impl Node for Node4 {
    const TYPE_BITS: u64 = 0;

    #[inline]
    fn new() -> Self {
        Self {
            meta: NodeMeta::new(Self::TYPE_BITS),
            keys: [0; 4],
            children: [NodePtr::null(); 4],
            leaf: NodePtr::null(),
        }
    }

    #[inline]
    fn insert(&mut self, key: Option<u8>, child: NodePtr) {
        if let Some(key) = key {
            let count = self.meta.count as usize;
            let mut pos = 0;
            while pos < count && self.keys[pos] < key {
                pos += 1;
            }
            self.keys.copy_within(pos..count, pos + 1);
            self.children.copy_within(pos..count, pos + 1);
            self.keys[pos] = key;
            self.children[pos] = child;
            self.meta.count += 1;
        } else {
            self.leaf = child;
        }
    }

    #[inline]
    fn remove(&mut self, key: Option<u8>) {
        if let Some(key) = key {
            let count = self.meta.count as usize;
            for i in 0..count {
                if self.keys[i] == key {
                    self.keys.copy_within((i + 1)..count, i);
                    self.children.copy_within((i + 1)..count, i);
                    self.meta.count -= 1;
                    return;
                }
            }
        } else {
            self.leaf = NodePtr::null();
        }
    }

    #[inline]
    fn drop<V>(self: Box<Self>) {
        let count = self.meta.count as usize;
        for i in 0..count {
            unsafe {
                self.children[i].drop::<V>();
            }
        }
        if !self.leaf.is_null() {
            unsafe {
                self.leaf.to_entry().dealloc::<V>();
            }
        }
    }

    #[inline]
    fn get_any_child(&self) -> NodePtr {
        let count = self.meta.count as usize;
        if !self.leaf.is_null() {
            return self.leaf;
        }
        let mut any_child = NodePtr::null();
        for i in 0..count {
            if self.children[i].is_entry() {
                return self.children[i];
            } else {
                any_child = self.children[i];
            }
        }
        any_child
    }

    #[inline]
    fn get_child(&self, node_key: Option<u8>) -> NodePtr {
        if let Some(node_key) = node_key {
            let count = self.meta.count as usize;
            for i in 0..count {
                if self.keys[i] == node_key {
                    return self.children[i];
                }
            }
            NodePtr::null()
        } else {
            self.leaf
        }
    }

    #[inline]
    fn change(&mut self, key: Option<u8>, new_node: NodePtr) {
        if let Some(key) = key {
            let count = self.meta.count as usize;
            for i in 0..count {
                if self.keys[i] == key {
                    self.children[i] = new_node;
                    return;
                }
            }
            unreachable!()
        } else {
            self.leaf = new_node;
        }
    }

    #[inline]
    fn set_leaf(&mut self, leaf: NodePtr) {
        self.leaf = leaf;
    }

    #[inline]
    fn is_full(&self) -> bool {
        self.meta.count == 4
    }

    #[inline]
    fn is_under_full(&self) -> bool {
        false
    }

    #[inline]
    fn copy_to<Dst: Node>(&self, dst: &mut Dst) {
        let count = self.meta.count as usize;
        for i in 0..count {
            Dst::insert(dst, Some(self.keys[i]), self.children[i]);
        }
        Dst::set_leaf(dst, self.leaf);
    }
}

#[repr(C)]
pub struct Node16 {
    meta: NodeMeta,
    leaf: NodePtr,
    keys: [u8; 16],
    children: [NodePtr; 16],
}

impl Node16 {
    #[inline]
    fn flip_sign(key_byte: u8) -> u8 {
        key_byte ^ 128
    }

    #[cfg(all(
        any(target_arch = "x86", target_arch = "x86_64"),
        target_feature = "sse2"
    ))]
    #[inline]
    fn get_child_pos(&self, key: u8, count: usize) -> Option<usize> {
        #[cfg(target_arch = "x86")]
        use std::arch::x86::*;
        #[cfg(target_arch = "x86_64")]
        use std::arch::x86_64::*;

        let flipped = Self::flip_sign(key);
        let bitfield = unsafe {
            let cmp = _mm_cmpeq_epi8(
                _mm_set1_epi8(flipped as i8),
                _mm_loadu_si128(self.keys.as_ptr() as *const _),
            );
            _mm_movemask_epi8(cmp) & ((1 << count) - 1)
        };

        if bitfield == 0 {
            None
        } else {
            Some(bitfield.trailing_zeros() as usize)
        }
    }
}

impl Node for Node16 {
    const TYPE_BITS: u64 = 1 << 62;

    #[inline]
    fn new() -> Self {
        Self {
            meta: NodeMeta::new(Self::TYPE_BITS),
            keys: [0; 16],
            children: [NodePtr::null(); 16],
            leaf: NodePtr::null(),
        }
    }

    #[cfg(all(
        any(target_arch = "x86", target_arch = "x86_64"),
        target_feature = "sse2"
    ))]
    #[inline]
    fn insert(&mut self, key: Option<u8>, child: NodePtr) {
        #[cfg(target_arch = "x86")]
        use std::arch::x86::*;
        #[cfg(target_arch = "x86_64")]
        use std::arch::x86_64::*;

        if let Some(key) = key {
            let flipped = Self::flip_sign(key);
            let cmp = unsafe {
                _mm_cmplt_epi8(
                    _mm_set1_epi8(flipped as i8),
                    _mm_loadu_si128(self.keys.as_ptr() as *const _),
                )
            };
            let count = self.meta.count as usize;
            let bitfield = unsafe { _mm_movemask_epi8(cmp) & (0xFFFF >> (16 - count)) };
            let pos = if bitfield == 0 {
                count
            } else {
                bitfield.trailing_zeros() as usize
            };
            self.keys.copy_within(pos..count, pos + 1);
            self.children.copy_within(pos..count, pos + 1);
            self.keys[pos] = flipped;
            self.children[pos] = child;
            self.meta.count += 1;
        } else {
            self.leaf = child;
        }
    }

    #[inline]
    fn remove(&mut self, key: Option<u8>) {
        if let Some(key) = key {
            let count = self.meta.count as usize;
            if let Some(pos) = self.get_child_pos(key, count) {
                self.keys.copy_within((pos + 1)..count, pos);
                self.children.copy_within((pos + 1)..count, pos);
                self.meta.count -= 1;
            }
        } else {
            self.leaf = NodePtr::null();
        }
    }

    #[inline]
    fn drop<V>(self: Box<Self>) {
        let count = self.meta.count as usize;
        for i in 0..count {
            unsafe {
                self.children[i].drop::<V>();
            }
        }
        if !self.leaf.is_null() {
            unsafe {
                self.leaf.to_entry().dealloc::<V>();
            }
        }
    }

    #[inline]
    fn get_any_child(&self) -> NodePtr {
        let count = self.meta.count as usize;
        if !self.leaf.is_null() {
            return self.leaf;
        }
        for i in 0..count {
            if self.children[i].is_entry() {
                return self.children[i];
            }
        }
        self.children[0]
    }

    #[inline]
    fn get_child(&self, node_key: Option<u8>) -> NodePtr {
        if let Some(node_key) = node_key {
            let count = self.meta.count as usize;
            if let Some(pos) = self.get_child_pos(node_key, count) {
                self.children[pos]
            } else {
                NodePtr::null()
            }
        } else {
            self.leaf
        }
    }

    #[inline]
    fn change(&mut self, key: Option<u8>, new_node: NodePtr) {
        if let Some(key) = key {
            let count = self.meta.count as usize;
            let pos = self.get_child_pos(key, count).unwrap();
            self.children[pos] = new_node;
        } else {
            self.leaf = new_node;
        }
    }

    #[inline]
    fn set_leaf(&mut self, leaf: NodePtr) {
        self.leaf = leaf;
    }

    #[inline]
    fn is_full(&self) -> bool {
        self.meta.count == 16
    }

    #[inline]
    fn is_under_full(&self) -> bool {
        self.meta.count == 3
    }

    #[inline]
    fn copy_to<Dst: Node>(&self, dst: &mut Dst) {
        let count = self.meta.count as usize;
        let node = self;
        for i in 0..count {
            Dst::insert(dst, Some(Self::flip_sign(node.keys[i])), node.children[i]);
        }
        Dst::set_leaf(dst, node.leaf);
    }
}

#[repr(C)]
pub struct Node48 {
    meta: NodeMeta,
    leaf: NodePtr,
    child_index: [u8; 256],
    children: [NodePtr; 48],
}

impl Node48 {
    const EMPTY_MARKER: u8 = 48;
}

impl Node for Node48 {
    const TYPE_BITS: u64 = 2 << 62;

    #[inline]
    fn new() -> Self {
        Self {
            meta: NodeMeta::new(Self::TYPE_BITS),
            child_index: [Self::EMPTY_MARKER; 256],
            children: [NodePtr::null(); 48],
            leaf: NodePtr::null(),
        }
    }

    #[inline]
    fn insert(&mut self, key: Option<u8>, child: NodePtr) {
        if let Some(key) = key {
            let mut pos = self.meta.count as usize;
            if !self.children[pos].is_null() {
                for i in 0..48 {
                    if self.children[i].is_null() {
                        pos = i;
                        break;
                    }
                }
            }
            self.children[pos] = child;
            self.child_index[key as usize] = pos as u8;
            self.meta.count += 1;
        } else {
            self.leaf = child;
        }
    }

    #[inline]
    fn remove(&mut self, key: Option<u8>) {
        if let Some(key) = key {
            let index = self.child_index[key as usize];
            if index == Self::EMPTY_MARKER {
                return;
            }
            self.children[index as usize] = NodePtr::null();
            self.child_index[key as usize] = Self::EMPTY_MARKER;
            self.meta.count -= 1;
        } else {
            self.leaf = NodePtr::null();
        }
    }

    #[inline]
    fn drop<V>(self: Box<Self>) {
        for i in 0..=255 {
            let index = self.child_index[i];
            if index != Self::EMPTY_MARKER {
                unsafe {
                    self.children[index as usize].drop::<V>();
                }
            }
        }
        if !self.leaf.is_null() {
            unsafe {
                self.leaf.to_entry().dealloc::<V>();
            }
        }
    }

    #[inline]
    fn get_any_child(&self) -> NodePtr {
        if !self.leaf.is_null() {
            return self.leaf;
        }
        let mut any_child = NodePtr::null();
        for i in 0..=255 {
            let index = self.child_index[i];
            if index != Self::EMPTY_MARKER {
                let child = self.children[index as usize];
                if child.is_entry() {
                    return child;
                } else {
                    any_child = child;
                }
            }
        }
        any_child
    }

    #[inline]
    fn get_child(&self, node_key: Option<u8>) -> NodePtr {
        if let Some(node_key) = node_key {
            let index = self.child_index[node_key as usize];
            if index == Self::EMPTY_MARKER {
                NodePtr::null()
            } else {
                self.children[index as usize]
            }
        } else {
            self.leaf
        }
    }

    #[inline]
    fn change(&mut self, key: Option<u8>, new_node: NodePtr) {
        if let Some(key) = key {
            let index = self.child_index[key as usize] as usize;
            self.children[index] = new_node;
        } else {
            self.leaf = NodePtr::null();
        }
    }

    #[inline]
    fn set_leaf(&mut self, leaf: NodePtr) {
        self.leaf = leaf;
    }

    #[inline]
    fn is_full(&self) -> bool {
        self.meta.count == 48
    }

    #[inline]
    fn is_under_full(&self) -> bool {
        self.meta.count == 12
    }

    #[inline]
    fn copy_to<Dst: Node>(&self, dst: &mut Dst) {
        for key in 0..256 {
            let idx = self.child_index[key];
            if idx != Self::EMPTY_MARKER {
                Dst::insert(dst, Some(key as u8), self.children[idx as usize]);
            }
        }
        Dst::set_leaf(dst, self.leaf);
    }
}

#[repr(C)]
pub struct Node256 {
    meta: NodeMeta,
    leaf: NodePtr,
    children: [NodePtr; 256],
}

impl Node for Node256 {
    const TYPE_BITS: u64 = 3 << 62;

    #[inline]
    fn new() -> Self {
        Self {
            meta: NodeMeta::new(Self::TYPE_BITS),
            children: [NodePtr::null(); 256],
            leaf: NodePtr::null(),
        }
    }

    #[inline]
    fn insert(&mut self, key: Option<u8>, child: NodePtr) {
        if let Some(key) = key {
            self.children[key as usize] = child;
            // hack
            self.meta.count = self.meta.count.wrapping_add(1);
        } else {
            self.leaf = child;
        }
    }

    #[inline]
    fn remove(&mut self, key: Option<u8>) {
        if let Some(key) = key {
            self.children[key as usize] = NodePtr::null();
            // hack
            self.meta.count = self.meta.count.wrapping_sub(1);
        } else {
            self.leaf = NodePtr::null();
        }
    }

    #[inline]
    fn drop<V>(self: Box<Self>) {
        for i in 0..256 {
            let child = self.children[i];
            if !child.is_null() {
                unsafe {
                    child.drop::<V>();
                }
            }
        }
        if !self.leaf.is_null() {
            unsafe {
                self.leaf.to_entry().dealloc::<V>();
            }
        }
    }

    #[inline]
    fn get_any_child(&self) -> NodePtr {
        if !self.leaf.is_null() {
            return self.leaf;
        }
        let mut any_child = NodePtr::null();
        for i in 0..=255 {
            let child = self.children[i];
            if !child.is_null() {
                if child.is_entry() {
                    return child;
                } else {
                    any_child = child;
                }
            }
        }
        any_child
    }

    #[inline]
    fn get_child(&self, node_key: Option<u8>) -> NodePtr {
        if let Some(node_key) = node_key {
            self.children[node_key as usize]
        } else {
            self.leaf
        }
    }

    #[inline]
    fn change(&mut self, key: Option<u8>, new_node: NodePtr) {
        if let Some(key) = key {
            self.children[key as usize] = new_node;
        } else {
            self.leaf = new_node;
        }
    }

    #[inline]
    fn set_leaf(&mut self, leaf: NodePtr) {
        self.leaf = leaf;
    }

    #[inline]
    fn is_full(&self) -> bool {
        false
    }

    #[inline]
    fn is_under_full(&self) -> bool {
        self.meta.count == 37
    }

    #[inline]
    fn copy_to<Dst: Node>(&self, dst: &mut Dst) {
        for i in 0..=255 {
            let node = self.children[i as usize];
            if !node.is_null() {
                Dst::insert(dst, Some(i), node);
            }
        }
        Dst::set_leaf(dst, self.leaf);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        println!("{}", mem::align_of::<NodeMeta>());
    }
}
