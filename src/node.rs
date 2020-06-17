use super::NeedRestart;

use crossbeam_epoch::Guard;
use static_assertions::assert_eq_size;
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

const META_LEN: usize = 24;

assert_eq_size!(NodeMeta, [u8; META_LEN]);

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

#[derive(Copy, Clone, Debug)]
pub struct NodePtr(*mut u8);

unsafe impl Send for NodePtr {}

impl NodePtr {
    pub fn null() -> NodePtr {
        NodePtr(ptr::null_mut())
    }

    pub fn is_null(self) -> bool {
        self.0 == ptr::null_mut()
    }

    pub unsafe fn dealloc(self) {
        let meta = &*(self.0 as *mut NodeMeta);
        let node_size = type_bits_to_node_size(meta.type_version_lock_obsolete.load(Relaxed) >> 62);
        let layout = Layout::from_size_align_unchecked(node_size, NODE_ALIGN);
        alloc::dealloc(self.0, layout);
    }

    unsafe fn meta_mut<'a>(self) -> &'a mut NodeMeta {
        &mut *(self.0 as *mut NodeMeta)
    }

    unsafe fn data_mut<'a, N: Node>(self) -> &'a mut N {
        &mut *(self.0.wrapping_add(META_LEN) as *mut N)
    }

    unsafe fn type_bits(self) -> u64 {
        self.meta_mut().type_version_lock_obsolete.load(Relaxed) & (0b11 << 62)
    }

    pub unsafe fn has_prefix(self) -> bool {
        let meta = &*(self.0 as *mut NodeMeta);
        meta.prefix_len > 0
    }

    pub unsafe fn prefix_len(self) -> usize {
        let meta = &*(self.0 as *mut NodeMeta);
        meta.prefix_len as usize
    }

    pub unsafe fn prefix_ptr(self) -> *mut u8 {
        let meta = &mut *(self.0 as *mut NodeMeta);
        meta.prefix.as_mut_ptr()
    }

    pub unsafe fn set_prefix(self, prefix: *const u8, prefix_len: usize) {
        let meta = self.meta_mut();
        if prefix_len > 0 {
            ptr::copy_nonoverlapping(
                prefix,
                meta.prefix.as_mut_ptr(),
                usize::min(prefix_len, MAX_STORED_PREFIX_LENGTH),
            );
            meta.prefix_len = prefix_len as u32;
        } else {
            meta.prefix_len = 0;
        }
    }

    pub fn is_leaf(self) -> bool {
        (self.0 as usize & MSB) == MSB
    }

    pub unsafe fn get_leaf(self) -> EntryPtr {
        EntryPtr((self.0 as usize & !MSB) as *mut u8)
    }

    pub unsafe fn read_lock(self) -> Result<u64, NeedRestart> {
        let type_version_lock_obsolete = self.meta_mut().type_version_lock_obsolete.load(SeqCst);
        if is_locked(type_version_lock_obsolete) || is_obsolete(type_version_lock_obsolete) {
            Err(NeedRestart)
        } else {
            Ok(type_version_lock_obsolete)
        }
    }

    pub unsafe fn read_unlock(self, version: u64) -> Result<(), NeedRestart> {
        if version == self.meta_mut().type_version_lock_obsolete.load(SeqCst) {
            Ok(())
        } else {
            Err(NeedRestart)
        }
    }

    pub unsafe fn write_lock(self) -> Result<(), NeedRestart> {
        let version = self.read_lock()?;
        self.upgrade_to_write_lock(version)?;
        Ok(())
    }

    pub unsafe fn upgrade_to_write_lock(self, version: u64) -> Result<u64, NeedRestart> {
        if let Ok(_) = self.meta_mut().type_version_lock_obsolete.compare_exchange(
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

    pub unsafe fn write_unlock(self) {
        self.meta_mut()
            .type_version_lock_obsolete
            .fetch_add(0b10, SeqCst);
    }

    pub unsafe fn write_unlock_obsolete(self) {
        self.meta_mut()
            .type_version_lock_obsolete
            .fetch_add(0b11, SeqCst);
    }

    pub unsafe fn check(self, start_read: u64) -> Result<(), NeedRestart> {
        self.read_unlock(start_read)
    }

    pub unsafe fn check_prefix(self, key: &[u8], mut level: usize) -> CheckPrefixResult {
        if self.has_prefix() {
            let prefix_len = self.prefix_len();
            if key.len() <= level + prefix_len {
                return CheckPrefixResult::NoMatch;
            }
            for i in 0..usize::min(prefix_len, MAX_STORED_PREFIX_LENGTH) {
                if *self.prefix_ptr().wrapping_add(i) != key[level] {
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

    pub unsafe fn check_prefix_pessimistic(
        self,
        key: &[u8],
        mut level: usize,
    ) -> Result<CheckPrefixPessimisticResult, NeedRestart> {
        if self.has_prefix() {
            let prev_level = level;
            let mut kt: *const u8 = ptr::null();
            for i in 0..self.prefix_len() {
                if i == MAX_STORED_PREFIX_LENGTH {
                    let entry = self.get_any_child_entry()?;
                    kt = entry.key().as_ptr();
                }
                let cur_key = if i >= MAX_STORED_PREFIX_LENGTH {
                    kt.wrapping_add(level).read()
                } else {
                    self.prefix_ptr().wrapping_add(i).read()
                };
                if cur_key != key[level] {
                    let non_matching_key = cur_key;
                    let mut remaining_prefix = Prefix::default();
                    if self.prefix_len() > MAX_STORED_PREFIX_LENGTH {
                        if i < MAX_STORED_PREFIX_LENGTH {
                            let entry = self.get_any_child_entry()?;
                            kt = entry.key().as_ptr();
                        }
                        ptr::copy_nonoverlapping(
                            kt.wrapping_add(level + 1),
                            remaining_prefix.as_mut_ptr(),
                            usize::min(
                                self.prefix_len() - (level - prev_level) - 1,
                                MAX_STORED_PREFIX_LENGTH,
                            ),
                        );
                    } else {
                        ptr::copy_nonoverlapping(
                            self.prefix_ptr().wrapping_add(i + 1),
                            remaining_prefix.as_mut_ptr(),
                            self.prefix_len() - i - 1,
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

    unsafe fn get_any_child_entry(self) -> Result<EntryPtr, NeedRestart> {
        let mut next_node = self;

        loop {
            let node = next_node;
            let version = node.read_lock()?;

            next_node = node.get_any_child();
            node.read_unlock(version)?;

            assert_ne!(next_node.0, ptr::null_mut());
            if next_node.is_leaf() {
                return Ok(next_node.get_leaf());
            }
        }
    }

    unsafe fn get_any_child(self) -> NodePtr {
        const VTABLE: [unsafe fn(NodePtr) -> NodePtr; 4] = [
            Node4::get_any_child,
            Node16::get_any_child,
            Node48::get_any_child,
            Node256::get_any_child,
        ];
        VTABLE[(self.type_bits() >> 62) as usize](self)
    }

    pub unsafe fn get_child(self, node_key: u8) -> NodePtr {
        const VTABLE: [unsafe fn(NodePtr, u8) -> NodePtr; 4] = [
            Node4::get_child,
            Node16::get_child,
            Node48::get_child,
            Node256::get_child,
        ];
        let type_bits = self.type_bits();
        VTABLE[(type_bits >> 62) as usize](self, node_key)
    }

    pub unsafe fn change(self, parent_key: u8, new_node: NodePtr) -> bool {
        const VTABLE: [unsafe fn(NodePtr, u8, NodePtr) -> bool; 4] = [
            Node4::change,
            Node16::change,
            Node48::change,
            Node256::change,
        ];
        VTABLE[(self.type_bits() >> 62) as usize](self, parent_key, new_node)
    }

    pub unsafe fn insert_and_unlock(
        self,
        version: u64,
        parent_node: NodePtr,
        parent_version: u64,
        parent_key: u8,
        key: u8,
        val: NodePtr,
        guard: &Guard,
    ) -> Result<(), NeedRestart> {
        match self.type_bits() {
            Node4::TYPE_BITS => Node4::insert_grow::<Node16>(
                self,
                version,
                parent_node,
                parent_version,
                parent_key,
                key,
                val,
                guard,
            ),
            Node16::TYPE_BITS => Node16::insert_grow::<Node48>(
                self,
                version,
                parent_node,
                parent_version,
                parent_key,
                key,
                val,
                guard,
            ),
            Node48::TYPE_BITS => Node48::insert_grow::<Node256>(
                self,
                version,
                parent_node,
                parent_version,
                parent_key,
                key,
                val,
                guard,
            ),
            Node256::TYPE_BITS => Node256::insert_grow::<Node256>(
                self,
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
}

#[derive(Copy, Clone)]
pub struct EntryPtr(*mut u8);

impl EntryPtr {
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

    pub unsafe fn dealloc<V>(self) {
        let ptr = self.0;
        let key_len = (ptr as *mut usize).read();
        let layout = Self::layout::<V>(key_len);
        alloc::dealloc(ptr, layout);
    }

    pub unsafe fn key<'a>(self) -> &'a [u8] {
        let ptr = self.0;
        let key_len = (ptr as *mut usize).read();
        slice::from_raw_parts_mut(ptr.wrapping_add(mem::size_of::<usize>()), key_len)
    }

    pub unsafe fn value_mut<'a, V>(self) -> &'a mut V {
        let ptr = self.0;
        let key_len = (ptr as *mut usize).read();
        let layout = Self::layout::<V>(key_len);
        let offset = layout.size() - mem::size_of::<V>();
        &mut *(ptr.wrapping_add(offset) as *mut V)
    }

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
        NodePtr((addr | MSB) as *mut u8)
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

    fn alloc() -> NodePtr {
        unsafe {
            let ptr = alloc::alloc_zeroed(Layout::from_size_align_unchecked(
                Self::node_size(),
                NODE_ALIGN,
            ));
            (ptr as *mut NodeMeta).write(NodeMeta::new(Self::TYPE_BITS));
            NodePtr(ptr)
        }
    }

    unsafe fn alloc_with_prefix(prefix: *const u8, prefix_len: usize) -> NodePtr {
        let ptr = Self::alloc();
        ptr.set_prefix(prefix, prefix_len);
        ptr
    }

    fn node_size() -> usize {
        mem::size_of::<NodeMeta>() + mem::size_of::<Self>()
    }

    unsafe fn insert(this: NodePtr, key: u8, child: NodePtr);

    unsafe fn get_any_child(this: NodePtr) -> NodePtr;

    unsafe fn get_child(this: NodePtr, node_key: u8) -> NodePtr;

    unsafe fn change(this: NodePtr, key: u8, new_node: NodePtr) -> bool;

    unsafe fn is_full(this: NodePtr) -> bool;

    unsafe fn is_under_full(this: NodePtr) -> bool;

    unsafe fn copy_to<Dst: Node>(this: NodePtr, dst: NodePtr);

    unsafe fn insert_grow<N: Node>(
        this: NodePtr,
        version: u64,
        parent_node: NodePtr,
        parent_version: u64,
        parent_key: u8,
        key: u8,
        val: NodePtr,
        guard: &Guard,
    ) -> Result<(), NeedRestart> {
        if !Self::is_full(this) {
            if !parent_node.is_null() {
                parent_node.read_unlock(parent_version)?;
            }
            this.upgrade_to_write_lock(version)?;
            Self::insert(this, key, val);
            this.write_unlock();
            return Ok(());
        }

        parent_node.upgrade_to_write_lock(parent_version)?;

        if let Err(restart) = this.upgrade_to_write_lock(version) {
            parent_node.write_unlock();
            return Err(restart);
        }

        let big_node = N::alloc_with_prefix(this.prefix_ptr(), this.prefix_len());
        Self::copy_to::<N>(this, big_node);
        N::insert(big_node, key, val);

        parent_node.change(parent_key, big_node);

        this.write_unlock_obsolete();
        guard.defer(move || {
            this.dealloc();
        });
        parent_node.write_unlock();
        Ok(())
    }
}

pub struct Node4 {
    keys: [u8; 4],
    children: [NodePtr; 4],
}

impl Node for Node4 {
    const TYPE_BITS: u64 = 0;

    unsafe fn insert(this: NodePtr, key: u8, child: NodePtr) {
        let count = this.meta_mut().count as usize;
        let node: &mut Self = this.data_mut();
        let mut pos = 0;
        while pos < count && node.keys[pos] < key {
            pos += 1;
        }
        node.keys.copy_within(pos..count, pos + 1);
        node.children.copy_within(pos..count, pos + 1);
        node.keys[pos] = key;
        node.children[pos] = child;
        this.meta_mut().count += 1;
    }
    unsafe fn get_any_child(this: NodePtr) -> NodePtr {
        let mut any_child = NodePtr::null();
        let count = this.meta_mut().count as usize;
        let data = this.data_mut::<Self>();
        for i in 0..count {
            if data.children[i].is_leaf() {
                return data.children[i];
            } else {
                any_child = data.children[i];
            }
        }
        any_child
    }
    unsafe fn get_child(this: NodePtr, node_key: u8) -> NodePtr {
        let count = this.meta_mut().count as usize;
        let data = this.data_mut::<Self>();
        for i in 0..count {
            if data.keys[i] == node_key {
                return data.children[i];
            }
        }
        NodePtr::null()
    }
    unsafe fn change(this: NodePtr, key: u8, new_node: NodePtr) -> bool {
        let count = this.meta_mut().count as usize;
        let data = this.data_mut::<Self>();
        for i in 0..count {
            if data.keys[i] == key {
                data.children[i] = new_node;
                return true;
            }
        }
        unreachable!()
    }
    unsafe fn is_full(this: NodePtr) -> bool {
        this.meta_mut().count == 4
    }
    unsafe fn is_under_full(_: NodePtr) -> bool {
        false
    }

    unsafe fn copy_to<Dst: Node>(this: NodePtr, dst: NodePtr) {
        let count = this.meta_mut().count as usize;
        let node = this.data_mut::<Self>();
        for i in 0..count {
            Dst::insert(dst, node.keys[i], node.children[i]);
        }
    }
}

pub struct Node16 {
    keys: [u8; 16],
    children: [NodePtr; 16],
}

impl Node16 {
    fn flip_sign(key_byte: u8) -> u8 {
        key_byte ^ 128
    }

    #[cfg(all(
        any(target_arch = "x86", target_arch = "x86_64"),
        target_feature = "sse2"
    ))]
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

    #[cfg(all(
        any(target_arch = "x86", target_arch = "x86_64"),
        target_feature = "sse2"
    ))]
    unsafe fn insert(this: NodePtr, key: u8, child: NodePtr) {
        #[cfg(target_arch = "x86")]
        use std::arch::x86::*;
        #[cfg(target_arch = "x86_64")]
        use std::arch::x86_64::*;

        let flipped = Self::flip_sign(key);
        let node: &mut Self = this.data_mut();
        let cmp = _mm_cmplt_epi8(
            _mm_set1_epi8(flipped as i8),
            _mm_loadu_si128(node.keys.as_ptr() as *const _),
        );
        let count = this.meta_mut().count as usize;
        let bitfield = _mm_movemask_epi8(cmp) & (0xFFFF >> (16 - count));
        let pos = if bitfield == 0 {
            count
        } else {
            bitfield.trailing_zeros() as usize
        };
        node.keys.copy_within(pos..count, pos + 1);
        node.children.copy_within(pos..count, pos + 1);
        node.keys[pos] = flipped;
        node.children[pos] = child;
        this.meta_mut().count += 1;
    }

    unsafe fn get_any_child(this: NodePtr) -> NodePtr {
        let count = this.meta_mut().count as usize;
        let data = this.data_mut::<Self>();
        for i in 0..count {
            if data.children[i].is_leaf() {
                return data.children[i];
            }
        }
        data.children[0]
    }
    unsafe fn get_child(this: NodePtr, node_key: u8) -> NodePtr {
        let count = this.meta_mut().count as usize;
        let data = this.data_mut::<Self>();
        if let Some(pos) = data.get_child_pos(node_key, count) {
            data.children[pos]
        } else {
            NodePtr::null()
        }
    }
    unsafe fn change(this: NodePtr, key: u8, new_node: NodePtr) -> bool {
        let count = this.meta_mut().count as usize;
        let data = this.data_mut::<Self>();
        let pos = data.get_child_pos(key, count).unwrap();
        data.children[pos] = new_node;
        true
    }
    unsafe fn is_full(this: NodePtr) -> bool {
        this.meta_mut().count == 16
    }
    unsafe fn is_under_full(this: NodePtr) -> bool {
        this.meta_mut().count == 3
    }
    unsafe fn copy_to<Dst: Node>(this: NodePtr, dst: NodePtr) {
        let count = this.meta_mut().count as usize;
        let node = this.data_mut::<Self>();
        for i in 0..count {
            Dst::insert(dst, Self::flip_sign(node.keys[i]), node.children[i]);
        }
    }
}

pub struct Node48 {
    child_index: [u8; 256],
    children: [NodePtr; 48],
}

impl Node48 {
    const EMPTY_MARKER: u8 = 48;
}

impl Node for Node48 {
    const TYPE_BITS: u64 = 2 << 62;

    fn alloc() -> NodePtr {
        unsafe {
            let ptr = alloc::alloc_zeroed(Layout::from_size_align_unchecked(
                Self::node_size(),
                NODE_ALIGN,
            ));
            (ptr as *mut NodeMeta).write(NodeMeta::new(Self::TYPE_BITS));
            let node = NodePtr(ptr);
            node.data_mut::<Self>().child_index = [Self::EMPTY_MARKER; 256];
            node
        }
    }

    unsafe fn insert(this: NodePtr, key: u8, child: NodePtr) {
        let mut pos = this.meta_mut().count as usize;
        let data = this.data_mut::<Self>();
        if !data.children[pos].is_null() {
            for i in 0..48 {
                if data.children[i].is_null() {
                    pos = i;
                    break;
                }
            }
        }
        data.children[pos] = child;
        data.child_index[key as usize] = pos as u8;
        this.meta_mut().count += 1;
    }
    unsafe fn get_any_child(this: NodePtr) -> NodePtr {
        let mut any_child = NodePtr::null();
        let data = this.data_mut::<Self>();
        for i in 0..=255 {
            let index = data.child_index[i];
            if index != Self::EMPTY_MARKER {
                let child = data.children[index as usize];
                if child.is_leaf() {
                    return child;
                } else {
                    any_child = child;
                }
            }
        }
        any_child
    }
    unsafe fn get_child(this: NodePtr, node_key: u8) -> NodePtr {
        let data = this.data_mut::<Self>();
        let index = data.child_index[node_key as usize];
        if index == Self::EMPTY_MARKER {
            NodePtr::null()
        } else {
            data.children[index as usize]
        }
    }
    unsafe fn change(this: NodePtr, key: u8, new_node: NodePtr) -> bool {
        let data = this.data_mut::<Self>();
        let index = data.child_index[key as usize] as usize;
        data.children[index] = new_node;
        true
    }
    unsafe fn is_full(this: NodePtr) -> bool {
        this.meta_mut().count == 48
    }
    unsafe fn is_under_full(this: NodePtr) -> bool {
        this.meta_mut().count == 12
    }
    unsafe fn copy_to<Dst: Node>(this: NodePtr, dst: NodePtr) {
        let data = this.data_mut::<Self>();
        for key in 0..256 {
            let idx = data.child_index[key];
            if idx != Self::EMPTY_MARKER {
                Dst::insert(dst, key as u8, data.children[idx as usize]);
            }
        }
    }
}

pub struct Node256 {
    children: [NodePtr; 256],
}

impl Node for Node256 {
    const TYPE_BITS: u64 = 3 << 62;

    unsafe fn insert(this: NodePtr, key: u8, child: NodePtr) {
        let data = this.data_mut::<Self>();
        data.children[key as usize] = child;
        this.meta_mut().count += 1;
    }
    unsafe fn get_any_child(this: NodePtr) -> NodePtr {
        let mut any_child = NodePtr::null();
        let data = this.data_mut::<Self>();
        for i in 0..=255 {
            let child = data.children[i];
            if !child.is_null() {
                if child.is_leaf() {
                    return child;
                } else {
                    any_child = child;
                }
            }
        }
        any_child
    }
    unsafe fn get_child(this: NodePtr, node_key: u8) -> NodePtr {
        let data = this.data_mut::<Self>();
        data.children[node_key as usize]
    }
    unsafe fn change(this: NodePtr, key: u8, new_node: NodePtr) -> bool {
        let data = this.data_mut::<Self>();
        data.children[key as usize] = new_node;
        true
    }
    unsafe fn is_full(_: NodePtr) -> bool {
        false
    }
    unsafe fn is_under_full(this: NodePtr) -> bool {
        this.meta_mut().count == 37
    }
    unsafe fn copy_to<Dst: Node>(this: NodePtr, dst: NodePtr) {
        let data = this.data_mut::<Self>();
        for i in 0..=255 {
            let node = data.children[i as usize];
            if !node.is_null() {
                Dst::insert(dst, i, node);
            }
        }
    }
}

fn type_bits_to_node_size(type_bits: u64) -> usize {
    match type_bits {
        Node4::TYPE_BITS => Node4::node_size(),
        Node16::TYPE_BITS => Node16::node_size(),
        Node48::TYPE_BITS => Node48::node_size(),
        Node256::TYPE_BITS => Node256::node_size(),
        _ => unreachable!(),
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
