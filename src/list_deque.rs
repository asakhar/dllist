use std::{
  cell::UnsafeCell,
  fmt::Debug,
  marker::{PhantomData, Unsize},
};

use self::implementation::{Node, NodePtr};

mod implementation {
  use std::marker::Unsize;

  #[derive(Clone, Copy, PartialEq, Eq)]
  pub struct NodePtr(u128);

  impl NodePtr {
    pub fn null() -> Self {
      Self(0)
    }
    pub fn is_null(&self) -> bool {
      self.0 == 0
    }
    pub fn is_not_null(&self) -> bool {
      self.0 != 0
    }
  }

  impl From<u128> for NodePtr {
    fn from(ptr: u128) -> Self {
      Self(ptr)
    }
  }

  impl From<u64> for NodePtr {
    fn from(ptr: u64) -> Self {
      Self(ptr as u128)
    }
  }

  impl From<u32> for NodePtr {
    fn from(ptr: u32) -> Self {
      Self(ptr as u128)
    }
  }

  pub struct Node<U: ?Sized> {
    pub next: NodePtr,
    pub prev: NodePtr,
    pub value: U,
  }

  impl<U: ?Sized> Node<U> {
    /// ## Safety requirements:
    /// - ptr must be aquired from Node::< U>::new<_>
    /// - ptr should point to memory that has not been currently dereferenced with other assosiated functions on Node (no exclusive or shared refs)
    pub unsafe fn from(ptr: NodePtr) -> Box<Node<U>> {
      // SAFETY: *mut Node<U> is either thin or wide ptr (64 or 128 bits respectivly).
      // So *mut Node<U> is always thinner or same as u128
      let node_ptr: *mut Node<U> = std::mem::transmute_copy(&ptr);
      Box::from_raw(node_ptr)
    }

    /// ## Safety requirements:
    /// - ptr must be aquired from Node::< U>::new<_>
    /// - ptr should point to memory that has not been currently dereferenced with other assosiated functions on Node (no exclusive or shared refs)
    pub unsafe fn mut_from<'a>(ptr: NodePtr) -> &'a mut Node<U> {
      std::mem::transmute_copy(&ptr)
    }

    /// ## Safety requirements:
    /// - ptr must be aquired from Node::< U>::new<_>
    /// - ptr should point to memory that has not been currently dereferenced with ownership taking or exclusive borrowing assosiated functions on Node
    pub unsafe fn ref_from<'a>(ptr: NodePtr) -> &'a Node<U> {
      std::mem::transmute_copy(&ptr)
    }

    pub fn new<T>(value: T, next: NodePtr, prev: NodePtr) -> NodePtr
    where
      T: Unsize<U>,
    {
      let node = Node::<T> { next, prev, value };
      let node_box = Box::new(node);
      let trait_box: Box<Node<U>> = node_box;
      let trait_ptr = Box::into_raw(trait_box);
      let size = std::mem::size_of_val(&trait_ptr);
      match size {
        4 => {
          // SAFETY: *mut Node<U> is thin ptr so in 32bit system it would fit in u32
          let tmp: u32 = unsafe { std::mem::transmute_copy(&trait_ptr) };
          tmp.into()
        }
        8 => {
          // SAFETY: *mut Node<U> is thin ptr so it would fit in u64
          let tmp: u64 = unsafe { std::mem::transmute_copy(&trait_ptr) };
          tmp.into()
        }
        // SAFETY: *mut Node<U> is wide ptr so it would fit in u128
        // in both cases ptr is always a valid uint
        16 => unsafe { std::mem::transmute_copy(&trait_ptr) },
        _ => unreachable!(),
      }
    }
  }
  impl<T> Node<T> {
    pub fn new_sized(value: T, next: NodePtr, prev: NodePtr) -> NodePtr {
      let node = Node::<T> { next, prev, value };
      let node_box = Box::new(node);
      let node_ptr = Box::into_raw(node_box);
      let size = std::mem::size_of_val(&node_ptr);
      match size {
        4 => {
          // SAFETY: *mut Node<T> is thin ptr so in 32bit system it would fit in u32
          let tmp: u32 = unsafe { std::mem::transmute_copy(&node_ptr) };
          tmp.into()
        }
        8 => {
          // SAFETY: *mut Node<T> is thin ptr so it would fit in u64
          let tmp: u64 = unsafe { std::mem::transmute_copy(&node_ptr) };
          tmp.into()
        }
        _ => unreachable!(),
      }
    }
  }
}
/// # Examples
/// ## Creation of ListDeque of trait objects and downcasting example
/// ```
/// use dllist::*;
/// trait AnyWrite: std::io::Write {
///   fn as_any(&self) -> &dyn std::any::Any;
/// }
///
/// impl AnyWrite for Vec<u8> {
///   fn as_any(&self) -> &dyn std::any::Any {
///     self
///   }
/// }
///
/// impl AnyWrite for std::fs::File {
///   fn as_any(&self) -> &dyn std::any::Any {
///     self
///   }
/// }
/// let buf1 = vec![0,1];
/// let buf2 = std::fs::File::create("/dev/null").unwrap();
/// let mut list: ListDeque<dyn AnyWrite> = deque![buf1, buf2];
///
/// let vector: &Vec<u8> = list.front()
///                            .unwrap()
///                            .as_any()
///                            .downcast_ref()
///                            .unwrap();
/// assert_eq!(vector[0], 0);
/// assert_eq!(vector[1], 1);
/// ```
/// ## Macro for constructing ListDeque and Debug format for ListDeque
/// ```
/// use dllist::*;
/// let mut list = deque_sized![1,2,3];
/// let item = list.back_mut().unwrap();
/// *item = 4;
/// assert_eq!(format!("{:?}", list), "[ 1, 2, 4, ]");
/// ```
/// ## Failes to compile: Consistency with borrowing rules (example 1)
/// ```compile_fail
/// use dllist::*;
/// let mut list = deque_sized![1,2,3];
/// let iter = list.iter();
/// list.push_back_sized(4);
/// for item in iter {
///   println!("{}", item);
/// }
/// ```
/// ## Failes to compile: Consistency with borrowing rules (example 2)
/// ```compile_fail
/// use dllist::*;
/// let mut list = deque_sized![1,2,3];
/// let item = list.peek_back_mut().unwrap();
/// println!("{:?}", list);
/// *item = 4;
/// ```
/// ## Failes to compile: ListDeque is not Sync
/// ```compile_fail
/// use dllist::*;
/// fn requires_sync<T: Sync>(_: T) {}
/// requires_sync(ListDeque::<i32>::new());
/// ```
/// ## However is Send (when U is Send of course)
/// ```
/// use dllist::*;
/// fn requires_send<T: Send>(_: T) {}
/// requires_send(ListDeque::<i32>::new());
/// ```
pub struct ListDeque<U: ?Sized> {
  begin: NodePtr,
  end: NodePtr,
  length: usize,
  // UnsafeCell is needed to unimplement Sync trait
  _phantom: PhantomData<UnsafeCell<U>>,
}

impl<U: ?Sized> ListDeque<U> {
  pub fn new() -> Self {
    Self {
      begin: NodePtr::null(),
      end: NodePtr::null(),
      length: 0,
      _phantom: Default::default(),
    }
  }

  pub fn drop_back(&mut self) -> Option<()> {
    let dropped = self.try_drop_last()?;
    if dropped.is_some() {
      return dropped;
    }
    // SAFETY: self.end is acquired from Node::<U>::new<T>()
    let end = unsafe { Node::<U>::from(self.end) };
    self.end = end.prev;
    if self.end.is_null() {
      return Some(());
    }
    // SAFETY: self.end is acquired from Node::<U>::new<T>()
    let mut end = unsafe { Node::<U>::mut_from(self.end) };
    end.next = NodePtr::null();
    Some(())
  }

  pub fn drop_front(&mut self) -> Option<()> {
    let dropped = self.try_drop_last()?;
    if dropped.is_some() {
      return dropped;
    }
    // SAFETY: self.begin is acquired from Node::<U>::new<T>()
    let begin = unsafe { Node::<U>::from(self.begin) };
    self.begin = begin.next;
    if self.begin.is_null() {
      return Some(());
    }
    // SAFETY: self.begin is acquired from Node::<U>::new<T>()
    let mut begin = unsafe { Node::<U>::mut_from(self.begin) };
    begin.prev = NodePtr::null();
    Some(())
  }

  pub fn size(&self) -> usize {
    self.length
  }

  pub fn back<'a>(&'a self) -> Option<&'a U> {
    if self.length == 0 {
      return None;
    }
    debug_assert!(self.begin.is_not_null() && self.end.is_not_null());
    // SAFETY: self.end is acquired from Node::<U>::new<T>()
    let end = unsafe { Node::<U>::ref_from(self.end) };
    Some(&end.value)
  }

  pub fn back_mut<'a>(&'a mut self) -> Option<&'a mut U> {
    if self.length == 0 {
      return None;
    }
    debug_assert!(self.begin.is_not_null() && self.end.is_not_null());
    // SAFETY: self.end is acquired from Node::<U>::new<T>()
    let end = unsafe { Node::<U>::mut_from(self.end) };
    Some(&mut end.value)
  }

  pub fn front<'a>(&'a self) -> Option<&'a U> {
    if self.length == 0 {
      return None;
    }
    debug_assert!(self.begin.is_not_null() && self.end.is_not_null());
    // SAFETY: self.begin is acquired from Node::<U>::new<T>()
    let begin = unsafe { Node::<U>::ref_from(self.begin) };
    Some(&begin.value)
  }

  pub fn front_mut<'a>(&'a mut self) -> Option<&'a mut U> {
    if self.length == 0 {
      return None;
    }
    debug_assert!(self.begin.is_not_null() && self.end.is_not_null());
    // SAFETY: self.begin is acquired from Node::<U>::new<T>()
    let begin = unsafe { Node::<U>::mut_from(self.begin) };
    Some(&mut begin.value)
  }

  pub fn push_back<T: Unsize<U>>(&mut self, value: T) {
    if let Some(value) = self.try_push_first(value) {
      let node = Node::<U>::new(value, NodePtr::null(), self.end);
      // SAFETY: self.end is acquired from Node::<U>::new<T>()
      let mut end = unsafe { Node::<U>::mut_from(self.end) };
      end.next = node;
      self.end = node;
    }
  }

  pub fn push_front<T: Unsize<U>>(&mut self, value: T) {
    if let Some(value) = self.try_push_first(value) {
      let node = Node::<U>::new(value, self.begin, NodePtr::null());
      // SAFETY: self.begin is acquired from Node::<U>::new<T>()
      let mut begin = unsafe { Node::<U>::mut_from(self.begin) };
      begin.prev = node;
      self.begin = node;
    }
  }

  pub fn iter<'a>(&'a self) -> Iter<'a, U> {
    Iter {
      begin: self.begin,
      end: self.end,
      remaining: self.length,
      _phantom: Default::default(),
    }
  }

  pub fn iter_mut<'a>(&'a mut self) -> IterMut<'a, U> {
    IterMut {
      begin: self.begin,
      end: self.end,
      remaining: self.length,
      _phantom: Default::default(),
    }
  }

  fn try_push_first<T: Unsize<U>>(&mut self, value: T) -> Option<T> {
    self.length += 1;
    if self.length != 1 {
      debug_assert!(self.begin.is_not_null() && self.end.is_not_null());
      return Some(value);
    }
    debug_assert!(self.begin.is_null() && self.end.is_null());
    let node = Node::<U>::new(value, NodePtr::null(), NodePtr::null());
    self.begin = node;
    self.end = node;
    return None;
  }

  fn try_drop_last(&mut self) -> Option<Option<()>> {
    self.length = self.length.checked_sub(1)?;
    debug_assert!(self.begin.is_not_null() && self.end.is_not_null());
    if self.length == 0 {
      // SAFETY: self.begin is acquired from Node::<U>::new<T>()
      let _ = unsafe { Node::<U>::from(self.begin) };
      self.begin = NodePtr::null();
      self.end = NodePtr::null();
      return Some(Some(()));
    }
    Some(None)
  }
}

impl<T> ListDeque<T> {
  pub fn push_back_sized(&mut self, value: T) {
    if let Some(value) = self.try_push_first_sized(value) {
      let node = Node::<T>::new_sized(value, NodePtr::null(), self.end);
      // SAFETY: self.end is acquired from Node::<U>::new<T>()
      let mut end = unsafe { Node::<T>::mut_from(self.end) };
      end.next = node;
      self.end = node;
    }
  }

  pub fn push_front_sized(&mut self, value: T) {
    if let Some(value) = self.try_push_first_sized(value) {
      let node = Node::<T>::new_sized(value, self.begin, NodePtr::null());
      // SAFETY: self.begin is acquired from Node::<U>::new<T>()
      let mut begin = unsafe { Node::<T>::mut_from(self.begin) };
      begin.prev = node;
      self.begin = node;
    }
  }

  pub fn pop_back(&mut self) -> Option<T> {
    let value = self.try_pop_last()?;
    if value.is_some() {
      return value;
    }
    // SAFETY: self.end is acquired from Node::<U>::new<T>()
    let end = unsafe { Node::<T>::from(self.end) };
    self.end = end.prev;
    let value = end.value;

    // SAFETY: self.end is acquired from Node::<U>::new<T>()
    let mut end = unsafe { Node::<T>::mut_from(self.end) };
    end.next = NodePtr::null();
    Some(value)
  }

  pub fn pop_front(&mut self) -> Option<T> {
    let value = self.try_pop_last()?;
    if value.is_some() {
      return value;
    }
    // SAFETY: self.begin is acquired from Node::<U>::new<T>()
    let begin = unsafe { Node::<T>::from(self.begin) };
    self.begin = begin.next;
    let value = begin.value;

    // SAFETY: self.begin is acquired from Node::<U>::new<T>()
    let mut begin = unsafe { Node::<T>::mut_from(self.begin) };
    begin.prev = NodePtr::null();
    Some(value)
  }

  fn try_push_first_sized(&mut self, value: T) -> Option<T> {
    self.length += 1;
    if self.length != 1 {
      debug_assert!(self.begin.is_not_null() && self.end.is_not_null());
      return Some(value);
    }
    debug_assert!(self.begin.is_null() && self.end.is_null());
    let node = Node::<T>::new_sized(value, NodePtr::null(), NodePtr::null());
    self.begin = node;
    self.end = node;
    return None;
  }

  fn try_pop_last(&mut self) -> Option<Option<T>> {
    self.length = self.length.checked_sub(1)?;
    debug_assert!(self.begin.is_not_null() && self.end.is_not_null());
    if self.length == 0 {
      // SAFETY: self.begin is acquired from Node::<U>::new<T>()
      let begin = unsafe { Node::<T>::from(self.begin) };
      self.begin = NodePtr::null();
      self.end = NodePtr::null();
      return Some(Some(begin.value));
    }
    Some(None)
  }
}

// SAFETY: ListDeque only have pointers to it's own data
unsafe impl<U: ?Sized + Send> Send for ListDeque<U> {}

impl<U: ?Sized> Drop for ListDeque<U> {
  fn drop(&mut self) {
    while self.drop_front().is_some() {}
    debug_assert!(self.begin.is_null() && self.end.is_null() && self.length == 0);
  }
}

pub struct Iter<'a, U: 'a + ?Sized> {
  begin: NodePtr,
  end: NodePtr,
  remaining: usize,
  _phantom: PhantomData<&'a ListDeque<U>>,
}

impl<'a, U: 'a + ?Sized> Iterator for Iter<'a, U> {
  type Item = &'a U;

  fn next(&mut self) -> Option<Self::Item> {
    self.remaining = self.remaining.checked_sub(1)?;
    debug_assert!(self.begin.is_not_null() && self.end.is_not_null());
    // SAFETY: self.begin is acquired from Node::<U>::new<T>()
    let begin = unsafe { Node::<U>::ref_from(self.begin) };
    let value = &begin.value;
    self.begin = begin.next;
    Some(value)
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.remaining, Some(self.remaining))
  }
}
impl<'a, U: 'a + ?Sized> DoubleEndedIterator for Iter<'a, U> {
  fn next_back(&mut self) -> Option<Self::Item> {
    self.remaining = self.remaining.checked_sub(1)?;
    debug_assert!(self.begin.is_not_null() && self.end.is_not_null());
    // SAFETY: self.end is acquired from Node::<U>::new<T>()
    let end = unsafe { Node::<U>::ref_from(self.end) };
    let value = &end.value;
    self.end = end.prev;
    Some(value)
  }
}

impl<'a, U: 'a + ?Sized> Clone for Iter<'a, U> {
  fn clone(&self) -> Self {
    Self {
      begin: self.begin,
      end: self.end,
      remaining: self.remaining,
      _phantom: Default::default(),
    }
  }
}

pub struct IterMut<'a, U: 'a + ?Sized> {
  begin: NodePtr,
  end: NodePtr,
  remaining: usize,
  _phantom: PhantomData<&'a mut ListDeque<U>>,
}

impl<'a, U: 'a + ?Sized> Iterator for IterMut<'a, U> {
  type Item = &'a mut U;

  fn next(&mut self) -> Option<Self::Item> {
    self.remaining = self.remaining.checked_sub(1)?;
    debug_assert!(self.begin.is_not_null() && self.end.is_not_null());
    // SAFETY: self.begin is acquired from Node::<U>::new<T>()
    let begin = unsafe { Node::<U>::mut_from(self.begin) };
    let value = &mut begin.value;
    self.begin = begin.next;
    Some(value)
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.remaining, Some(self.remaining))
  }
}

impl<'a, U: 'a + ?Sized> DoubleEndedIterator for IterMut<'a, U> {
  fn next_back(&mut self) -> Option<Self::Item> {
    self.remaining = self.remaining.checked_sub(1)?;
    debug_assert!(self.begin.is_not_null() && self.end.is_not_null());
    // SAFETY: self.end is acquired from Node::<U>::new<T>()
    let end = unsafe { Node::<U>::mut_from(self.end) };
    let value = &mut end.value;
    self.end = end.prev;
    Some(value)
  }
}

pub struct IntoIter<T> {
  begin: NodePtr,
  end: NodePtr,
  remaining: usize,
  _phantom: PhantomData<T>,
}

impl<T> Iterator for IntoIter<T> {
  type Item = T;

  fn next(&mut self) -> Option<Self::Item> {
    self.remaining = self.remaining.checked_sub(1)?;
    debug_assert!(self.begin.is_not_null() && self.end.is_not_null());
    // SAFETY: self.begin is acquired from Node::<U>::new<T>()
    let begin = unsafe { Node::<T>::from(self.begin) };
    let value = begin.value;
    self.begin = begin.next;
    Some(value)
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.remaining, Some(self.remaining))
  }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
  fn next_back(&mut self) -> Option<Self::Item> {
    self.remaining = self.remaining.checked_sub(1)?;
    debug_assert!(self.begin.is_not_null() && self.end.is_not_null());
    // SAFETY: self.end is acquired from Node::<U>::new<T>()
    let end = unsafe { Node::<T>::from(self.end) };
    let value = end.value;
    self.end = end.prev;
    Some(value)
  }
}

impl<T> IntoIterator for ListDeque<T> {
  type Item = T;

  type IntoIter = crate::list_deque::IntoIter<T>;

  fn into_iter(mut self) -> Self::IntoIter {
    let begin = self.begin;
    let end = self.end;
    let remaining = self.length;
    self.begin = NodePtr::null();
    self.end = NodePtr::null();
    self.length = 0;
    Self::IntoIter {
      begin,
      end,
      remaining,
      _phantom: Default::default(),
    }
  }
}

impl<T: Iterator> From<T> for ListDeque<T::Item> {
  fn from(it: T) -> Self {
    let mut list = ListDeque::new();
    for item in it {
      list.push_back_sized(item);
    }
    list
  }
}

impl<U: ?Sized + Debug> Debug for ListDeque<U> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.write_str("[ ")?;
    for item in self.iter() {
      f.write_fmt(format_args!("{:?}, ", item))?;
    }
    f.write_str("]")?;
    Ok(())
  }
}

#[cfg(feature = "negative_sized_trait")]
mod negative_sized_trait;

impl<T: Clone> Clone for ListDeque<T> {
  fn clone(&self) -> Self {
    self.iter().cloned().into()
  }
}
