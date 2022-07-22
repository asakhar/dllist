#![feature(unsize)]

#[macro_use]
pub mod list_deque {
  #[macro_export]
  macro_rules! deque_sized {
      ($($x:expr),*) => {
          {
              let mut new_list = ListDeque::new();
              for item in [$($x),*] {
                  new_list.push_back_sized(item);
              }
              new_list
          }
      };
      ($elem:expr; $n:expr) => {
          {
              let mut new_list = deque_sized![];
              let size: usize = $n;
              let elem = $elem;
              for _ in 0..size {
                  new_list.push_back_sized(elem);
              }
              new_list
          }
      };
  }

  #[macro_export]
  macro_rules! deque {
      ($($x:expr),*) => {
          {
              let mut new_list = ListDeque::new();
              for item in [$($x),*] {
                  new_list.push_back(item);
              }
              new_list
          }
      };
      ($elem:expr; $n:expr) => {
          {
              let mut new_list = list_deque![];
              let size: usize = $n;
              let elem = $elem;
              for _ in 0..size {
                  new_list.push_back(elem);
              }
              new_list
          }
      }
  }

  use std::{
    fmt::Debug,
    marker::{PhantomData, Unsize},
    mem::ManuallyDrop,
  };

  struct Node<U: ?Sized> {
    next: u128,
    prev: u128,
    value: U,
  }

  impl<U: ?Sized> Node<U> {
    /// ## Safety requirements:
    /// ptr must be aquired from Node::<U>::new<_>
    unsafe fn from(ptr: u128) -> ManuallyDrop<Box<Node<U>>> {
      // SAFETY: *mut Node<U> is either thin or wide ptr (64 or 128 bits respectivly).
      // So *mut Node<U> is always thinner or same as u128
      let node_ptr: *mut Node<U> = std::mem::transmute_copy(&ptr);
      ManuallyDrop::new(Box::from_raw(node_ptr))
    }

    /// ## Safety requirements:
    /// ptr must be aquired from Node::<U>::new<_>
    unsafe fn mut_from<'a>(ptr: u128) -> &'a mut Node<U> {
      Box::leak(ManuallyDrop::into_inner(Self::from(ptr)))
    }

    /// ## Safety requirements:
    /// ptr must be aquired from Node::<U>::new<_>
    unsafe fn ref_from<'a>(ptr: u128) -> &'a Node<U> {
      Box::leak(ManuallyDrop::into_inner(Self::from(ptr)))
    }

    fn new<T>(value: T, next: u128, prev: u128) -> u128
    where
      T: Unsize<U>,
    {
      let node = Node::<T> { next, prev, value };
      let node_box = Box::new(node);
      let trait_box: Box<Node<U>> = node_box;
      let trait_ptr = Box::into_raw(trait_box);
      let size = std::mem::size_of_val(&trait_ptr);
      match size {
        8 => {
          // SAFETY: *mut Node<U> is thin ptr so it would fit in u64
          let tmp: u64 = unsafe { std::mem::transmute_copy(&trait_ptr) };
          tmp as u128
        }
        // SAFETY: *mut Node<U> is wide ptr so it would fit in u128
        // in both cases ptr is always a valid uint
        16 => unsafe { std::mem::transmute_copy(&trait_ptr) },
        _ => unreachable!(),
      }
    }
  }
  impl<T> Node<T> {
    fn new_sized(value: T, next: u128, prev: u128) -> u128 {
      let node = Node::<T> { next, prev, value };
      let node_box = Box::new(node);
      let node_ptr = Box::into_raw(node_box);
      let size = std::mem::size_of_val(&node_ptr);
      match size {
        8 => {
          // SAFETY: *mut Node<U> is thin ptr so it would fit in u64
          let tmp: u64 = unsafe { std::mem::transmute_copy(&node_ptr) };
          tmp as u128
        }
        _ => unreachable!(),
      }
    }
  }

  /// ```
  /// use dllist::*;
  /// let mut list = deque_sized![1,2,3];
  /// let item = list.peek_back_mut().unwrap();
  /// *item = 4;
  /// assert_eq!(format!("{:?}", list), "[ 1, 2, 4, ]");
  /// ```
  /// ```compile_fail
  /// use dllist::*;
  /// let mut list = deque_sized![1,2,3];
  /// let iter = list.iter();
  /// list.push_back_sized(4);
  /// for item in iter {
  ///   println!("{}", item);
  /// }
  /// ```
  /// ```compile_fail
  /// use dllist::*;
  /// let mut list = deque_sized![1,2,3];
  /// let item = list.peek_back_mut().unwrap();
  /// println!("{:?}", list);
  /// *item = 4;
  /// ```
  pub struct ListDeque<U: ?Sized> {
    begin: u128,
    end: u128,
    length: usize,
    _phantom: PhantomData<U>,
  }

  impl<U: ?Sized> ListDeque<U> {
    pub fn new() -> Self {
      Self {
        begin: 0,
        end: 0,
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
      let end = ManuallyDrop::into_inner(unsafe { Node::<U>::from(self.end) });
      self.end = end.prev;
      if self.end == 0 {
        return Some(());
      }
      // SAFETY: self.end is acquired from Node::<U>::new<T>()
      let mut end = unsafe { Node::<U>::from(self.end) };
      end.next = 0;
      Some(())
    }

    pub fn drop_front(&mut self) -> Option<()> {
      let dropped = self.try_drop_last()?;
      if dropped.is_some() {
        return dropped;
      }
      // SAFETY: self.begin is acquired from Node::<U>::new<T>()
      let begin = ManuallyDrop::into_inner(unsafe { Node::<U>::from(self.begin) });
      self.begin = begin.next;
      if self.begin == 0 {
        return Some(());
      }
      // SAFETY: self.begin is acquired from Node::<U>::new<T>()
      let mut begin = unsafe { Node::<U>::from(self.begin) };
      begin.prev = 0;
      Some(())
    }

    pub fn size(&self) -> usize {
      self.length
    }

    pub fn peek_back<'a>(&'a self) -> Option<&'a U> {
      if self.length == 0 {
        return None;
      }
      debug_assert!(self.begin != 0 && self.end != 0);
      // SAFETY: self.end is acquired from Node::<U>::new<T>()
      let end = unsafe { Node::<U>::ref_from(self.end) };
      Some(&end.value)
    }

    pub fn peek_back_mut<'a>(&'a mut self) -> Option<&'a mut U> {
      if self.length == 0 {
        return None;
      }
      debug_assert!(self.begin != 0 && self.end != 0);
      // SAFETY: self.end is acquired from Node::<U>::new<T>()
      let end = unsafe { Node::<U>::mut_from(self.end) };
      Some(&mut end.value)
    }

    pub fn peek_front<'a>(&'a self) -> Option<&'a U> {
      if self.length == 0 {
        return None;
      }
      debug_assert!(self.begin != 0 && self.end != 0);
      // SAFETY: self.begin is acquired from Node::<U>::new<T>()
      let begin = unsafe { Node::<U>::ref_from(self.begin) };
      Some(&begin.value)
    }

    pub fn peek_front_mut<'a>(&'a mut self) -> Option<&'a mut U> {
      if self.length == 0 {
        return None;
      }
      debug_assert!(self.begin != 0 && self.end != 0);
      // SAFETY: self.begin is acquired from Node::<U>::new<T>()
      let begin = unsafe { Node::<U>::mut_from(self.begin) };
      Some(&mut begin.value)
    }

    pub fn push_back<T: Unsize<U>>(&mut self, value: T) {
      if let Some(value) = self.try_push_first(value) {
        let node = Node::<U>::new(value, 0, self.end);
        // SAFETY: self.end is acquired from Node::<U>::new<T>()
        let mut end = unsafe { Node::<U>::from(self.end) };
        end.next = node;
        self.end = node;
      }
    }

    pub fn push_front<T: Unsize<U>>(&mut self, value: T) {
      if let Some(value) = self.try_push_first(value) {
        let node = Node::<U>::new(value, self.begin, 0);
        // SAFETY: self.begin is acquired from Node::<U>::new<T>()
        let mut begin = unsafe { Node::<U>::from(self.begin) };
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
        debug_assert!(self.begin != 0 && self.end != 0);
        return Some(value);
      }
      debug_assert!(self.begin == 0 && self.end == 0);
      let node = Node::<U>::new(value, 0, 0);
      self.begin = node;
      self.end = node;
      return None;
    }

    fn try_drop_last(&mut self) -> Option<Option<()>> {
      self.length = self.length.checked_sub(1)?;
      debug_assert!(self.begin != 0 && self.end != 0);
      if self.length == 0 {
        // SAFETY: self.begin is acquired from Node::<U>::new<T>()
        let _ = ManuallyDrop::into_inner(unsafe { Node::<U>::from(self.begin) });
        self.begin = 0;
        self.end = 0;
        return Some(Some(()));
      }
      Some(None)
    }
  }

  impl<T> ListDeque<T> {
    pub fn push_back_sized(&mut self, value: T) {
      if let Some(value) = self.try_push_first_sized(value) {
        let node = Node::<T>::new_sized(value, 0, self.end);
        // SAFETY: self.end is acquired from Node::<U>::new<T>()
        let mut end = unsafe { Node::<T>::from(self.end) };
        end.next = node;
        self.end = node;
      }
    }

    pub fn push_front_sized(&mut self, value: T) {
      if let Some(value) = self.try_push_first_sized(value) {
        let node = Node::<T>::new_sized(value, self.begin, 0);
        // SAFETY: self.begin is acquired from Node::<U>::new<T>()
        let mut begin = unsafe { Node::<T>::from(self.begin) };
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
      let end = ManuallyDrop::into_inner(unsafe { Node::<T>::from(self.end) });
      self.end = end.prev;
      let value = end.value;

      // SAFETY: self.end is acquired from Node::<U>::new<T>()
      let mut end = unsafe { Node::<T>::from(self.end) };
      end.next = 0;
      Some(value)
    }

    pub fn pop_front(&mut self) -> Option<T> {
      let value = self.try_pop_last()?;
      if value.is_some() {
        return value;
      }
      // SAFETY: self.begin is acquired from Node::<U>::new<T>()
      let begin = ManuallyDrop::into_inner(unsafe { Node::<T>::from(self.begin) });
      self.begin = begin.next;
      let value = begin.value;

      // SAFETY: self.begin is acquired from Node::<U>::new<T>()
      let mut begin = unsafe { Node::<T>::from(self.begin) };
      begin.prev = 0;
      Some(value)
    }

    fn try_push_first_sized(&mut self, value: T) -> Option<T> {
      self.length += 1;
      if self.length != 1 {
        debug_assert!(self.begin != 0 && self.end != 0);
        return Some(value);
      }
      debug_assert!(self.begin == 0 && self.end == 0);
      let node = Node::<T>::new_sized(value, 0, 0);
      self.begin = node;
      self.end = node;
      return None;
    }

    fn try_pop_last(&mut self) -> Option<Option<T>> {
      self.length = self.length.checked_sub(1)?;
      debug_assert!(self.begin != 0 && self.end != 0);
      if self.length == 0 {
        // SAFETY: self.begin is acquired from Node::<U>::new<T>()
        let begin = ManuallyDrop::into_inner(unsafe { Node::<T>::from(self.begin) });
        self.begin = 0;
        self.end = 0;
        return Some(Some(begin.value));
      }
      Some(None)
    }
  }

  impl<U: ?Sized> Drop for ListDeque<U> {
    fn drop(&mut self) {
      while self.drop_front().is_some() {}
      debug_assert!(self.begin == 0 && self.end == 0 && self.length == 0);
    }
  }

  pub struct Iter<'a, U: 'a + ?Sized> {
    begin: u128,
    end: u128,
    remaining: usize,
    _phantom: PhantomData<&'a ListDeque<U>>,
  }

  impl<'a, U: 'a + ?Sized> Iterator for Iter<'a, U> {
    type Item = &'a U;

    fn next(&mut self) -> Option<Self::Item> {
      self.remaining = self.remaining.checked_sub(1)?;
      debug_assert!(self.begin != 0 && self.end != 0);
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
      debug_assert!(self.begin != 0 && self.end != 0);
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
    begin: u128,
    end: u128,
    remaining: usize,
    _phantom: PhantomData<&'a mut ListDeque<U>>,
  }

  impl<'a, U: 'a + ?Sized> Iterator for IterMut<'a, U> {
    type Item = &'a mut U;

    fn next(&mut self) -> Option<Self::Item> {
      self.remaining = self.remaining.checked_sub(1)?;
      debug_assert!(self.begin != 0 && self.end != 0);
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
      debug_assert!(self.begin != 0 && self.end != 0);
      // SAFETY: self.end is acquired from Node::<U>::new<T>()
      let end = unsafe { Node::<U>::mut_from(self.end) };
      let value = &mut end.value;
      self.end = end.prev;
      Some(value)
    }
  }

  pub struct IntoIter<T> {
    begin: u128,
    end: u128,
    remaining: usize,
    _phantom: PhantomData<T>,
  }

  impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
      self.remaining = self.remaining.checked_sub(1)?;
      debug_assert!(self.begin != 0 && self.end != 0);
      // SAFETY: self.begin is acquired from Node::<U>::new<T>()
      let begin = ManuallyDrop::into_inner(unsafe { Node::<T>::from(self.begin) });
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
      debug_assert!(self.begin != 0 && self.end != 0);
      // SAFETY: self.end is acquired from Node::<U>::new<T>()
      let end = ManuallyDrop::into_inner(unsafe { Node::<T>::from(self.end) });
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
      self.begin = 0;
      self.end = 0;
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
      let mut list = deque_sized![];
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
}

#[macro_use]
pub mod prelude {
  pub use crate::list_deque::*;
}

pub use list_deque::ListDeque;
#[cfg(test)]
mod tests {
  use std::{any::Any, io::Write};

  use crate::{deque_sized, list_deque::ListDeque};

  trait AnyWrite: Write {
    fn as_any(&self) -> &dyn Any;
  }

  impl AnyWrite for Vec<u8> {
    fn as_any(&self) -> &dyn Any {
      self
    }
  }

  #[test]
  fn unsized_test() {
    let mut list = ListDeque::<dyn AnyWrite>::new();

    assert_eq!(list.size(), 0);
    let buf1 = Vec::new();
    list.push_back(buf1);
    let buf2 = Vec::new();
    assert_eq!(list.size(), 1);
    list.push_back(buf2);
    assert_eq!(list.size(), 2);
    list.peek_back_mut().unwrap().write_all(b"b").unwrap();
    assert_eq!(list.size(), 2);
    list.peek_front_mut().unwrap().write_all(b"a").unwrap();
    assert_eq!(list.size(), 2);

    for (item, c) in list.iter().zip(b"ab") {
      let vector: &Vec<u8> = item.as_any().downcast_ref().unwrap();
      assert_eq!(vector[0], *c);
    }
    assert_eq!(list.size(), 2);
    assert_eq!(list.drop_front(), Some(()));
    assert_eq!(list.size(), 1);
    assert_eq!(list.drop_back(), Some(()));
    assert_eq!(list.size(), 0);
    assert_eq!(list.drop_front(), None);
    assert_eq!(list.size(), 0);
    assert_eq!(list.drop_back(), None);
    assert_eq!(list.size(), 0);
  }

  #[test]
  fn pushes() {
    let mut list = ListDeque::new();
    for i in 1..10 {
      list.push_back_sized(i);
    }
    for i in 10..20 {
      list.push_front_sized(i);
    }
    assert_eq!(
      format!("{:?}", list),
      "[ 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, ]"
    );
  }

  #[test]
  fn pops() {
    let mut list = ListDeque::new();
    for i in 1..10 {
      list.push_back_sized(i);
    }
    for i in 10..20 {
      list.push_front_sized(i);
    }
    for i in (1..10).rev() {
      assert_eq!(list.pop_back(), Some(i));
    }
    for i in (10..20).rev() {
      assert_eq!(list.pop_front(), Some(i));
    }
    assert_eq!(list.size(), 0);
    assert_eq!(list.pop_front(), None);
    assert_eq!(list.pop_back(), None);
  }

  #[test]
  fn macro_test() {
    let list = deque_sized![1, 2, 3, 4];
    assert_eq!(format!("{:?}", list), "[ 1, 2, 3, 4, ]");
    let list = deque_sized![33; 5];
    assert_eq!(format!("{:?}", list), "[ 33, 33, 33, 33, 33, ]");
  }

  #[test]
  fn iterators() {
    let list = deque_sized![1, 2, 3, 4, 5];
    let mut j = 0;
    for (i, item) in list.iter().enumerate() {
      assert_eq!(*item, i + 1);
      j += 1;
    }
    for (i, item) in list.iter().rev().enumerate() {
      assert_eq!(*item, 5 - i);
      j += 1;
    }
    let mut list = list;
    for (i, item) in list.iter_mut().enumerate() {
      *item = i + 10;
      j += 1;
    }
    assert_eq!(format!("{:?}", list), "[ 10, 11, 12, 13, 14, ]");
    for (i, item) in list.iter_mut().rev().enumerate() {
      *item = i + 10;
      j += 1;
    }
    assert_eq!(format!("{:?}", list), "[ 14, 13, 12, 11, 10, ]");
    let list_copy = list.clone();
    assert_eq!(format!("{:?}", list_copy), "[ 14, 13, 12, 11, 10, ]");
    for (i, item) in list.into_iter().enumerate() {
      assert_eq!(item, 14 - i);
      j += 1;
    }
    for (i, item) in list_copy.into_iter().rev().enumerate() {
      assert_eq!(item, i + 10);
      j += 1;
    }
    assert_eq!(j, 30);
  }
}
