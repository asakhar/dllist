use std::{
  any::Any,
  collections::VecDeque,
  io::{Read, Seek, SeekFrom, Write},
};

macro_rules! deque_sized {
  ($($x:expr),*) => {
{
  let mut new_list = crate::ListDeque::new();
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

macro_rules! deque_insertion_helper {
($deq:ident, $x:expr) => {
  $deq.push_back($x);
};
($deq:ident, $x:expr, $($y:expr),*) => {
  {
    $deq.push_back($x);
    deque_insertion_helper!($deq, $($y),*);
  }
}
  }

macro_rules! deque {
  ($($x:expr),*) => {
{
  let mut new_list = crate::ListDeque::new();
  deque_insertion_helper!(new_list, $($x),*);
  new_list
}
  };
  ($elem:expr; $n:expr) => {
{
  let mut new_list = deque![];
  let size: usize = $n;
  let elem = $elem;
  for _ in 0..size {
    new_list.push_back(elem);
  }
  new_list
}
  }
}

use rand::distributions::Uniform;

use crate::list_deque::ListDeque;

trait AnyWrite: Write {
  fn as_any(&self) -> &dyn Any;
  fn as_mut_any(&mut self) -> &mut dyn Any;
}

impl AnyWrite for Vec<u8> {
  fn as_any(&self) -> &dyn Any {
    self
  }
  fn as_mut_any(&mut self) -> &mut dyn Any {
    self
  }
}

impl AnyWrite for std::fs::File {
  fn as_any(&self) -> &dyn Any {
    self
  }
  fn as_mut_any(&mut self) -> &mut dyn Any {
    self
  }
}

#[test]
fn macro_unsized() {
  let buf1: Vec<u8> = Vec::new();
  let buf2 = std::fs::File::options()
    .create(true)
    .read(true)
    .write(true)
    .open("a")
    .unwrap();
  let mut list: ListDeque<dyn AnyWrite> = deque![buf1, buf2];
  assert_eq!(list.size(), 2);
  list.back_mut().unwrap().write_all(b"b").unwrap();
  assert_eq!(list.size(), 2);
  list.front_mut().unwrap().write_all(b"a").unwrap();
  assert_eq!(list.size(), 2);

  for (item, c) in list.iter_mut().zip(b"ab") {
    if let Some(vector) = item.as_any().downcast_ref::<Vec<u8>>() {
      assert_eq!(vector[0], *c);
    } else if let Some(mut file) = item.as_mut_any().downcast_ref::<std::fs::File>() {
      let mut buf = [0u8; 1];
      file.seek(SeekFrom::Start(0)).unwrap();
      file.read_exact(&mut buf).unwrap();
      assert_eq!(buf[0], *c);
      std::fs::remove_file("a").unwrap();
    } else {
      panic!("ListDeque contains only vector and file");
    }
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
fn unsized_test() {
  let mut list = ListDeque::<dyn AnyWrite>::new();

  assert_eq!(list.size(), 0);
  let buf1 = Vec::new();
  list.push_back(buf1);
  let buf2 = Vec::new();
  assert_eq!(list.size(), 1);
  list.push_back(buf2);
  assert_eq!(list.size(), 2);
  list.back_mut().unwrap().write_all(b"b").unwrap();
  assert_eq!(list.size(), 2);
  list.front_mut().unwrap().write_all(b"a").unwrap();
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

#[test]
fn fuzz() {
  let mut deque = ListDeque::new();
  let mut refer = VecDeque::new();
  use rand::prelude::*;
  let actions = rand::thread_rng().sample_iter(Uniform::new(0, 6));
  for i in actions.take(1000000) {
    match i {
      0 => {
        let val = rand::thread_rng().next_u64();
        deque.push_front_sized(val);
        refer.push_front(val);
      }
      1 => {
        let val = rand::thread_rng().next_u64();
        deque.push_back_sized(val);
        refer.push_back(val);
      }
      2 => {
        assert_eq!(deque.front().cloned(), refer.front().cloned());
      }
      3 => {
        assert_eq!(deque.back().cloned(), refer.back().cloned());
      }
      4 => {
        assert_eq!(deque.pop_front(), refer.pop_front());
      }
      5 => {
        assert_eq!(deque.pop_back(), refer.pop_back());
      }
      _ => unreachable!(),
    }
  }
}
