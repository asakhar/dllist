use std::marker::Unsize;

use crate::ListDeque;

impl<T: Iterator, U /* : !Sized */> From<T> for ListDeque<U>
where
  T::Item: Unsize<U>,
{
  fn from(it: T) -> Self {
    let mut list = crate::ListDeque::new();
    for item in it {
      list.push_back_sized(item);
    }
    list
  }
}
