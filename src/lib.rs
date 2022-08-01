#![feature(unsize)]

#[macro_export]
macro_rules! deque_sized {
  ($($x:expr),*) => {
    {
      let mut new_list = dllist::ListDeque::new();
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

#[macro_export]
macro_rules! deque {
  ($($x:expr),*) => {
    {
      let mut new_list = dllist::ListDeque::new();
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

pub mod list_deque;

#[macro_use]
pub mod prelude;

pub use list_deque::ListDeque;
#[cfg(test)]
mod tests;
