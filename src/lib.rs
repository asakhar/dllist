#[macro_export]
macro_rules! list {
    ($($x:expr),*) => {
        {
            let mut new_list = crate::list::ListDeque::new();
            for item in [$($x),*] {
                new_list.push_back(item);
            }
            new_list
        }
    };
    ($elem:expr; $n:expr) => {
        {
            let mut new_list = list![];
            let size: usize = $n;
            let elem = $elem;
            for _ in 0..size {
                new_list.push_back(elem);
            }
            new_list
        }
    }
}

mod list {

    use std::{cell::UnsafeCell, fmt::Debug, marker::PhantomData};

    struct Node<T> {
        value: T,
        next: Option<Box<UnsafeCell<Node<T>>>>,
        prev: Option<*mut Node<T>>,
    }

    pub struct ListDeque<T> {
        begin: Option<Box<UnsafeCell<Node<T>>>>,
        end: Option<*mut Node<T>>,
        length: usize,
    }

    pub struct Iter<'a, T: 'a> {
        node_front: Option<*const Node<T>>,
        node_back: Option<*const Node<T>>,
        remaining: usize,
        phantom: PhantomData<&'a ListDeque<T>>,
    }

    impl<'a, T: 'a> Iterator for Iter<'a, T> {
        type Item = &'a T;

        fn next(&mut self) -> Option<Self::Item> {
            self.remaining = self.remaining.checked_sub(1)?;
            // SAFETY:
            //   pointer is:
            //     - given by UnsafeCell, which lifetime is at least 'a
            //     - non-null
            //     - previous mut ref defenetly expired
            let res = unsafe { &(*self.node_front.unwrap()).value };
            // SAFETY: same as previous
            self.node_front =
                unsafe { (*self.node_front.unwrap()).next.as_ref() }.map(|v| v.get() as *const _);
            Some(res)
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            (self.remaining, Some(self.remaining))
        }
    }

    impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
        fn next_back(&mut self) -> Option<Self::Item> {
            self.remaining = self.remaining.checked_sub(1)?;
            let res = unsafe { &(*self.node_back.unwrap()).value };
            self.node_back = unsafe { (*self.node_back.unwrap()).prev }.map(|v| v as *const _);
            Some(res)
        }
    }

    impl<'a, T: 'a> Clone for Iter<'a, T> {
        fn clone(&self) -> Self {
            Self {
                node_front: self.node_front.clone(),
                node_back: self.node_back.clone(),
                remaining: self.remaining,
                phantom: Default::default(),
            }
        }
    }

    pub struct IterMut<'a, T: 'a> {
        node_front: Option<*mut Node<T>>,
        node_back: Option<*mut Node<T>>,
        remaining: usize,
        phantom: PhantomData<&'a mut ListDeque<T>>,
    }

    impl<'a, T: 'a> Iterator for IterMut<'a, T> {
        type Item = &'a mut T;

        fn next(&mut self) -> Option<Self::Item> {
            self.remaining = self.remaining.checked_sub(1)?;
            // SAFETY:
            //   pointer is:
            //     - given by UnsafeCell, which lifetime is at least 'a
            //     - non-null
            //     - previous exclusive ref defenetly expired
            let next = unsafe { (*self.node_front.unwrap()).next.as_ref() }.map(|v| v.get());
            // SAFETY: same as previous due to expiration of previous exclusive borrow
            let res = unsafe { &mut (*self.node_front.unwrap()).value };
            self.node_front = next;
            Some(res)
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            (self.remaining, Some(self.remaining))
        }
    }

    impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
        fn next_back(&mut self) -> Option<Self::Item> {
            self.remaining = self.remaining.checked_sub(1)?;
            let res = unsafe { &mut (*self.node_back.unwrap()).value };
            self.node_back = unsafe { (*self.node_back.unwrap()).prev };
            Some(res)
        }
    }

    pub struct IntoIter<T> {
        first_node: Option<Box<UnsafeCell<Node<T>>>>,
        last_node: Option<*mut Node<T>>,
        remaining: usize,
    }

    impl<T> Iterator for IntoIter<T> {
        type Item = T;

        fn next(&mut self) -> Option<Self::Item> {
            self.remaining = self.remaining.checked_sub(1)?;
            let Node { value, next, .. } = self.first_node.take().unwrap().into_inner();
            self.first_node = next;
            Some(value)
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            (self.remaining, Some(self.remaining))
        }
    }

    impl<T> DoubleEndedIterator for IntoIter<T> {
        fn next_back(&mut self) -> Option<Self::Item> {
            self.remaining = self.remaining.checked_sub(1)?;
            self.last_node = unsafe { &mut *self.last_node.take().unwrap() }.prev;
            Some(
                if let Some(last_node) = self.last_node {
                    unsafe { &mut (*last_node).next }
                } else {
                    &mut self.first_node
                }
                .take()
                .unwrap()
                .into_inner()
                .value,
            )
        }
    }

    impl<T> ListDeque<T> {
        pub fn new() -> Self {
            Self {
                begin: None,
                end: None,
                length: 0,
            }
        }
        pub fn push_back(&mut self, value: T) {
            self.length += 1;
            if self.end.is_some() {
                assert!(self.begin.is_some());
                let new_preend = unsafe { &mut *self.end.take().unwrap() };
                new_preend.next = Some(Box::new(UnsafeCell::new(Node {
                    value,
                    next: None,
                    prev: Some(new_preend as *mut _),
                })));
                self.end = Some(new_preend.next.as_ref().unwrap().get());
                return;
            }
            self.push_first(value)
        }

        pub fn push_front(&mut self, value: T) {
            self.length += 1;
            if self.begin.is_some() {
                assert!(self.end.is_some());
                self.begin = Some(Box::new(UnsafeCell::new(Node {
                    value,
                    next: self.begin.take(),
                    prev: None,
                })));
                self.begin
                    .as_mut()
                    .unwrap()
                    .get_mut()
                    .next
                    .as_mut()
                    .unwrap()
                    .get_mut()
                    .prev = Some(self.begin.as_ref().unwrap().get());
                return;
            }
            self.push_first(value)
        }

        pub fn iter<'a>(&'a self) -> Iter<'a, T> {
            Iter {
                node_front: self.begin.as_ref().map(|v| v.get() as *const _),
                node_back: self.end.map(|v| v as *const _),
                remaining: self.size(),
                phantom: Default::default(),
            }
        }

        pub fn iter_mut<'a>(&'a mut self) -> IterMut<'a, T> {
            IterMut {
                node_front: self.begin.as_ref().map(|v| v.get()),
                node_back: self.end,
                remaining: self.size(),
                phantom: Default::default(),
            }
        }

        pub fn into_iter(mut self) -> IntoIter<T> {
            IntoIter {
                first_node: self.begin.take(),
                last_node: self.end.take(),
                remaining: self.size(),
            }
        }

        pub fn size(&self) -> usize {
            self.length
        }

        pub fn pop_back(&mut self) -> Option<T> {
            self.length = self.length.checked_sub(1)?;
            if self.length == 0 {
                return Some(self.pop_single());
            };

            let prev = unsafe { &mut *(*self.end.unwrap()).prev.unwrap() };
            let res = prev.next.take().unwrap();
            self.end = Some(prev as *mut _);
            Some(res.into_inner().value)
        }

        pub fn pop_front(&mut self) -> Option<T> {
            self.length = self.length.checked_sub(1)?;
            if self.length == 0 {
                return Some(self.pop_single());
            };

            let mut begin = self.begin.take().unwrap();
            self.begin = begin.get_mut().next.take();
            Some(begin.into_inner().value)
        }

        fn pop_single(&mut self) -> T {
            self.end.take();
            self.begin.take().unwrap().into_inner().value
        }

        fn push_first(&mut self, value: T) {
            debug_assert!(self.begin.is_none() && self.end.is_none());
            let node = Box::new(UnsafeCell::new(Node {
                value,
                next: None,
                prev: None,
            }));
            self.end = Some(node.get());
            self.begin = Some(node);
        }
    }

    impl<T: Debug> Debug for ListDeque<T> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let iter = self.iter();
            let last = iter.clone().last();
            let iter = iter.take(self.length.checked_sub(1).unwrap_or_default());
            for item in iter {
                f.write_fmt(format_args!("{:?} ", item))?;
            }
            if let Some(last) = last {
                f.write_fmt(format_args!("{:?}", last))?;
            }
            Ok(())
        }
    }

    unsafe impl<T: Send> Send for ListDeque<T> {}

    impl<T: Iterator> From<T> for ListDeque<T::Item> {
        fn from(it: T) -> Self {
            let mut list = list![];
            for item in it {
                list.push_back(item);
            }
            list
        }
    }

    impl<T: Clone> Clone for ListDeque<T> {
        fn clone(&self) -> Self {
            self.iter().cloned().into()
        }
    }
}

pub use list::ListDeque;

#[cfg(test)]
mod tests {
    use super::ListDeque;

    #[test]
    fn pushes() {
        let mut list = ListDeque::new();
        for i in 1..10 {
            list.push_back(i);
        }
        for i in 10..20 {
            list.push_front(i);
        }
        assert_eq!(
            format!("{:?}", list),
            "19 18 17 16 15 14 13 12 11 10 1 2 3 4 5 6 7 8 9"
        );
    }

    #[test]
    fn pops() {
        let mut list = ListDeque::new();
        for i in 1..10 {
            list.push_back(i);
        }
        for i in 10..20 {
            list.push_front(i);
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
        let list = list![1, 2, 3, 4];
        assert_eq!(format!("{:?}", list), "1 2 3 4");
        let list = list![33; 5];
        assert_eq!(format!("{:?}", list), "33 33 33 33 33");
    }

    #[test]
    fn iterators() {
        let list = list![1, 2, 3, 4, 5];
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
        assert_eq!(format!("{:?}", list), "10 11 12 13 14");
        for (i, item) in list.iter_mut().rev().enumerate() {
            *item = i + 10;
            j += 1;
        }
        assert_eq!(format!("{:?}", list), "14 13 12 11 10");
        let list_copy = list.clone();
        assert_eq!(format!("{:?}", list_copy), "14 13 12 11 10");
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

    // #[test]
    // fn borrowing_rules() {
    //     let mut list = List::new();
    //     list.push_back(0);
    //     let mut iter_mut = list.iter_mut();
    //     let mut iter = list.iter_mut();
    //     iter_mut.next();
    //     iter.next();
    // }
}
