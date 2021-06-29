//! This crate provides a const-size queue-like data structure. When full, pushing new items will
//! remove the head (first-added) items.
//!
//! ```toml
//! [dependencies]
//! lobby-queue = "0.2"
//! ```
//!
//! ```
//! use lobby_queue::Lobby;
//!
//! let mut m = Lobby::new([None, None, None]);
//!
//! m.push(0);
//! m.push(1);
//! m.push(2);
//! assert_eq!(Some(&0), m.first());
//!
//! let v0 = m.push(3);
//! assert_eq!(Some(0), v0);
//! assert_eq!(Some(&1), m.first());
//!
//! for v in m {
//!     println!("{}", v);
//! }
//! ```

pub mod iter;

use crate::iter::{IntoIter, Iter, IterMut};

use std::mem;

/// A const-size queue-like data structure.
#[derive(Debug, Clone)]
pub struct Lobby<T, const N: usize> {
    arr: [Option<T>; N],

    head: usize,
    tail: usize,

    len: usize,
}

impl<T, const N: usize> Lobby<T, N> {
    /// Create a new Lobby. The caller **must** pass in an array of all [`None`].
    ///
    /// # Limitation
    ///
    /// Until some workaround/fix for [#44796](https://github.com/rust-lang/rust/issues/44796)
    /// becomes available, an initial array must be passed in.
    ///
    /// ```
    /// use lobby_queue::Lobby;
    ///
    /// let mut lobby = Lobby::new([None, None, None, None]);
    /// lobby.push(0);
    /// ```
    #[inline]
    pub const fn new(arr: [Option<T>; N]) -> Self {
        Self {
            arr,
            head: 0,
            tail: 0,
            len: 0,
        }
    }

    /// Get the head item.
    ///
    /// ```
    /// use lobby_queue::Lobby;
    ///
    /// let mut lobby = Lobby::new([None, None, None]);
    /// assert_eq!(None, lobby.first());
    ///
    /// lobby.push(0);
    /// assert_eq!(Some(&0), lobby.first());
    ///
    /// lobby.push(1);
    /// assert_eq!(Some(&0), lobby.first());
    /// ```
    #[inline]
    pub const fn first(&self) -> Option<&T> {
        self.arr[self.head].as_ref()
    }

    /// Get a mutable reference to the head item. See [`Self::first`].
    #[inline]
    pub fn first_mut(&mut self) -> Option<&mut T> {
        self.arr[self.head].as_mut()
    }

    /// Get the tail item.
    ///
    /// ```
    /// use lobby_queue::Lobby;
    ///
    /// let mut lobby = Lobby::new([None, None, None]);
    /// assert_eq!(None, lobby.last());
    ///
    /// lobby.push(0);
    /// assert_eq!(Some(&0), lobby.last());
    ///
    /// lobby.push(1);
    /// assert_eq!(Some(&1), lobby.last());
    /// ```
    #[inline]
    pub const fn last(&self) -> Option<&T> {
        self.arr[self.tail].as_ref()
    }

    /// Get a mutable reference to the head item. See [`Self::last`].
    #[inline]
    pub fn last_mut(&mut self) -> Option<&mut T> {
        self.arr[self.tail].as_mut()
    }

    /// Get the nth item.
    ///
    /// ```
    /// use lobby_queue::Lobby;
    ///
    /// let mut lobby = Lobby::new([None, None, None]);
    /// assert_eq!(None, lobby.nth(1));
    ///
    /// lobby.push(0);
    /// assert_eq!(None, lobby.nth(1));
    ///
    /// lobby.push(1);
    /// assert_eq!(Some(&1), lobby.nth(1));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `n` is greater than or equal to `N`.
    ///
    /// ```should_panic
    /// use lobby_queue::Lobby;
    ///
    /// let mut lobby = Lobby::new([None, None, None]);
    /// lobby.push(0);
    ///
    /// let _ = lobby.nth(3);
    /// ```
    #[inline]
    pub const fn nth(&self, n: usize) -> Option<&T> {
        let idx = if n >= N {
            N
        } else {
            Self::mod_incr(self.head, n)
        };

        self.arr[idx].as_ref()
    }

    /// Get a mutable reference to the nth item. See [`Self::nth`].
    ///
    /// ```
    /// use lobby_queue::Lobby;
    ///
    /// let mut lobby = Lobby::new([None, None, None]);
    ///
    /// lobby.push(0);
    /// lobby.push(1);
    ///
    /// let v1 = lobby.nth_mut(1).unwrap();
    /// *v1 = 3;
    ///
    /// assert_eq!(Some(&3), lobby.nth(1));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics under the same conditions as [`Self::nth`].
    #[inline]
    pub fn nth_mut(&mut self, n: usize) -> Option<&mut T> {
        let idx = if n >= N {
            N
        } else {
            Self::mod_incr(self.head, n)
        };

        self.arr[idx].as_mut()
    }

    /// Push a new item to the lobby, returning the head if the lobby is currently full.
    ///
    /// ```
    /// use lobby_queue::Lobby;
    ///
    /// let mut lobby = Lobby::new([None, None, None]);
    ///
    /// lobby.push(0);
    /// assert_eq!(Some(&0), lobby.first());
    ///
    /// lobby.push(1);
    /// assert_eq!(Some(&0), lobby.first());
    ///
    /// lobby.push(2);
    /// assert_eq!(Some(&0), lobby.first());
    ///
    /// lobby.push(3);
    /// assert_eq!(Some(&1), lobby.first());
    /// ```
    #[inline]
    pub fn push(&mut self, v: T) -> Option<T> {
        if self.arr[self.tail].is_some() {
            // Increment tail position to insert at next spot.
            self.tail = Self::mod_incr(self.tail, 1);
        }

        // Make push.
        let mut v = Some(v);
        mem::swap(&mut v, &mut self.arr[self.tail]);

        // Head position should be moved if the new element overrides an old.
        if v.is_some() {
            self.head = Self::mod_incr(self.head, 1);
        } else {
            self.len += 1;
        }

        v
    }

    /// Shift out the head item from the lobby.
    ///
    /// ```
    /// use lobby_queue::Lobby;
    ///
    /// let mut lobby = Lobby::new([None, None, None]);
    /// lobby.push(0);
    /// lobby.push(1);
    /// lobby.push(2);
    ///
    /// assert_eq!(Some(0), lobby.shift());
    /// assert_eq!(Some(1), lobby.shift());
    /// assert_eq!(Some(2), lobby.shift());
    /// assert_eq!(None, lobby.shift());
    /// ```
    #[inline]
    pub fn shift(&mut self) -> Option<T> {
        let mut v = None;
        mem::swap(&mut v, &mut self.arr[self.head]);

        let next = Self::mod_incr(self.head, 1);
        if self.arr[next].is_some() {
            self.head = next;
        }

        if v.is_some() {
            self.len -= 1;
        }

        v
    }

    /// Pop off the tail item from the lobby.
    ///
    /// ```
    /// use lobby_queue::Lobby;
    ///
    /// let mut lobby = Lobby::new([None, None, None]);
    /// lobby.push(0);
    /// lobby.push(1);
    /// lobby.push(2);
    ///
    /// assert_eq!(Some(2), lobby.pop());
    /// assert_eq!(Some(1), lobby.pop());
    /// assert_eq!(Some(0), lobby.pop());
    /// assert_eq!(None, lobby.pop());
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        let mut v = None;
        mem::swap(&mut v, &mut self.arr[self.tail]);

        let prev = Self::mod_decr(self.tail, 1);
        if self.arr[prev].is_some() {
            self.tail = prev;
        }

        if v.is_some() {
            self.len -= 1;
        }

        v
    }

    /// Returns `true` if the Lobby is empty, `false` if it is not.
    ///
    /// ```
    /// use lobby_queue::Lobby;
    ///
    /// let mut lobby = Lobby::new([None, None, None]);
    /// assert!(lobby.is_empty());
    ///
    /// lobby.push(0);
    /// assert!(!lobby.is_empty());
    ///
    /// lobby.shift();
    /// assert!(lobby.is_empty());
    /// ```
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns `true` if the Lobby is full, `false` if it is not.
    ///
    /// ```
    /// use lobby_queue::Lobby;
    ///
    /// let mut lobby = Lobby::new([None, None, None]);
    /// assert!(!lobby.is_full());
    ///
    /// lobby.push(0);
    /// assert!(!lobby.is_full());
    ///
    /// lobby.push(1);
    /// assert!(!lobby.is_full());
    ///
    /// lobby.push(2);
    /// assert!(lobby.is_full());
    /// ```
    #[inline]
    pub const fn is_full(&self) -> bool {
        Self::mod_incr(self.tail, 1) == self.head
    }

    /// Returns the current number of items stored in the lobby.
    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns the capacity of the lobby, which will always be `N`.
    #[inline]
    pub const fn capacity(&self) -> usize {
        N
    }

    #[inline]
    const fn mod_incr(counter: usize, d: usize) -> usize {
        (counter + d) % N
    }

    #[inline]
    const fn mod_decr(counter: usize, d: usize) -> usize {
        let d = d % N;
        if counter >= d {
            counter - d
        } else {
            counter + N - d
        }
    }
}

impl<T, const N: usize> PartialEq<Lobby<T, N>> for Lobby<T, N>
where
    T: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Lobby<T, N>) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<T, const N: usize> PartialEq<[Option<T>; N]> for Lobby<T, N>
where
    T: PartialEq,
{
    #[inline]
    fn eq(&self, other: &[Option<T>; N]) -> bool {
        self.iter().with_full().eq(other.iter().map(|v| v.as_ref()))
    }
}

impl<T, const N: usize> Lobby<T, N> {
    /// Returns an iterator over the items in the lobby.
    #[inline]
    pub fn iter(&self) -> Iter<'_, T, N> {
        Iter::new(self)
    }

    /// Returns an iterator that allows modifying each value.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, T, N> {
        IterMut::new(self)
    }
}

impl<T, const N: usize> IntoIterator for Lobby<T, N> {
    type Item = T;
    type IntoIter = IntoIter<T, N>;

    #[inline]
    fn into_iter(self) -> IntoIter<T, N> {
        IntoIter::new(self)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_push() {
        let mut x = Lobby::new([None, None, None]);

        x.push(0);
        assert_eq!([Some(0), None, None], x.arr);
        assert_eq!((0, 0), (x.head, x.tail));
        assert_eq!(1, x.len());

        x.push(1);
        assert_eq!([Some(0), Some(1), None], x.arr);
        assert_eq!((0, 1), (x.head, x.tail));
        assert_eq!(2, x.len());

        x.push(2);
        assert_eq!([Some(0), Some(1), Some(2)], x.arr);
        assert_eq!((0, 2), (x.head, x.tail));
        assert_eq!(3, x.len());

        let v0 = x.push(3);
        assert_eq!(Some(0), v0);
        assert_eq!([Some(3), Some(1), Some(2)], x.arr);
        assert_eq!((1, 0), (x.head, x.tail));
        assert_eq!(3, x.len());

        let v1 = x.push(4);
        assert_eq!(Some(1), v1);
        assert_eq!([Some(3), Some(4), Some(2)], x.arr);
        assert_eq!((2, 1), (x.head, x.tail));
        assert_eq!(3, x.len());
    }

    #[test]
    fn test_shift() {
        let mut x = Lobby::new([None, None, None]);
        x.push(0);
        x.push(1);
        x.push(2);

        assert_eq!([Some(0), Some(1), Some(2)], x.arr);
        assert_eq!((0, 2), (x.head, x.tail));
        assert_eq!(3, x.len());

        let v0 = x.shift();
        assert_eq!(Some(0), v0);
        assert_eq!([None, Some(1), Some(2)], x.arr);
        assert_eq!((1, 2), (x.head, x.tail));
        assert_eq!(2, x.len());

        let v1 = x.shift();
        assert_eq!(Some(1), v1);
        assert_eq!([None, None, Some(2)], x.arr);
        assert_eq!((2, 2), (x.head, x.tail));
        assert_eq!(1, x.len());

        let v2 = x.shift();
        assert_eq!(Some(2), v2);
        assert_eq!([None, None, None], x.arr);
        assert_eq!((2, 2), (x.head, x.tail));
        assert_eq!(0, x.len());

        let ve = x.shift();
        assert_eq!(None, ve);
        assert_eq!([None, None, None], x.arr);
        assert_eq!((2, 2), (x.head, x.tail));
        assert_eq!(0, x.len());
    }

    #[test]
    fn test_pop() {
        let mut x = Lobby::new([None, None, None]);
        x.push(0);
        x.push(1);
        x.push(2);

        assert_eq!([Some(0), Some(1), Some(2)], x.arr);
        assert_eq!((0, 2), (x.head, x.tail));
        assert_eq!(3, x.len());

        let v2 = x.pop();
        assert_eq!(Some(2), v2);
        assert_eq!([Some(0), Some(1), None], x.arr);
        assert_eq!((0, 1), (x.head, x.tail));
        assert_eq!(2, x.len());

        let v1 = x.pop();
        assert_eq!(Some(1), v1);
        assert_eq!([Some(0), None, None], x.arr);
        assert_eq!((0, 0), (x.head, x.tail));
        assert_eq!(1, x.len());

        let v0 = x.pop();
        assert_eq!(Some(0), v0);
        assert_eq!([None, None, None], x.arr);
        assert_eq!((0, 0), (x.head, x.tail));
        assert_eq!(0, x.len());

        let ve = x.pop();
        assert_eq!(None, ve);
        assert_eq!([None, None, None], x.arr);
        assert_eq!((0, 0), (x.head, x.tail));
        assert_eq!(0, x.len());
    }

    #[test]
    fn test_is_empty() {
        let mut x = Lobby::new([None, None, None]);
        assert!(x.is_empty());

        // [0, _, _]
        x.push(0);
        assert!(!x.is_empty());

        // [0, 1, _]
        x.push(1);
        assert!(!x.is_empty());

        // [0, 1, 2]
        x.push(2);
        assert!(!x.is_empty());

        // [3, 1, 2]
        x.push(3);
        assert!(!x.is_empty());

        // [3, _, 2]
        x.shift();
        assert!(!x.is_empty());

        // [3, _, 2]
        x.shift();
        assert!(!x.is_empty());

        // [_, _, _]
        x.shift();
        assert!(x.is_empty());
    }

    #[test]
    fn test_is_full() {
        let mut x = Lobby::new([None, None, None]);
        assert!(!x.is_full());

        // [0, _, _]
        x.push(0);
        assert!(!x.is_full());

        // [0, 1, _]
        x.push(1);
        assert!(!x.is_full());

        // [0, 1, 2]
        x.push(2);
        assert!(x.is_full());

        // [3, 1, 2]
        x.push(3);
        assert!(x.is_full());

        // [3, _, 2]
        x.shift();
        assert!(!x.is_full());

        // [3, _, 2]
        x.shift();
        assert!(!x.is_full());

        // [_, _, _]
        x.shift();
        assert!(!x.is_full());
    }

    #[test]
    fn test_increase_counter() {
        type L = Lobby<usize, 4>;

        let x = 0;
        assert_eq!(1, L::mod_incr(x, 1));
        assert_eq!(2, L::mod_incr(x, 2));
        assert_eq!(3, L::mod_incr(x, 3));
        assert_eq!(0, L::mod_incr(x, 4));
        assert_eq!(1, L::mod_incr(x, 5));
        assert_eq!(0, L::mod_incr(x, 8));
        assert_eq!(1, L::mod_incr(x, 9));
    }

    #[test]
    fn test_decrease_counter() {
        type L = Lobby<usize, 4>;

        let x = 2;
        assert_eq!(1, L::mod_decr(x, 1));
        assert_eq!(0, L::mod_decr(x, 2));
        assert_eq!(3, L::mod_decr(x, 3));
        assert_eq!(2, L::mod_decr(x, 4));
        assert_eq!(1, L::mod_decr(x, 5));
        assert_eq!(0, L::mod_decr(x, 6));
        assert_eq!(2, L::mod_decr(x, 8));
        assert_eq!(1, L::mod_decr(x, 9));
    }

    #[test]
    fn test_partial_eq() {
        let mut x = Lobby::new([None, None, None]);
        let mut y = Lobby::new([None, None, None]);

        x.push(0);
        x.push(1);

        y.push(0);
        y.push(1);

        assert_eq!(x, y);

        y.pop();
        x.push(0);
        x.shift();
        x.shift();

        assert_eq!(x, y);
        assert_eq!(x, [Some(0), None, None]);
    }

    #[test]
    fn test_iter() {
        let mut x = Lobby::new([None, None, None]);

        x.push(0);
        assert_eq!(vec![&0], x.iter().collect::<Vec<_>>());
        assert_eq!(vec![0], x.clone().into_iter().collect::<Vec<_>>());

        x.push(1);
        x.push(2);
        assert_eq!(vec![&0, &1, &2], x.iter().collect::<Vec<_>>());
        assert_eq!(vec![0, 1, 2], x.clone().into_iter().collect::<Vec<_>>());

        x.push(3);
        assert_eq!(vec![&1, &2, &3], x.iter().collect::<Vec<_>>());
        assert_eq!(vec![1, 2, 3], x.clone().into_iter().collect::<Vec<_>>());

        x.shift();
        assert_eq!(vec![&2, &3], x.iter().collect::<Vec<_>>());
        assert_eq!(vec![2, 3], x.into_iter().collect::<Vec<_>>());
    }

    #[test]
    fn test_iter_mut() {
        let mut x = Lobby::new([None, None, None, None]);
        x.push(1);
        x.push(2);
        x.push(3);
        x.push(4);

        for v in x.iter_mut() {
            *v *= 2;
        }

        assert_eq!(x, [Some(2), Some(4), Some(6), Some(8)]);
    }
}
