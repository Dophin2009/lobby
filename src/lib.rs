//! This crate provides a const-size queue-like data structure. When full, pushing new items will
//! remove the head (first-added) items.
//!
//! ```toml
//! [dependencies]
//! lobby = "0.1"
//! ```
//!
//! ```
//! use lobby::Lobby;
//!
//! let mut m = Lobby::new([None, None, None]);
//!
//! m.push(0);
//! m.push(1);
//! m.push(2);
//! assert_eq!(Some(&0), m.first());
//!
//! m.push(3);
//! assert_eq!(Some(&1), m.first());
//! ```

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
    /// use lobby::Lobby;
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
    /// use lobby::Lobby;
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

    /// Get the tail item.
    ///
    /// ```
    /// use lobby::Lobby;
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

    /// Get the nth item.
    ///
    /// ```
    /// use lobby::Lobby;
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
    #[inline]
    pub const fn nth(&self, n: usize) -> Option<&T> {
        let idx = if n > N {
            N
        } else {
            Self::mod_incr(self.head, n)
        };

        self.arr[idx].as_ref()
    }

    /// Push a new item to the lobby, returning the head if the lobby is currently full.
    ///
    /// ```
    /// use lobby::Lobby;
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

        println!("{}", self.len);

        v
    }

    /// Shift out the head item from the lobby.
    ///
    /// ```
    /// use lobby::Lobby;
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
    /// use lobby::Lobby;
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
    /// use lobby::Lobby;
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
        self.head == self.tail && self.arr[self.head].is_none()
    }

    /// Returns `true` if the Lobby is full, `false` if it is not.
    ///
    /// ```
    /// use lobby::Lobby;
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

    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }

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
}
