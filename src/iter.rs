//! Iterators for Lobby.

use crate::Lobby;

/// Immutable Lobby iterator.
#[derive(Debug)]
pub struct Iter<'a, T, const N: usize> {
    inner: IterFull<'a, T, N>,
}

impl<'a, T, const N: usize> Iter<'a, T, N> {
    /// Create a new Iter.
    #[inline]
    pub fn new(inner: &'a Lobby<T, N>) -> Self {
        Self {
            inner: IterFull { inner, idx: 0 },
        }
    }

    /// Transforms this iterator into an `IterFull`.
    #[inline]
    pub fn with_full(self) -> IterFull<'a, T, N> {
        self.inner
    }
}

impl<'a, T, const N: usize> Iterator for Iter<'a, T, N> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().and_then(|v| v)
    }
}

/// Immutable Lobby iterator that yields `N` items for each space in the Lobby.
#[derive(Debug)]
pub struct IterFull<'a, T, const N: usize> {
    inner: &'a Lobby<T, N>,

    idx: usize,
}

impl<'a, T, const N: usize> Iterator for IterFull<'a, T, N> {
    type Item = Option<&'a T>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.idx += 1;
        if self.idx > N {
            None
        } else {
            Some(self.inner.nth(self.idx - 1))
        }
    }
}

/// Mutable Lobby iterator.
#[derive(Debug)]
pub struct IterMut<'a, T, const N: usize> {
    inner: IterMutFull<'a, T, N>,
}

impl<'a, T, const N: usize> IterMut<'a, T, N> {
    /// Create a new IterMut.
    #[inline]
    pub fn new(inner: &'a mut Lobby<T, N>) -> Self {
        Self {
            inner: IterMutFull {
                inner: &mut inner.arr,
                idx: 0,
            },
        }
    }

    /// Transforms this iterator into an [`IterMutFull`].
    #[inline]
    pub fn with_full(self) -> IterMutFull<'a, T, N> {
        self.inner
    }
}

impl<'a, T, const N: usize> Iterator for IterMut<'a, T, N> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().and_then(|v| v)
    }
}

/// Mutable Lobby iterator that yields `N` items for each space in the Lobby.
#[derive(Debug)]
pub struct IterMutFull<'a, T, const N: usize> {
    inner: &'a mut [Option<T>; N],

    idx: usize,
}

impl<'a, T, const N: usize> Iterator for IterMutFull<'a, T, N> {
    type Item = Option<&'a mut T>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.idx >= N {
            None
        } else {
            // SAFETY: self.idx is guaranteed to be within bounds.
            let v = (unsafe { &mut *self.inner.as_mut_ptr().add(self.idx) }).as_mut();
            self.idx += 1;
            Some(v)
        }
    }
}

/// Owning Lobby iterator.
#[derive(Debug)]
pub struct IntoIter<T, const N: usize> {
    inner: IntoIterFull<T, N>,
}

impl<'a, T, const N: usize> IntoIter<T, N> {
    /// Create a new IterMut.
    #[inline]
    pub fn new(inner: Lobby<T, N>) -> Self {
        Self {
            inner: IntoIterFull { inner, idx: 0 },
        }
    }

    /// Transforms this iterator into an [`IntoIterFull`].
    #[inline]
    pub fn with_full(self) -> IntoIterFull<T, N> {
        self.inner
    }
}

impl<T, const N: usize> Iterator for IntoIter<T, N> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().and_then(|v| v)
    }
}

/// Owning Lobby iterator that yields `N` items for each space in the Lobby.
#[derive(Debug)]
pub struct IntoIterFull<T, const N: usize> {
    inner: Lobby<T, N>,

    idx: usize,
}

impl<T, const N: usize> Iterator for IntoIterFull<T, N> {
    type Item = Option<T>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.idx >= N {
            None
        } else {
            self.idx += 1;
            Some(self.inner.shift())
        }
    }
}
