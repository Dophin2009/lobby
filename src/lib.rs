use std::mem;

#[derive(Debug, Clone)]
pub struct Lobby<T, const N: usize> {
    arr: [Option<T>; N],

    head: usize,
    tail: usize,
}

impl<T, const N: usize> Lobby<T, N> {
    // Hopefully some fix to <https://github.com/rust-lang/rust/issues/44796>.
    #[inline]
    pub const fn new(arr: [Option<T>; N]) -> Self {
        Self {
            arr,
            head: 0,
            tail: 0,
        }
    }

    #[inline]
    pub const fn first(&self) -> Option<&T> {
        self.arr[self.head].as_ref()
    }

    #[inline]
    pub const fn nth<const C: usize>(&self, n: usize) -> Option<&T> {
        self.arr[n].as_ref()
    }

    #[inline]
    pub fn push(&mut self, v: T) -> Option<T> {
        if self.arr[self.tail].is_some() {
            // Increment tail position to insert at next spot.
            self.tail = increment_counter::<N>(self.tail);
        }

        // Make push.
        let mut v = Some(v);
        mem::swap(&mut v, &mut self.arr[self.tail]);

        // Head position should be moved if the new element overrides an old.
        if v.is_some() {
            self.head = increment_counter::<N>(self.head);
        }

        v
    }

    #[inline]
    pub fn shift(&mut self) -> Option<T> {
        let mut v = None;
        mem::swap(&mut v, &mut self.arr[self.head]);

        if v.is_some() {
            self.head = decrement_counter::<N>(self.head);
        }

        v
    }

    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        let mut v = None;
        mem::swap(&mut v, &mut self.arr[self.tail]);

        if v.is_some() {
            self.tail = decrement_counter::<N>(self.tail);
        }

        v
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.head == self.tail && self.arr[self.head].is_none()
    }
}

#[inline]
const fn increment_counter<const N: usize>(mut counter: usize) -> usize {
    counter += 1;
    if counter >= N {
        counter = 0;
    }

    counter
}

#[inline]
const fn decrement_counter<const N: usize>(counter: usize) -> usize {
    if counter == 0 {
        N - 1
    } else {
        counter - 1
    }
}
