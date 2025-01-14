//! Janet tuple type.
use core::{
    cmp::Ordering,
    fmt::{self, Debug},
    iter::FusedIterator,
    marker::PhantomData,
    ops::Index,
    slice::{Chunks, ChunksExact, RChunks, RChunksExact, Windows},
};

use evil_janet::{janet_tuple_head, Janet as CJanet, JanetTupleHead};

use super::{Janet, JanetArray};

pub type Split<'a, P> = core::slice::Split<'a, Janet, P>;
pub type RSplit<'a, P> = core::slice::RSplit<'a, Janet, P>;
pub type SplitN<'a, P> = core::slice::SplitN<'a, Janet, P>;
pub type RSplitN<'a, P> = core::slice::RSplitN<'a, Janet, P>;

/// Builder for [`JanetTuple`]s.
#[derive(Debug)]
#[must_use = "builder cannot be utilized as a proper JanetTuple, use the `finish` method"]
pub struct JanetTupleBuilder<'data> {
    raw:     *mut CJanet,
    len:     i32,
    added:   i32,
    phantom: PhantomData<&'data ()>,
}

impl<'data> JanetTupleBuilder<'data> {
    /// Add a new value to the values in the tuple builder.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn put(mut self, value: impl Into<Janet>) -> Self {
        let value = value.into();

        if self.added >= self.len {
            return self;
        }

        // SAFETY: We assured that if cannot try to write above it's max len in the lines above.
        unsafe {
            let val_ptr = self.raw.offset(self.added as isize);
            *val_ptr = value.inner;
        }

        self.added += 1;
        self
    }

    /// Finalie the build process and create [`JanetTuple`].
    ///
    /// If the build is finalized and not all the allocated space was inserted with a
    /// item, the unnused space will all have value of Janet number zero.
    #[inline]
    #[must_use = "function finishies building process and returns JanetStruct"]
    pub fn finalize(self) -> JanetTuple<'data> {
        JanetTuple {
            raw:     unsafe { evil_janet::janet_tuple_end(self.raw) },
            phantom: PhantomData,
        }
    }
}

/// Janet [tuples](https://janet-lang.org/docs/data_structures/tuples.html) are immutable,
/// sequential types that are similar to [Janet arrays].
///
/// To facilitate the creation of this structure, you can use the macro
/// [`tuple`](crate::tuple!).
///
/// # Example
/// ```
/// use janetrs::{Janet, JanetTuple};
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let tuple = JanetTuple::builder(2)
///     .put(Janet::number(10.0))
///     .put(Janet::boolean(true));
/// ```
///
/// [Janet arrays]: JanetArray
#[repr(transparent)]
pub struct JanetTuple<'data> {
    pub(crate) raw: *const CJanet,
    phantom: PhantomData<&'data ()>,
}

impl<'data> JanetTuple<'data> {
    /// Start the build process to create a [`JanetTuple`].
    ///
    /// If the given `len` is lesser than zero it behaves the same as if `len` is zero.
    #[inline]
    pub fn builder(len: i32) -> JanetTupleBuilder<'data> {
        let len = if len < 0 { 0 } else { len };

        JanetTupleBuilder {
            raw: unsafe { evil_janet::janet_tuple_begin(len) },
            len,
            added: 0,
            phantom: PhantomData,
        }
    }

    /// Creates a tuple where all of it's elements are `elem`.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn with_default_elem(elem: Janet, len: i32) -> Self {
        let len = if len < 0 { 0 } else { len };

        let mut tuple = Self::builder(len);

        for _ in 0..len {
            tuple = tuple.put(elem);
        }

        tuple.finalize()
    }

    /// Create a new [`JanetTuple`] with a `raw` pointer.
    ///
    /// # Safety
    /// This function do not check if the given `raw` is `NULL` or not. Use at your
    /// own risk.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub const unsafe fn from_raw(raw: *const CJanet) -> Self {
        Self {
            raw,
            phantom: PhantomData,
        }
    }

    // Get the [`JanetTupleHead`] from the `JanetStruct` pointer.
    fn head(&self) -> &JanetTupleHead {
        // SAFETY: Janet tuple are always a valid pointer
        unsafe { &*janet_tuple_head(self.raw) }
    }

    // Get the [`JanetTupleHead`] from the `JanetStruct` pointer.
    fn head_mut(&mut self) -> &mut JanetTupleHead {
        // SAFETY: Janet tuple are always a valid pointer
        unsafe { &mut *janet_tuple_head(self.raw) }
    }

    /// Returns the sourcemap metadata attached to `JanetTuple`, which is a Rust tuple
    /// (line, column).
    #[crate::cjvg("1.9.0")]
    pub fn sourcemap(&self) -> (i32, i32) {
        let head = self.head();
        (head.sm_line, head.sm_column)
    }

    /// Set the sourcemap metadata on the `JanetTuple`.
    #[crate::cjvg("1.9.0")]
    pub fn set_sourcemap(&mut self, line: i32, column: i32) {
        let head = self.head_mut();
        head.sm_line = line;
        head.sm_column = column;
    }

    /// Returns a reference to an element in the tuple.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{Janet, JanetTuple};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let tup = JanetTuple::builder(2).put("hey").put(11).finalize();
    /// assert_eq!(tup.get(0), Some(&Janet::from("hey")));
    /// assert_eq!(tup.get(1), Some(&Janet::integer(11)));
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn get(&self, index: i32) -> Option<&Janet> {
        if index < 0 || index >= self.len() {
            None
        } else {
            // SAFETY: it's safe because we just checked that it is in bounds
            unsafe {
                let item = self.raw.offset(index as isize) as *const Janet;
                Some(&*item)
            }
        }
    }

    /// Returns a reference to an element, without doing bounds checking.
    ///
    /// # Safety
    /// Calling this method with an out-of-bounds index is *[undefined behavior]*
    /// even if the resulting reference is not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub unsafe fn get_unchecked(&self, index: i32) -> &Janet {
        let item = self.raw.offset(index as isize) as *const Janet;
        &*item
    }

    /// Returns the number of elements in the tuple, also referred to as its 'length'.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetTuple;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let tup = JanetTuple::builder(2).put("hey").put(11).finalize();
    /// assert_eq!(tup.len(), 2);
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn len(&self) -> i32 {
        self.head().length
    }

    /// Returns `true` if the tuple contains no elements.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetTuple;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let tup = JanetTuple::builder(2).put("hey").put(11).finalize();
    /// assert!(!tup.is_empty());
    ///
    /// let tup = JanetTuple::builder(0).finalize();
    /// assert!(tup.is_empty());
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns `true` if the tuple contains an element with the given `value`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::tuple;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let tup = tuple![1.0, "foo", 4.0];
    /// assert!(tup.contains("foo"));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn contains(&self, value: impl Into<Janet>) -> bool {
        let value = value.into();
        self.iter().any(|&elem| elem == value)
    }

    /// Returns a reference to the first element of the tuple, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{tuple, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = tuple![10, 40, 30];
    /// assert_eq!(Some(&Janet::from(10)), v.first());
    ///
    /// let w = tuple![];
    /// assert_eq!(None, w.first());
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn first(&self) -> Option<&Janet> {
        if let [first, ..] = self.as_ref() {
            Some(first)
        } else {
            None
        }
    }

    /// Returns a reference of the first and a reference to all the rest of the elements
    /// of the tuple, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{tuple, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let x = tuple![0, 1, 2];
    ///
    /// if let Some((first, elements)) = x.split_first() {
    ///     assert_eq!(first, &Janet::from(0));
    ///     assert_eq!(elements, &[Janet::from(1), Janet::from(2)]);
    /// }
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn split_first(&self) -> Option<(&Janet, &[Janet])> {
        if let [first, tail @ ..] = self.as_ref() {
            Some((first, tail))
        } else {
            None
        }
    }

    /// Returns a reference to the last element of the tuple, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{tuple, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = tuple![10, 40, 30];
    /// assert_eq!(Some(&Janet::from(30)), v.last());
    ///
    /// let w = tuple![];
    /// assert_eq!(None, w.last());
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn last(&self) -> Option<&Janet> {
        if let [.., last] = self.as_ref() {
            Some(last)
        } else {
            None
        }
    }

    /// Returns a reference of the last and all the rest of the elements of the array, or
    /// `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{array, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let x = array![0, 1, 2];
    ///
    /// if let Some((last, elements)) = x.split_last() {
    ///     assert_eq!(last, &Janet::from(2));
    ///     assert_eq!(elements, &[Janet::from(0), Janet::from(1)]);
    /// }
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn split_last(&self) -> Option<(&Janet, &[Janet])> {
        if let [init @ .., last] = self.as_ref() {
            Some((last, init))
        } else {
            None
        }
    }

    /// Divides one tuple into two at an index.
    ///
    /// The first will contain all indices from `[0, mid)` (excluding
    /// the index `mid` itself) and the second will contain all
    /// indices from `[mid, len)` (excluding the index `len` itself).
    ///
    /// # Panics
    ///
    /// Panics if `mid > len` or `mid < 0`.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{tuple, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = tuple![1, 2, 3, 4, 5, 6];
    ///
    /// {
    ///     let (left, right) = v.split_at(0);
    ///     assert!(left.is_empty());
    ///     assert_eq!(right, tuple![1, 2, 3, 4, 5, 6].as_ref());
    /// }
    ///
    /// {
    ///     let (left, right) = v.split_at(2);
    ///     assert_eq!(left, tuple![1, 2].as_ref());
    ///     assert_eq!(right, tuple![3, 4, 5, 6].as_ref());
    /// }
    ///
    /// {
    ///     let (left, right) = v.split_at(6);
    ///     assert_eq!(left, tuple![1, 2, 3, 4, 5, 6].as_ref());
    ///     assert!(right.is_empty());
    /// }
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn split_at(&self, mid: i32) -> (&[Janet], &[Janet]) {
        if mid < 0 {
            crate::jpanic!(
                "index out of bounds: the index ({}) is negative and must be positive",
                mid
            )
        }
        self.as_ref().split_at(mid as usize)
    }

    /// Creates a tuple by repeating a tuple `n` times.
    ///
    /// # Panics
    ///
    /// This function will panic if the capacity would overflow.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::{tuple, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(
    ///     tuple![1, 2].repeat(3).as_ref(),
    ///     tuple![1, 2, 1, 2, 1, 2].as_ref()
    /// );
    /// ```
    ///
    /// A panic upon overflow:
    ///
    /// ```should_panic
    /// use janetrs::{tuple, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// // this will panic at runtime
    /// b"0123456789abcdef".repeat(usize::MAX);
    /// ```
    #[inline]
    #[must_use = "this returns a new JanetArray, without modifying the original"]
    pub fn repeat(&self, n: usize) -> JanetArray {
        self.as_ref().repeat(n).into_iter().collect()
    }

    /// Returns `true` if `needle` is a prefix of the tuple.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{tuple, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = tuple![10, 40, 30];
    /// assert!(v.starts_with(&[Janet::from(10)]));
    /// assert!(v.starts_with(&[Janet::from(10), Janet::from(40)]));
    /// assert!(!v.starts_with(&[Janet::from(50)]));
    /// assert!(!v.starts_with(&[Janet::from(10), Janet::from(50)]));
    /// ```
    ///
    /// Always returns `true` if `needle` is an empty slice:
    ///
    /// ```
    /// use janetrs::{tuple, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = tuple![10, 40, 30];
    /// assert!(v.starts_with(&[]));
    /// let v = tuple![];
    /// assert!(v.starts_with(&[]));
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn starts_with(&self, needle: &[Janet]) -> bool {
        self.as_ref().starts_with(needle)
    }

    /// Returns `true` if `needle` is a suffix of the tuple.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{tuple, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = tuple![10, 40, 30];
    /// assert!(v.ends_with(&[Janet::from(30)]));
    /// assert!(v.ends_with(&[Janet::from(40), Janet::from(30)]));
    /// assert!(!v.ends_with(&[Janet::from(50)]));
    /// assert!(!v.ends_with(&[Janet::from(50), Janet::from(30)]));
    /// ```
    ///
    /// Always returns `true` if `needle` is an empty slice:
    ///
    /// ```
    /// use janetrs::{tuple, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = tuple![10, 40, 30];
    /// assert!(v.ends_with(&[]));
    /// let v = tuple![];
    /// assert!(v.ends_with(&[]));
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn ends_with(&self, needle: &[Janet]) -> bool {
        self.as_ref().ends_with(needle)
    }

    /// Binary searches this tuple for a given element.
    ///
    /// If the value is found then [`Result::Ok`] is returned, containing the
    /// index of the matching element. If there are multiple matches, then any
    /// one of the matches could be returned. If the value is not found then
    /// [`Result::Err`] is returned, containing the index where a matching
    /// element could be inserted while maintaining sorted order.
    ///
    /// # Examples
    ///
    /// Looks up a series of four elements. The first is found, with a
    /// uniquely determined position; the second and third are not
    /// found; the fourth could match any position in `[1, 4]`.
    ///
    /// ```
    /// use janetrs::{tuple, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = tuple![0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    ///
    /// assert_eq!(s.binary_search(&Janet::from(13)), Ok(9));
    /// assert_eq!(s.binary_search(&Janet::from(4)), Err(7));
    /// assert_eq!(s.binary_search(&Janet::from(100)), Err(13));
    /// let r = s.binary_search(&Janet::from(1));
    /// assert!(match r {
    ///     Ok(1..=4) => true,
    ///     _ => false,
    /// });
    /// ```
    ///
    /// If you want to insert an item to a sorted vector, while maintaining
    /// sort order:
    ///
    /// ```
    /// use janetrs::{tuple, Janet, JanetArray};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut s = tuple![0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    /// let num = Janet::from(42);
    /// let idx = s.binary_search(&num).unwrap_or_else(|x| x);
    /// let mut s = JanetArray::from(s);
    /// s.insert(idx as i32, num);
    /// assert_eq!(
    ///     s.as_ref(),
    ///     tuple![0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 42, 55].as_ref()
    /// );
    /// ```
    #[inline]
    pub fn binary_search(&self, x: &Janet) -> Result<usize, usize> {
        self.binary_search_by(|p| p.cmp(x))
    }

    /// Binary searches this sorted tuple with a comparator function.
    ///
    /// The comparator function should implement an order consistent
    /// with the sort order of the underlying slice, returning an
    /// order code that indicates whether its argument is `Less`,
    /// `Equal` or `Greater` the desired target.
    ///
    /// If the value is found then [`Result::Ok`] is returned, containing the
    /// index of the matching element. If there are multiple matches, then any
    /// one of the matches could be returned. If the value is not found then
    /// [`Result::Err`] is returned, containing the index where a matching
    /// element could be inserted while maintaining sorted order.
    ///
    /// # Examples
    ///
    /// Looks up a series of four elements. The first is found, with a
    /// uniquely determined position; the second and third are not
    /// found; the fourth could match any position in `[1, 4]`.
    ///
    /// ```
    /// use janetrs::{tuple, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = tuple![0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    ///
    /// let seek = Janet::from(13);
    /// assert_eq!(s.binary_search_by(|probe| probe.cmp(&seek)), Ok(9));
    /// let seek = Janet::from(4);
    /// assert_eq!(s.binary_search_by(|probe| probe.cmp(&seek)), Err(7));
    /// let seek = Janet::from(100);
    /// assert_eq!(s.binary_search_by(|probe| probe.cmp(&seek)), Err(13));
    /// let seek = Janet::from(1);
    /// let r = s.binary_search_by(|probe| probe.cmp(&seek));
    /// assert!(match r {
    ///     Ok(1..=4) => true,
    ///     _ => false,
    /// });
    /// ```
    #[inline]
    pub fn binary_search_by<'a, F>(&'a self, f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a Janet) -> Ordering,
    {
        self.as_ref().binary_search_by(f)
    }

    /// Binary searches this tuple with a key extraction function.
    ///
    /// Assumes that the tuple is sorted by the key, for instance with
    /// [`sort_by_key`] using the same key extraction function.
    ///
    /// If the value is found then [`Result::Ok`] is returned, containing the
    /// index of the matching element. If there are multiple matches, then any
    /// one of the matches could be returned. If the value is not found then
    /// [`Result::Err`] is returned, containing the index where a matching
    /// element could be inserted while maintaining sorted order.
    ///
    /// [`sort_by_key`]: #method.sort_by_key
    ///
    /// # Examples
    /// TODO: Find a good example
    ///
    /// ```
    /// use janetrs::{tuple, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    /// ```
    #[inline]
    pub fn binary_search_by_key<'a, B, F>(&'a self, b: &B, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a Janet) -> B,
        B: Ord,
    {
        self.binary_search_by(|k| f(k).cmp(b))
    }

    /// Creates a iterator over the reference of the array items.
    #[inline]
    pub fn iter(&self) -> Iter<'_, '_> {
        Iter {
            tup: self,
            index_head: 0,
            index_tail: self.len(),
        }
    }

    /// Creates an iterator over all contiguous windows of length
    /// `size`. The windows overlap. If the tuple is shorter than
    /// `size`, the iterator returns no values.
    ///
    /// # Panics
    ///
    /// Panics if `size` is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{tuple, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = tuple!['r', 'u', 's', 't'];
    /// let mut iter = arr.windows(2);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('r'), Janet::from('u')]);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('u'), Janet::from('s')]);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('s'), Janet::from('t')]);
    /// assert!(iter.next().is_none());
    /// ```
    ///
    /// If the tuple is shorter than `size`:
    ///
    /// ```
    /// use janetrs::{tuple, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = tuple!['f', 'o', 'o'];
    /// let mut iter = arr.windows(4);
    /// assert!(iter.next().is_none());
    /// ```
    #[inline]
    pub fn windows(&self, size: usize) -> Windows<'_, Janet> {
        self.as_ref().windows(size)
    }

    /// Creates an iterator over `chunk_size` elements of the tuple at a time, starting at
    /// the beginning of the tuple.
    ///
    /// The chunks are slices and do not overlap. If `chunk_size` does not divide the
    /// length of the tuple, then the last chunk will not have length `chunk_size`.
    ///
    /// See [`chunks_exact`] for a variant of this iterator that returns chunks of always
    /// exactly `chunk_size` elements, and [`rchunks`] for the same iterator but
    /// starting at the end of the tuple.
    ///
    /// # Panics
    ///
    /// Panics if `chunk_size` is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{tuple, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = tuple!['l', 'o', 'r', 'e', 'm'];
    /// let mut iter = arr.chunks(2);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('l'), Janet::from('o')]);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('r'), Janet::from('e')]);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('m')]);
    /// assert!(iter.next().is_none());
    /// ```
    ///
    /// [`chunks_exact`]: #method.chunks_exact
    /// [`rchunks`]: #method.rchunks
    #[inline]
    pub fn chunks(&self, chunk_size: usize) -> Chunks<'_, Janet> {
        self.as_ref().chunks(chunk_size)
    }

    /// Creates an iterator over `chunk_size` elements of the tuple at a time, starting at
    /// the beginning of the tuple.
    ///
    /// The chunks are slices and do not overlap. If `chunk_size` does not divide the
    /// length of the tuple, then the last up to `chunk_size-1` elements will be
    /// omitted and can be retrieved from the `remainder` function of the iterator.
    ///
    /// Due to each chunk having exactly `chunk_size` elements, the compiler can often
    /// optimize the resulting code better than in the case of [`chunks`].
    ///
    /// See [`chunks`] for a variant of this iterator that also returns the remainder as a
    /// smaller chunk, and [`rchunks_exact`] for the same iterator but starting at the
    /// end of the tuple.
    ///
    /// # Panics
    ///
    /// Panics if `chunk_size` is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{tuple, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = tuple!['l', 'o', 'r', 'e', 'm'];
    /// let mut iter = arr.chunks_exact(2);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('l'), Janet::from('o')]);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('r'), Janet::from('e')]);
    /// assert!(iter.next().is_none());
    /// assert_eq!(iter.remainder(), &[Janet::from('m')]);
    /// ```
    ///
    /// [`chunks`]: #method.chunks
    /// [`rchunks_exact`]: #method.rchunks_exact
    #[inline]
    pub fn chunks_exact(&self, chunk_size: usize) -> ChunksExact<'_, Janet> {
        self.as_ref().chunks_exact(chunk_size)
    }

    /// Create an iterator over `chunk_size` elements of the tuple at a time, starting at
    /// the end of the tuple.
    ///
    /// The chunks are slices and do not overlap. If `chunk_size` does not divide the
    /// length of the tuple, then the last chunk will not have length `chunk_size`.
    ///
    /// See [`rchunks_exact`] for a variant of this iterator that returns chunks of always
    /// exactly `chunk_size` elements, and [`chunks`] for the same iterator but
    /// starting at the beginning of the tuple.
    ///
    /// # Panics
    ///
    /// Panics if `chunk_size` is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{tuple, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = tuple!['l', 'o', 'r', 'e', 'm'];
    /// let mut iter = arr.rchunks(2);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('e'), Janet::from('m')]);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('o'), Janet::from('r')]);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('l')]);
    /// assert!(iter.next().is_none());
    /// ```
    ///
    /// [`rchunks_exact`]: #method.rchunks_exact
    /// [`chunks`]: #method.chunks
    #[inline]
    pub fn rchunks(&self, chunk_size: usize) -> RChunks<'_, Janet> {
        self.as_ref().rchunks(chunk_size)
    }

    /// Returns an iterator over `chunk_size` elements of the tuple at a time, starting at
    /// the end of the tuple.
    ///
    /// The chunks are slices and do not overlap. If `chunk_size` does not divide the
    /// length of the tuple, then the last up to `chunk_size-1` elements will be
    /// omitted and can be retrieved from the `remainder` function of the iterator.
    ///
    /// Due to each chunk having exactly `chunk_size` elements, the compiler can often
    /// optimize the resulting code better than in the case of [`chunks`].
    ///
    /// See [`rchunks`] for a variant of this iterator that also returns the remainder as
    /// a smaller chunk, and [`chunks_exact`] for the same iterator but starting at
    /// the beginning of the tuple.
    ///
    /// # Panics
    ///
    /// Panics if `chunk_size` is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{tuple, Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = tuple!['l', 'o', 'r', 'e', 'm'];
    /// let mut iter = arr.rchunks_exact(2);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('e'), Janet::from('m')]);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('o'), Janet::from('r')]);
    /// assert!(iter.next().is_none());
    /// assert_eq!(iter.remainder(), &[Janet::from('l')]);
    /// ```
    ///
    /// [`chunks`]: #method.chunks
    /// [`rchunks`]: #method.rchunks
    /// [`chunks_exact`]: #method.chunks_exact
    #[inline]
    pub fn rchunks_exact(&self, chunk_size: usize) -> RChunksExact<'_, Janet> {
        self.as_ref().rchunks_exact(chunk_size)
    }

    /// Creates an iterator over subslices separated by elements that match
    /// `pred`. The matched element is not contained in the subslices.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{tuple, Janet, TaggedJanet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = tuple![10, 40, 33, 20];
    /// let mut iter = arr.split(|j| match j.unwrap() {
    ///     TaggedJanet::Number(num) => (num % 3.0) as u128 == 0,
    ///     _ => false,
    /// });
    ///
    /// assert_eq!(iter.next().unwrap(), tuple![10, 40].as_ref());
    /// assert_eq!(iter.next().unwrap(), tuple![20].as_ref());
    /// assert!(iter.next().is_none());
    /// ```
    ///
    /// If the first element is matched, an empty slice will be the first item
    /// returned by the iterator. Similarly, if the last element in the slice
    /// is matched, an empty slice will be the last item returned by the
    /// iterator:
    ///
    /// ```
    /// use janetrs::{tuple, Janet, TaggedJanet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = tuple![10, 40, 33];
    /// let mut iter = arr.split(|j| match j.unwrap() {
    ///     TaggedJanet::Number(num) => (num % 3.0) as u128 == 0,
    ///     _ => false,
    /// });
    ///
    /// assert_eq!(iter.next().unwrap(), tuple![10, 40].as_ref());
    /// assert_eq!(iter.next().unwrap(), tuple![].as_ref());
    /// assert!(iter.next().is_none());
    /// ```
    ///
    /// If two matched elements are directly adjacent, an empty slice will be
    /// present between them:
    ///
    /// ```
    /// use janetrs::{tuple, Janet, TaggedJanet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = tuple![10, 6, 33, 20];
    /// let mut iter = arr.split(|j| match j.unwrap() {
    ///     TaggedJanet::Number(num) => (num % 3.0) as u128 == 0,
    ///     _ => false,
    /// });
    ///
    /// assert_eq!(iter.next().unwrap(), tuple![10].as_ref());
    /// assert_eq!(iter.next().unwrap(), tuple![].as_ref());
    /// assert_eq!(iter.next().unwrap(), tuple![20].as_ref());
    /// assert!(iter.next().is_none());
    /// ```
    #[inline]
    pub fn split<F>(&self, pred: F) -> Split<'_, F>
    where
        F: FnMut(&Janet) -> bool,
    {
        self.as_ref().split(pred)
    }

    /// Creates an iterator over subslices separated by elements that match
    /// `pred`, starting at the end of the slice and working backwards.
    /// The matched element is not contained in the subslices.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{tuple, Janet, TaggedJanet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = tuple![11, 22, 33, 0, 44, 55];
    /// let mut iter = arr.rsplit(|j| match j.unwrap() {
    ///     TaggedJanet::Number(num) => num as i64 == 0,
    ///     _ => false,
    /// });
    ///
    /// assert_eq!(iter.next().unwrap(), tuple![44, 55].as_ref());
    /// assert_eq!(iter.next().unwrap(), tuple![11, 22, 33].as_ref());
    /// assert_eq!(iter.next(), None);
    /// ```
    ///
    /// As with `split()`, if the first or last element is matched, an empty
    /// slice will be the first (or last) item returned by the iterator.
    ///
    /// ```
    /// use janetrs::{tuple, Janet, TaggedJanet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = tuple![0, 1, 1, 2, 3, 5, 8];
    /// let mut it = v.rsplit(|j| match j.unwrap() {
    ///     TaggedJanet::Number(n) => n as i64 % 2 == 0,
    ///     _ => false,
    /// });
    /// assert_eq!(it.next().unwrap(), tuple![].as_ref());
    /// assert_eq!(it.next().unwrap(), tuple![3, 5].as_ref());
    /// assert_eq!(it.next().unwrap(), tuple![1, 1].as_ref());
    /// assert_eq!(it.next().unwrap(), tuple![].as_ref());
    /// assert_eq!(it.next(), None);
    /// ```
    #[inline]
    pub fn rsplit<F>(&self, pred: F) -> RSplit<'_, F>
    where
        F: FnMut(&Janet) -> bool,
    {
        self.as_ref().rsplit(pred)
    }

    /// Creates an iterator over subslices separated by elements that match
    /// `pred`, limited to returning at most `n` items. The matched element is
    /// not contained in the subslices.
    ///
    /// The last element returned, if any, will contain the remainder of the
    /// tuple.
    ///
    /// # Examples
    ///
    /// Print the tuple split once by numbers divisible by 3 (i.e., `[10, 40]`,
    /// `[20, 60, 50]`):
    ///
    /// ```
    /// use janetrs::{tuple, Janet, TaggedJanet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = tuple![10, 40, 30, 20, 60, 50];
    ///
    /// for group in v.splitn(2, |j| match j.unwrap() {
    ///     TaggedJanet::Number(num) => num as i64 % 3 == 0,
    ///     _ => false,
    /// }) {
    ///     println!("{:?}", group);
    /// }
    /// ```
    #[inline]
    pub fn splitn<F>(&self, n: usize, pred: F) -> SplitN<'_, F>
    where
        F: FnMut(&Janet) -> bool,
    {
        self.as_ref().splitn(n, pred)
    }

    /// Returns an iterator over subslices separated by elements that match
    /// `pred` limited to returning at most `n` items. This starts at the end of
    /// the tuple and works backwards. The matched element is not contained in
    /// the subslices.
    ///
    /// The last element returned, if any, will contain the remainder of the
    /// tuple.
    ///
    /// # Examples
    ///
    /// Print the tuple split once, starting from the end, by numbers divisible
    /// by 3 (i.e., `[50]`, `[10, 40, 30, 20]`):
    ///
    /// ```
    /// use janetrs::{tuple, Janet, TaggedJanet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = tuple![10, 40, 30, 20, 60, 50];
    ///
    /// for group in v.rsplitn(2, |j| match j.unwrap() {
    ///     TaggedJanet::Number(num) => num as i64 % 3 == 0,
    ///     _ => false,
    /// }) {
    ///     println!("{:?}", group);
    /// }
    /// ```
    #[inline]
    pub fn rsplitn<F>(&self, n: usize, pred: F) -> RSplitN<'_, F>
    where
        F: FnMut(&Janet) -> bool,
    {
        self.as_ref().rsplitn(n, pred)
    }

    /// Return a raw pointer to the tuple raw structure.
    ///
    /// The caller must ensure that the fiber outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    #[must_use]
    pub const fn as_raw(&self) -> *const CJanet {
        self.raw
    }

    /// Return a raw pointer to the tuple first data.
    ///
    /// The caller must ensure that the array outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    #[must_use]
    pub fn as_ptr(&self) -> *const Janet {
        self.raw as _
    }
}

impl Debug for JanetTuple<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl Clone for JanetTuple<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        let len = self.len();
        let mut clone = Self::builder(len);

        for elem in self.into_iter().copied() {
            clone = clone.put(elem);
        }

        clone.finalize()
    }
}

impl PartialOrd for JanetTuple<'_> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for JanetTuple<'_> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        use core::cmp::Ordering::{Equal, Greater, Less};

        match self.len().cmp(&other.len()) {
            x @ (Less | Greater) => x,
            Equal => {
                for (s, o) in self.iter().zip(other.iter()) {
                    match s.cmp(o) {
                        x @ (Less | Greater) => return x,
                        Equal => continue,
                    }
                }
                Equal
            },
        }
    }
}

impl PartialEq for JanetTuple<'_> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // if the pointer is the same, one are equal to the other
        if self.raw.eq(&other.raw) {
            return true;
        }

        // If the hash is the same
        // SAFETY: Janet tuple must always be a valid pointer
        if self.head().hash.eq(&self.head().hash) {
            return true;
        }

        // if they have the same length, check value by value
        if self.len().eq(&other.len()) {
            return self.iter().zip(other.iter()).all(|(s, o)| s.eq(o));
        }
        // otherwise it's false
        false
    }
}

impl Eq for JanetTuple<'_> {}

impl super::DeepEq<JanetArray<'_>> for JanetTuple<'_> {
    #[inline]
    fn deep_eq(&self, other: &JanetArray<'_>) -> bool {
        other.deep_eq(self)
    }
}

impl Default for JanetTuple<'_> {
    #[inline]
    fn default() -> Self {
        crate::tuple![]
    }
}

impl AsRef<[Janet]> for JanetTuple<'_> {
    #[inline]
    fn as_ref(&self) -> &[Janet] {
        // SAFETY: Janet uses i32 as max size for all collections and indexing, so it always has
        // len lesser than isize::MAX
        unsafe { core::slice::from_raw_parts(self.raw as *const _, self.len() as usize) }
    }
}

impl From<JanetArray<'_>> for JanetTuple<'_> {
    #[inline]
    fn from(arr: JanetArray<'_>) -> Self {
        arr.into_iter().collect()
    }
}

impl From<&JanetArray<'_>> for JanetTuple<'_> {
    #[inline]
    fn from(arr: &JanetArray<'_>) -> Self {
        arr.into_iter().collect()
    }
}

impl<'data> IntoIterator for JanetTuple<'data> {
    type IntoIter = IntoIter<'data>;
    type Item = Janet;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let len = self.len();
        IntoIter {
            tup: self,
            index_head: 0,
            index_tail: len,
        }
    }
}

impl<'a, 'data> IntoIterator for &'a JanetTuple<'data> {
    type IntoIter = Iter<'a, 'data>;
    type Item = &'a Janet;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let len = self.len();
        Iter {
            tup: self,
            index_head: 0,
            index_tail: len,
        }
    }
}

impl<U: Into<Janet>> FromIterator<U> for JanetTuple<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from_iter<T: IntoIterator<Item = U>>(iter: T) -> Self {
        let iter = iter.into_iter().collect::<JanetArray>().into_iter();
        let (lower, upper) = iter.size_hint();

        let mut new = if let Some(upper) = upper {
            Self::builder(upper as i32)
        } else if lower > 0 {
            Self::builder(lower as i32)
        } else {
            Self::builder(20)
        };

        for i in iter {
            new = new.put(i);
        }
        new.finalize()
    }
}

impl Index<i32> for JanetTuple<'_> {
    type Output = Janet;

    /// Get a reference of the [`Janet`] hold by [`JanetTuple`] at `index`.
    ///
    /// # Janet Panics
    /// This function may Janet panic if try to access `index` out of the bounds
    #[inline]
    fn index(&self, index: i32) -> &Self::Output {
        if index < 0 {
            crate::jpanic!(
                "index out of bounds: the index ({}) is negative and must be positive",
                index
            )
        }

        self.get(index).unwrap_or_else(|| {
            crate::jpanic!(
                "index out of bounds: the len is {} but the index is {}",
                self.len(),
                index
            )
        })
    }
}

/// An iterator over a reference to the [`JanetTuple`] elements.
#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Iter<'a, 'data> {
    tup: &'a JanetTuple<'data>,
    index_head: i32,
    index_tail: i32,
}

impl Debug for Iter<'_, '_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.tup.as_ref()).finish()
    }
}

impl<'a> Iterator for Iter<'a, '_> {
    type Item = &'a Janet;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.index_head >= self.index_tail {
            None
        } else {
            let ret = self.tup.get(self.index_head);
            self.index_head += 1;
            ret
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = (self.index_tail - self.index_head) as usize;
        (exact, Some(exact))
    }
}

impl DoubleEndedIterator for Iter<'_, '_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index_head == self.index_tail {
            None
        } else {
            self.index_tail -= 1;
            self.tup.get(self.index_tail)
        }
    }
}

impl ExactSizeIterator for Iter<'_, '_> {}

impl FusedIterator for Iter<'_, '_> {}

/// An iterator that moves out of a [`JanetTuple`].
#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct IntoIter<'data> {
    tup: JanetTuple<'data>,
    index_head: i32,
    index_tail: i32,
}

impl Debug for IntoIter<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.tup.as_ref()).finish()
    }
}

impl Iterator for IntoIter<'_> {
    type Item = Janet;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.index_head >= self.index_tail {
            None
        } else {
            let ret = self.tup.get(self.index_head).copied();
            self.index_head += 1;
            ret
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = (self.index_tail - self.index_head) as usize;
        (exact, Some(exact))
    }
}

impl DoubleEndedIterator for IntoIter<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index_head == self.index_tail {
            None
        } else {
            self.index_tail -= 1;
            self.tup.get(self.index_tail).copied()
        }
    }
}

impl ExactSizeIterator for IntoIter<'_> {}

impl FusedIterator for IntoIter<'_> {}

#[cfg(all(test, any(feature = "amalgation", feature = "link-system")))]
mod tests {
    use super::*;
    use crate::{client::JanetClient, tuple, *};
    use alloc::vec;

    #[test]
    fn builder() -> Result<(), client::Error> {
        let _client = JanetClient::init()?;

        let tuple = JanetTuple::builder(0).finalize();
        assert!(tuple.is_empty());

        let tuple = JanetTuple::builder(3)
            .put(Janet::number(10.0))
            .put(Janet::nil())
            .put(Janet::boolean(true))
            .finalize();

        assert_eq!(3, tuple.len());

        Ok(())
    }

    #[test]
    fn get() -> Result<(), client::Error> {
        let _client = JanetClient::init()?;

        let tuple = JanetTuple::builder(3)
            .put(Janet::number(10.0))
            .put(Janet::nil())
            .put(Janet::boolean(true))
            .finalize();

        assert_eq!(None, tuple.get(-1));
        assert_eq!(Some(&Janet::number(10.0)), tuple.get(0));
        assert_eq!(Some(&Janet::nil()), tuple.get(1));
        assert_eq!(Some(&Janet::boolean(true)), tuple.get(2));
        assert_eq!(None, tuple.get(3));

        Ok(())
    }

    #[test]
    fn clone() -> Result<(), client::Error> {
        let _client = JanetClient::init()?;

        let tuple = JanetTuple::builder(3)
            .put(Janet::number(10.0))
            .put(Janet::nil())
            .put(Janet::boolean(true))
            .finalize();

        let clone = tuple.clone();

        assert_ne!(tuple.raw, clone.raw);
        assert_eq!(tuple.get(-1), clone.get(-1));
        assert_eq!(tuple.get(0), clone.get(0));
        assert_eq!(tuple.get(1), clone.get(1));
        assert_eq!(tuple.get(2), clone.get(2));
        assert_eq!(tuple.get(3), clone.get(3));

        Ok(())
    }

    #[test]
    fn collect() -> Result<(), client::Error> {
        let _client = JanetClient::init()?;
        let vec = vec![Janet::nil(); 100];

        let jtup: JanetTuple<'_> = vec.into_iter().collect();
        assert_eq!(jtup.len(), 100);
        assert!(jtup.iter().all(|j| j == Janet::nil()));

        let vec = crate::array![101.0, "string", true];

        let jtup: JanetTuple<'_> = vec.into_iter().collect();
        assert_eq!(jtup.len(), 3);
        let mut iter = jtup.iter();
        assert_eq!(Some(&Janet::number(101.0)), iter.next());
        assert_eq!(
            Some(&Janet::string(JanetString::new("string"))),
            iter.next()
        );
        assert_eq!(Some(&Janet::boolean(true)), iter.next());
        assert_eq!(None, iter.next());

        Ok(())
    }

    #[test]
    fn iter_iterator() -> Result<(), client::Error> {
        let _client = JanetClient::init()?;
        let array = tuple![1, "hey", true];

        let mut iter = array.iter();

        assert_eq!(Some(&Janet::integer(1)), iter.next());
        assert_eq!(Some(&Janet::from("hey")), iter.next());
        assert_eq!(Some(&Janet::boolean(true)), iter.next());
        assert_eq!(None, iter.next());

        Ok(())
    }

    #[test]
    fn iter_double_ended_iterator() -> Result<(), client::Error> {
        let _client = JanetClient::init()?;
        let numbers = tuple![1, 2, 3, 4, 5, 6];

        let mut iter = numbers.iter();

        assert_eq!(iter.len(), 6);
        assert_eq!(Some(&Janet::integer(1)), iter.next());
        assert_eq!(iter.len(), 5);
        assert_eq!(Some(&Janet::integer(6)), iter.next_back());
        assert_eq!(iter.len(), 4);
        assert_eq!(Some(&Janet::integer(5)), iter.next_back());
        assert_eq!(iter.len(), 3);
        assert_eq!(Some(&Janet::integer(2)), iter.next());
        assert_eq!(iter.len(), 2);
        assert_eq!(Some(&Janet::integer(3)), iter.next());
        assert_eq!(iter.len(), 1);
        assert_eq!(Some(&Janet::integer(4)), iter.next());
        assert_eq!(iter.len(), 0);
        assert_eq!(None, iter.next());
        assert_eq!(None, iter.next_back());

        Ok(())
    }

    #[test]
    fn intoiter_iterator() -> Result<(), client::Error> {
        let _client = JanetClient::init()?;
        let array = tuple![1, "hey", true];

        let mut iter = array.into_iter();

        assert_eq!(Some(Janet::integer(1)), iter.next());
        assert_eq!(Some(Janet::from("hey")), iter.next());
        assert_eq!(Some(Janet::boolean(true)), iter.next());
        assert_eq!(None, iter.next());

        Ok(())
    }

    #[test]
    fn intoiter_double_ended_iterator() -> Result<(), client::Error> {
        let _client = JanetClient::init()?;
        let numbers = tuple![1, 2, 3, 4, 5, 6];

        let mut iter = numbers.into_iter();

        assert_eq!(iter.len(), 6);
        assert_eq!(Some(Janet::integer(1)), iter.next());
        assert_eq!(iter.len(), 5);
        assert_eq!(Some(Janet::integer(6)), iter.next_back());
        assert_eq!(iter.len(), 4);
        assert_eq!(Some(Janet::integer(5)), iter.next_back());
        assert_eq!(iter.len(), 3);
        assert_eq!(Some(Janet::integer(2)), iter.next());
        assert_eq!(iter.len(), 2);
        assert_eq!(Some(Janet::integer(3)), iter.next());
        assert_eq!(iter.len(), 1);
        assert_eq!(Some(Janet::integer(4)), iter.next());
        assert_eq!(iter.len(), 0);
        assert_eq!(None, iter.next());
        assert_eq!(None, iter.next_back());

        Ok(())
    }

    #[test]
    fn size_hint() -> Result<(), client::Error> {
        let _client = JanetClient::init()?;
        let mut iter = tuple![0; 100].into_iter();

        // The code for all the iterators of the array are the same
        assert_eq!(iter.len(), 100);
        let _ = iter.next();
        assert_eq!(iter.len(), 99);
        let _ = iter.next_back();
        assert_eq!(iter.len(), 98);
        Ok(())
    }

    #[test]
    fn compare() -> Result<(), client::Error> {
        use core::cmp::Ordering::*;
        let _client = JanetClient::init()?;

        let test = tuple![1, 2, 3, 4, 5, 6];
        let clone = test.clone();

        assert_eq!(test.cmp(&clone), Equal);

        let test2 = tuple![1, 2];
        assert_eq!(test.cmp(&test2), Greater);

        Ok(())
    }
}
