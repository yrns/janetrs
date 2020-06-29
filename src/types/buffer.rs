//! Janet dynamic buffer (string)
use core::marker::PhantomData;

#[cfg(feature = "std")]
use std::ffi::CStr;

use janet_ll::{
    janet_buffer, janet_buffer_ensure, janet_buffer_extra, janet_buffer_push_bytes,
    janet_buffer_push_u16, janet_buffer_push_u32, janet_buffer_push_u64, janet_buffer_push_u8,
    janet_buffer_setcount, JanetBuffer as CJanetBuffer,
};

#[cfg(feature = "std")]
use janet_ll::janet_buffer_push_cstring;

use super::JanetExtend;

/// Janet [buffers](https://janet-lang.org/docs/data_structures/buffers.html) are the mutable
/// version of [`JanetStrings`]. Since Janet strings can hold any sequence of bytes,
/// including zeros, buffers share this same property and can be used to hold any
/// arbitrary memory, which makes them very simple but versatile data structures. They can
/// be used to accumulate small strings into a large string, to implement a bitset, or to
/// represent sound or images in a program.
///
/// # Examples
/// You can create a `JanetBuffer` from a Rust string literal.
///
/// ```ignore
/// let hello = JanetBuffer::from("Hello, world!");
/// ```
///
/// You can append a [`char`] to a JanetBuffer with the [`push`] method, and append a
/// [`str`] with the [`push_str`] method:
///
/// ```ignore
/// let mut buff = JanetBuffer::from("Hello, ");
/// buff.push('w');
/// buff.push_str("orld!");
/// ```
///
/// You can also append a arbitrary sized unsigned integers with [`push_u8`],
/// [`push_u16`], [`push_u32`], [`push_u64`]:
///
/// ```ignore
/// let mut buff = JanetBuffer::with_capacity(20);
///
/// buff.push_u8(10),
/// buff.push_u16(1000028472),
/// buff.push_u32(u32::MAX),
/// buff.push_u64(u64::MIN),
/// ```
///
/// [`JanetStrings`]: ./../string/struct.JanetString.html
/// [`push`]: ./struct.JanetBuffer.html#method.push
/// [`push_str`]: ./struct.JanetBuffer.html#method.push_str
/// [`push_u8`]: ./struct.JanetBuffer.html#method.push_u8
/// [`push_u16`]: ./struct.JanetBuffer.html#method.push_u16
/// [`push_u32`]: ./struct.JanetBuffer.html#method.push_u32
/// [`push_u64`]: ./struct.JanetBuffer.html#method.push_u64
pub struct JanetBuffer<'data> {
    pub(crate) raw: *mut CJanetBuffer,
    phantom: PhantomData<&'data ()>,
}

impl JanetBuffer<'_> {
    /// Creates a empty [`JanetBuffer`].
    ///
    /// It is initially created with capacity 0, so it will not allocate until it is
    /// first pushed into.
    #[inline]
    pub fn new() -> Self {
        Self {
            raw:     unsafe { janet_buffer(0) },
            phantom: PhantomData,
        }
    }

    /// Create a empty [`JanetBuffer`] given to Janet the specified `capacity`.
    ///
    /// When `capacity` is lesser than zero, it's the same as calling with `capacity`
    /// equals to zero.
    #[inline]
    pub fn with_capacity(capacity: i32) -> Self {
        Self {
            raw:     unsafe { janet_buffer(capacity) },
            phantom: PhantomData,
        }
    }

    /// Returns the number of elements the buffer can hold without reallocating.
    #[inline]
    pub fn capacity(&self) -> i32 { unsafe { (*self.raw).capacity } }

    /// Returns the number of elements in the buffer, also referred to as its 'length'.
    #[inline]
    pub fn len(&self) -> i32 { unsafe { (*self.raw).count } }

    /// Returns `true` if the buffer contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    /// Set the length of the buffer to `new_len`.
    ///
    /// If `new_len` is greater than the current
    /// buffer length, this append null character ('\0') values into the buffer, and if
    /// `new_len` is lesser than the current buffer length, the Janet garbage
    /// collector will handle the bytes not used anymore, that's the reason this
    /// function is safe to call compared to the Rust [`String`] method with the same
    /// name.
    ///
    /// This functions does nothing if `new_len` is lesser than zero.
    #[inline]
    pub fn set_len(&mut self, new_len: i32) { unsafe { janet_buffer_setcount(self.raw, new_len) }; }

    /// Ensure that a buffer has enough space for `check_capacity` elements. If not,
    /// resize the backing memory to `capacity` * `growth` slots. In most cases, `growth`
    /// should be `1` or `2`.
    #[inline]
    pub fn ensure(&mut self, check_capacity: i32, growth: i32) {
        unsafe { janet_buffer_ensure(self.raw, check_capacity, growth) };
    }

    /// Ensures that this buffer's capacity is `additional` bytes larger than its length.
    ///
    /// # Panics
    /// Panics if the new capacity overflows [`i32`].
    #[inline]
    pub fn reserve(&mut self, additional: i32) {
        unsafe { janet_buffer_extra(self.raw, additional) };
    }

    /// Append the given [`char`] onto the end of the buffer.
    #[inline]
    pub fn push(&mut self, ch: char) { self.push_u32(ch as u32) }

    /// Append the given byte slice onto the end of the buffer.
    #[inline]
    pub fn push_bytes(&mut self, bytes: &[u8]) {
        // TODO: Check if bytes length is bigger than i32::MAX, if it is, panic!
        // But should panic be rust panic or Janet panic?
        unsafe { janet_buffer_push_bytes(self.raw, bytes.as_ptr(), bytes.len() as i32) }
    }

    /// Append the given string slice onto the end of the buffer.
    #[inline]
    pub fn push_str(&mut self, string: &str) { self.push_bytes(string.as_bytes()) }

    /// Append the given [`u8`] onto the end of the buffer.
    #[inline]
    pub fn push_u8(&mut self, elem: u8) { unsafe { janet_buffer_push_u8(self.raw, elem) } }

    /// Append the given [`u16`] onto the end of the buffer.
    #[inline]
    pub fn push_u16(&mut self, elem: u16) { unsafe { janet_buffer_push_u16(self.raw, elem) } }

    /// Append the given [`u32`] onto the end of the buffer.
    #[inline]
    pub fn push_u32(&mut self, elem: u32) { unsafe { janet_buffer_push_u32(self.raw, elem) } }

    /// Append the given [`u64`] onto the end of the buffer.
    #[inline]
    pub fn push_u64(&mut self, elem: u64) { unsafe { janet_buffer_push_u64(self.raw, elem) } }

    /// Append the given c-string slice onto the end of the buffer.
    #[cfg(feature = "std")]
    #[inline]
    pub fn push_cstr(&mut self, cstr: &CStr) {
        unsafe { janet_buffer_push_cstring(self.raw, cstr.as_ptr()) }
    }

    /// Return a raw pointer to the buffer raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    ///
    /// If you need to mutate the contents of the slice, use [`as_mut_ptr`].
    ///
    /// [`as_mut_ptr`]: ./struct.JanetBuffer.html#method.as_mut_raw
    #[inline]
    pub fn as_raw(&self) -> *const CJanetBuffer { self.raw }

    /// Return a raw mutable pointer to the buffer raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_mut_raw(&mut self) -> *mut CJanetBuffer { self.raw }
}

impl From<&str> for JanetBuffer<'_> {
    fn from(string: &str) -> Self {
        let cap = string.len();
        let mut buff = JanetBuffer::with_capacity(cap as i32);
        buff.push_str(string);
        buff
    }
}

impl From<char> for JanetBuffer<'_> {
    fn from(ch: char) -> Self {
        let mut buff = JanetBuffer::with_capacity(4);
        buff.push(ch);
        buff
    }
}

impl Default for JanetBuffer<'_> {
    #[inline]
    fn default() -> Self { Self::new() }
}

impl JanetExtend<char> for JanetBuffer<'_> {
    #[inline]
    fn extend(&mut self, ch: char) { self.push(ch) }
}

impl JanetExtend<&char> for JanetBuffer<'_> {
    #[inline]
    fn extend(&mut self, &ch: &char) { self.push(ch) }
}

impl JanetExtend<&str> for JanetBuffer<'_> {
    #[inline]
    fn extend(&mut self, string: &str) { self.push_str(string) }
}

impl JanetExtend<&[u8]> for JanetBuffer<'_> {
    #[inline]
    fn extend(&mut self, slice: &[u8]) { self.push_bytes(slice) }
}

#[cfg(feature = "std")]
impl JanetExtend<&CStr> for JanetBuffer<'_> {
    #[inline]
    fn extend(&mut self, cstr: &CStr) { self.push_cstr(cstr) }
}

#[cfg(all(test, feature = "amalgation"))]
mod tests {
    use super::*;
    use crate::client::JanetClient;
    use serial_test::serial;

    #[test]
    #[serial]
    fn creation() {
        let _client = JanetClient::init().unwrap();

        let test = JanetBuffer::new();
        assert!(test.is_empty());
        assert_eq!(0, test.capacity());

        let test = JanetBuffer::with_capacity(100);
        assert!(test.is_empty());
        assert_eq!(100, test.capacity());
    }

    #[test]
    #[serial]
    fn pushs_and_length() {
        let _client = JanetClient::init().unwrap();

        let mut test = JanetBuffer::with_capacity(10);
        assert!(test.is_empty());

        test.push('a');
        assert_eq!(4, test.len());

        test.push_bytes(b"bytes");
        assert_eq!(9, test.len());

        test.push_u8(b'a');
        assert_eq!(10, test.len());
    }

    #[test]
    #[serial]
    fn set_length() {
        let _client = JanetClient::init().unwrap();
        let mut buffer = JanetBuffer::new();

        for i in 0..10 {
            buffer.push(i.into());
        }

        assert_eq!(40, buffer.len());
        buffer.set_len(0);
        assert_eq!(0, buffer.len());
        buffer.set_len(19);
        assert_eq!(19, buffer.len());
        buffer.set_len(-10);
        assert_eq!(19, buffer.len());
    }
}
