#![feature(macro_rules, phase)]

//! See the `Bitmap` type.

#[phase(link, plugin)] extern crate log;

extern crate libc;

use std::num::Int;

/// A dense bitmap, intended to store small bitslices (<= width of uint).
#[unsafe_no_drop_flag]
pub struct Bitmap {
    entries: uint,
    width: uint,
    // we avoid a vector here because we have our own bounds checking, and
    // don't need to duplicate the length.
    data: *mut u8,
}

fn get_n_bits_at(byte: u8, n: u8, start: u8) -> u8 {
    (byte >> (8-n-start) as uint) & (0xFF >> (8-n) as uint)
}

impl Drop for Bitmap {
    fn drop(&mut self) {
        let p = self.data;
        if p != std::ptr::null_mut() {
            self.data = std::ptr::null_mut();
            unsafe { libc::free(p as *mut libc::c_void); }
        }
    }
}

impl Bitmap {
    /// Create a new bitmap, returning None if the data can't be allocated or
    /// if the width of each slice can't fit in a uint. entries * width must
    /// not overflow uint.
    pub fn new(entries: uint, width: uint) -> Option<Bitmap> {
        if width > (std::mem::size_of::<uint>() * 8) {
            None
        } else {
            entries.checked_mul(width)
            .and_then(|bits| bits.checked_add(8 - (bits % 8)))
            .and_then(|rbits| rbits.checked_div(8))
            .and_then(|needed| {
                // can't use ~ or ~[] because they fail on failure to allocate. this needs to be
                // more resilient to failure.
                let ptr = unsafe { libc::malloc(needed as u64) };

                if ptr == std::ptr::null_mut() {
                    None
                } else {
                    unsafe { std::ptr::zero_memory(ptr, needed); }
                    Some(Bitmap {
                        entries: entries,
                        width: width,
                        data: ptr as *mut u8
                    })
                }
            })
        }
    }

    /// Create a new Bitmap from raw parts. Will return None if the given
    /// entry and width would overflow the number of bits or bytes needed to
    /// store the Bitmap.
    pub unsafe fn new_raw(entries: uint, width: uint, ptr: *mut u8) -> Option<Bitmap> {
        if width > (std::mem::size_of::<uint>() * 8) {
            None
        } else {
            entries.checked_mul(width)
            .and_then(|bits| bits.checked_add(8 - (bits % 8)))
            .and_then(|rbits| rbits.checked_div(8))
            .and_then(|_| {
                Some(Bitmap {
                    entries: entries,
                    width: width,
                    data: ptr
                })
            })
        }
    }

    /// Get the `i`th bitslice, returning None on out-of-bounds
    pub fn get(&self, i: uint) -> Option<uint> {
        if i >= self.entries {
            None
        } else {
            let mut bit_offset = i * self.width;

            let mut in_byte_offset = bit_offset % 8;
            let mut byte_offset = (bit_offset - in_byte_offset) / 8;

            let mut bits_left = self.width;

            let mut value: uint = 0;

            while bits_left > 0 {
                // how many bits can we need to set in this byte?
                let can_get = std::cmp::min(8 - in_byte_offset, bits_left);

                // alright, pull them out.
                let byte = unsafe { *self.data.offset(byte_offset as int) };
                let got = get_n_bits_at(byte, can_get as u8, in_byte_offset as u8) as uint;

                // make room for the bits we just read
                value <<= can_get;
                value |= got;

                // update all the state
                bit_offset += can_get;
                in_byte_offset = bit_offset % 8;
                byte_offset = (bit_offset - in_byte_offset) / 8;
                bits_left -= can_get;
            }
            Some(value)
        }
    }

    /// Set the `i`th bitslice to `value`, returning false on out-of-bounds or if `value` contains
    /// bits outside of the least significant `self.width` bits.
    pub fn set(&mut self, i: uint, mut value: uint) -> bool {
        let uintbits = std::mem::size_of::<uint>() * 8;
        if i >= self.entries || value & !(-1 >> (uintbits - self.width)) != 0 {
            false
        } else {
            // shift over into the high bits
            value <<= uintbits - self.width;

            let mut bit_offset = i * self.width;

            let mut in_byte_offset = bit_offset % 8;
            let mut byte_offset = (bit_offset - in_byte_offset) / 8;

            let mut bits_left = self.width;

            while bits_left > 0 {
                let can_set = std::cmp::min(8 - in_byte_offset, bits_left);

                // pull out the highest can_set bits from value
                let mut to_set: uint = value >> (uintbits - can_set);
                // move them into where they will live
                to_set <<= 8 - can_set - in_byte_offset;

                let addr = unsafe { self.data.offset(byte_offset as int) };
                let mut byte = unsafe { *addr };

                // clear the bits we'll be setting
                byte &= !(0xFF >> (8 - in_byte_offset) << (8 - in_byte_offset - self.width));

                debug_assert!(to_set <= 255);

                byte |= to_set as u8;

                unsafe { *addr = byte };

                // update all the state
                value <<= can_set;
                bit_offset += can_set;
                in_byte_offset = bit_offset % 8;
                byte_offset = (bit_offset - in_byte_offset) / 8;
                bits_left -= can_set;
            }
            true
        }
    }

    /// Length in number of bitslices cointained.
    pub fn len(&self) -> uint {
        self.entries
    }

    /// Size of the internal buffer, in bytes.
    pub fn byte_len(&self) -> uint {
        let w = self.entries * self.width;
        let r = w % 8;
        (w + r) / 8
    }

    pub fn iter<'a>(&'a self) -> Slices<'a> {
        Slices { idx: 0, bm: self }
    }

    /// Get the raw pointer to this Bitmap's data.
    pub unsafe fn get_ptr(&self) -> *mut u8 {
        self.data
    }

    /// Set the raw pointer to this Bitmap's data, returning the old one. It
    /// needs to be free'd with `libc::free` if the Bitmap was not made with
    /// `new_raw`. In general this operation should really be avoided. The
    /// destructor will call `libc::free` on the internal pointer.
    pub unsafe fn set_ptr(&mut self, ptr: *mut u8) -> *mut u8 {
        let p = self.data;
        self.data = ptr;
        p
    }
}

/// Iterator over the bitslices in the bitmap
pub struct Slices<'a> {
    idx: uint,
    bm: &'a Bitmap
}

impl<'a> Iterator<uint> for Slices<'a> {
    /// *NOTE*: This iterator is not "well-behaved", in that if you keep calling
    /// `next` after it returns None, eventually it will overflow and start
    /// yielding elements again. Use the `fuse` method to make this
    /// "well-behaved".
    fn next(&mut self) -> Option<uint> {
        let rv = self.bm.get(self.idx);
        self.idx += 1;
        rv
    }

    fn size_hint(&self) -> (uint, Option<uint>) {
        (self.bm.len(), Some(self.bm.len()))
    }
}

// The docs for RAI recommend that it's either an infinite iterator or a
// DoubleEndedIterator. This is neither.
impl<'a> std::iter::RandomAccessIterator<uint> for Slices<'a> {
    fn indexable(&self) -> uint {
        self.bm.len()
    }

    fn idx(&mut self, index: uint) -> Option<uint> {
        self.bm.get(index)
    }
}

#[cfg(test)]
mod test {
    use super::{get_n_bits_at, Bitmap};
    use std;

    #[test]
    fn empty() {
        let bm = Bitmap::new(10, 10).unwrap();

        for i in range(0u, 10) {
            assert_eq!(bm.get(i), Some(0));
        }

        assert_eq!(bm.get(11), None);
    }

    #[test]
    fn get() {
        let mut data: [u8, ..4] = [0b000_001_01, 0b0_011_100_1, 0b01_110_111, 0];
        let bm = Bitmap {
            entries: 8,
            width: 3,
            data: &mut data as *mut [u8, ..4] as *mut u8
        };

        for i in range(0u, 8) {
            assert_eq!(bm.get(i), Some(i));
        }

        assert_eq!(bm.get(8), None);
        assert_eq!(bm.get(9), None);

        // we don't use real data here, so don't bother freeing it
        let mut bm = bm;
        unsafe { bm.set_ptr(std::ptr::null_mut()); }
    }

    #[test]
    fn set() {
        let mut bm = Bitmap::new(10, 3).unwrap();

        for i in range(0u, 8) {
            assert!(bm.set(i, i));
            assert_eq!(bm.get(i), Some(i));
        }
        assert_eq!(bm.get(8), Some(0));
        assert_eq!(bm.get(9), Some(0));

        assert_eq!(bm.get(10), None);
    }

    #[test]
    fn get_n_bits() {
        macro_rules! t {
            ( $( $e:expr, $n:expr, $s:expr, $g:expr; )*  ) => (
                {
                    $(
                        assert_eq!(get_n_bits_at($e, $n, $s), $g);
                     )*
                }
            )
        }

        t! {
            0b00111001, 1, 0, 0b0;
            0b00111001, 8, 0, 0b00111001;
            0b11010101, 2, 0, 0b11;
            0b11010101, 2, 1, 0b10;
            0b11010101, 2, 2, 0b01;
            0b11010101, 2, 3, 0b10;
            0b11010101, 2, 4, 0b01;
            0b11010101, 3, 0, 0b110;
            0b11010101, 3, 1, 0b101;
            0b11010101, 3, 2, 0b010;
        }
    }

    #[test]
    fn iter() {
        let mut bm = Bitmap::new(10, 3).unwrap();

        bm.set(2, 0b101);
        bm.set(7, 0b110);

        let bs: Vec<uint> = bm.iter().collect();
        assert_eq!(bs.as_slice(), [0, 0, 0b101, 0, 0, 0, 0, 0b110, 0, 0].as_slice());
    }
}
