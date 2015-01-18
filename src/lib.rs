//! See the `Bitmap` type.

#[macro_use] extern crate log;

use std::num::Int;
use std::rt::heap;

/// A dense bitmap, intended to store small bitslices (<= width of usize).
#[unsafe_no_drop_flag]
pub struct Bitmap {
    entries: usize,
    width: usize,
    // Avoid a vector here because we have our own bounds checking, and
    // don't want to duplicate the length, or panic.
    data: *mut u8,
}

fn get_n_bits_at(byte: u8, n: u8, start: u8) -> u8 {
    (byte >> (8-n-start) as usize) & (0xFF >> (8-n) as usize)
}

impl Drop for Bitmap {
    fn drop(&mut self) {
        let p = self.data;
        if p != 0 as *mut _ {
            self.data = 0 as *mut _;
            unsafe { heap::deallocate(p as *mut u8, self.byte_len(), std::mem::align_of::<u8>()) }
        }
    }
}

impl Bitmap {
    /// Create a new bitmap, returning None if the data can't be allocated or
    /// if the width of each slice can't fit in a usize. entries * width must
    /// not overflow usize.
    pub fn new(entries: usize, width: usize) -> Option<Bitmap> {
        if width > (std::mem::size_of::<usize>() * 8) {
            None
        } else {
            entries.checked_mul(width)
            .and_then(|bits| bits.checked_add(8 - (bits % 8)))
            .and_then(|rbits| rbits.checked_div(8))
            .and_then(|needed| {
                // can't use Box or Vec because they panic on failure to allocate. this needs to be
                // more resilient to failure.
                let ptr = unsafe { heap::allocate(needed, std::mem::align_of::<u8>()) };

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
    pub unsafe fn new_raw(entries: usize, width: usize, ptr: *mut u8) -> Option<Bitmap> {
        if width > (std::mem::size_of::<usize>() * 8) {
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
    pub fn get(&self, i: usize) -> Option<usize> {
        if i >= self.entries {
            None
        } else {
            let mut bit_offset = i * self.width;

            let mut in_byte_offset = bit_offset % 8;
            let mut byte_offset = (bit_offset - in_byte_offset) / 8;

            let mut bits_left = self.width;

            let mut value: usize = 0;

            while bits_left > 0 {
                // how many bits can we need to set in this byte?
                let can_get = std::cmp::min(8 - in_byte_offset, bits_left);

                // alright, pull them out.
                let byte = unsafe { *self.data.offset(byte_offset as isize) };
                let got = get_n_bits_at(byte, can_get as u8, in_byte_offset as u8) as usize;

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
    pub fn set(&mut self, i: usize, mut value: usize) -> bool {
        let usize = std::mem::size_of::<usize>() * 8;
        if i >= self.entries || value & !(-1 >> (usize - self.width)) != 0 {
            false
        } else {
            // shift over into the high bits
            value <<= usize - self.width;

            let mut bit_offset = i * self.width;

            let mut in_byte_offset = bit_offset % 8;
            let mut byte_offset = (bit_offset - in_byte_offset) / 8;

            let mut bits_left = self.width;

            while bits_left > 0 {
                let can_set = std::cmp::min(8 - in_byte_offset, bits_left);

                // pull out the highest can_set bits from value
                let mut to_set: usize = value >> (usize - can_set);
                // move them into where they will live
                to_set <<= 8 - can_set - in_byte_offset;

                let addr = unsafe { self.data.offset(byte_offset as isize) };
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
    pub fn len(&self) -> usize {
        self.entries
    }

    /// Size of the internal buffer, in bytes.
    pub fn byte_len(&self) -> usize {
        // can't overflow, since creation asserts that it doesn't.
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
    idx: usize,
    bm: &'a Bitmap
}

impl<'a> Iterator for Slices<'a> {
    type Item = usize;
    /// *NOTE*: This iterator is not "well-behaved", in that if you keep calling
    /// `next` after it returns None, eventually it will overflow and start
    /// yielding elements again. Use the `fuse` method to make this
    /// "well-behaved".
    fn next(&mut self) -> Option<usize> {
        let rv = self.bm.get(self.idx);
        self.idx += 1;
        rv
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.bm.len(), Some(self.bm.len()))
    }
}

// The docs for RAI recommend that it's either an infinite iterator or a
// DoubleEndedIterator. This is neither.
impl<'a> std::iter::RandomAccessIterator for Slices<'a> {
    fn indexable(&self) -> usize {
        self.bm.len()
    }

    fn idx(&mut self, index: usize) -> Option<usize> {
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

        for i in range(0, 10) {
            assert_eq!(bm.get(i), Some(0));
        }

        assert_eq!(bm.get(11), None);
    }

    #[test]
    fn get() {
        let mut data: [u8; 4] = [0b000_001_01, 0b0_011_100_1, 0b01_110_111, 0];
        let bm = Bitmap {
            entries: 8,
            width: 3,
            data: &mut data as *mut [u8; 4] as *mut u8
        };

        for i in range(0, 8) {
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

        for i in range(0, 8) {
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

        let bs: Vec<usize> = bm.iter().collect();
        assert_eq!(bs.as_slice(), [0, 0, 0b101, 0, 0, 0, 0, 0b110, 0, 0].as_slice());
    }
}
