#![crate_id = "bitmap#1.0.0"]
#![crate_type = "rlib"]
#![crate_type = "dylib"]

//! See the `Bitmap` type.

extern crate libc;

use std;
use std::num::CheckedDiv;

/// A dense bitmap, intended to store small bitslices (<= width of uint).
pub struct Bitmap {
    entries: uint,
    width: uint,
    // we avoid a vector here because we have our own bounds checking, and
    // don't need to duplicate the length.
    data: *mut u8,
}

fn get_n_bits_at(byte: u8, n: u8, start: u8) -> u8 {
    (byte >> (8-n-start)) & (0xFF >> (8-n))
}

impl Bitmap {
    /// Create a new bitmap, returning None if the data can't be allocated or
    /// if the width of each slice can't fit in a uint. entries * width must
    /// not overflow uint.
    pub fn new(entries: uint, width: uint) -> Option<Bitmap> {
        if width > (std::mem::size_of::<uint>() * 8) {
            None
        } else {
            entries.checked_mul(&width)
            .and_then(|bits| bits.checked_add( &(8 - (bits % 8)) ))
            .and_then(|rbits| rbits.checked_div(&8))
            .and_then(|needed| {
                // can't use ~ or ~[] because they fail on failure to allocate. this needs to be
                // more resilient to failure.
                let ptr = unsafe { libc::malloc(needed as u64) };

                if ptr == std::ptr::mut_null() {
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

                debug!("can_get = {}, bit_offset = {}, in_byte_offset = {}, byte_offset = {}, bits_left = {}",
                        can_get, bit_offset, in_byte_offset, byte_offset, bits_left);

                // alright, pull them out.
                let byte = unsafe { *self.data.offset(byte_offset as int) };
                debug!("byte is {:t}", byte);
                let got = get_n_bits_at(byte, can_get as u8, in_byte_offset as u8) as uint;
                debug!("got {:t}", got);

                // make room for the bits we just read
                value <<= can_get;
                value |= got;

                debug!("value is now {:t}", value);

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
            debug!("value is {:t}", value);
            value <<= uintbits - self.width;
            debug!("we shifted it into {:t}", value);

            let mut bit_offset = i * self.width;

            let mut in_byte_offset = bit_offset % 8;
            let mut byte_offset = (bit_offset - in_byte_offset) / 8;

            let mut bits_left = self.width;

            while bits_left > 0 {
                let can_set = std::cmp::min(8 - in_byte_offset, bits_left);

                debug!("can_set = {}, bit_offset = {}, in_byte_offset = {}, byte_offset = {}, bits_left = {}",
                        can_set, bit_offset, in_byte_offset, byte_offset, bits_left);

                // pull out the highest can_set bits from value
                let mut to_set: uint = value >> (uintbits - can_set);
                debug!("to_set is {:t}", to_set);
                // move them into where they will live
                to_set <<= 8 - can_set - in_byte_offset;
                debug!("and now it's {:t}", to_set);

                let addr = unsafe { self.data.offset(byte_offset as int) };
                let mut byte = unsafe { *addr };

                debug!("found byte {:t}", byte);
                // clear the bits we'll be setting
                byte &= !(0xFF >> (8 - in_byte_offset) << (8 - in_byte_offset - self.width));
                debug!("cleared some bits to get {:t}", byte);

                assert!(to_set <= 255, "oh no! {:t} doesn't fit in a byte :(", to_set);

                byte |= to_set as u8;

                debug!("all done, storing {:t}", byte);

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
}

#[cfg(test)]
mod test {
    use super::{get_n_bits_at, Bitmap};

    #[test]
    fn bitmap_empty() {
        let bm = Bitmap::new(10, 10).unwrap();

        for i in range(0u, 10) {
            debug!("i is {}", i);
            assert_eq!(bm.get(i), Some(0));
        }

        assert_eq!(bm.get(11), None);
    }

    #[test]
    fn bitmap_get() {
        let mut data: [u8, ..4] = [0b000_001_01, 0b0_011_100_1, 0b01_110_111, 0];
        let bm = Bitmap {
            entries: 8,
            width: 3,
            data: &mut data as *mut [u8, ..4] as *mut u8
        };

        for i in range(0u, 8) {
            debug!("i is {}", i);
            assert_eq!(bm.get(i), Some(i));
        }

        assert_eq!(bm.get(8), None);
        assert_eq!(bm.get(9), None);
    }

    #[test]
    fn bitmap_set() {
        let mut bm = Bitmap::new(10, 3).unwrap();

        for i in range(0u, 8) {
            debug!("i is {}", i);
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
}
