//! Supposedly a "safe" way to create a custom DSTs with flexible array members.
//!
//! Currently, the main usage is FFI that uses a single allocation to return
//! both the API-consumable data and the backing storage for it at the same,
//! think inline strings or collections with dynamic item count.

#![cfg_attr(feature = "static-assert", feature(const_transmute))]
#![no_std]
#![deny(missing_docs)]

use core::{mem, slice};

#[cfg(feature = "static-assert")]
const _: () = {
    // As of writing, only the pointer layout to slices (`&[u8]`) and singular
    // trait objects (`&dyn Trait`) are defined, so make sure at compile-time
    // that the layout of such types isn't accidentally broken with next Rust
    // release.
    // See https://rust-lang.github.io/unsafe-code-guidelines/layout/pointers.html.
    macro_rules! check_dst_len {
        ($type: ty, $val: expr, $len: expr) => {{
            const VAL: &$type = &$val;

            const REPR: (*const (), usize) = unsafe { core::intrinsics::transmute(VAL) };
            static_assertions::const_assert_eq!(REPR.1, $len);
        }};
    }

    check_dst_len!(Tailed<(), [u8]>, Tailed { head: (), tail: [] }, 0);
    check_dst_len!(Tailed<u32, [u8]>, Tailed { head: 0, tail: [] }, 0);
    check_dst_len!(Tailed<u32, [u8]>, Tailed { head: 5, tail: [1] }, 1);
    check_dst_len!(Tailed<u32, [u8]>, Tailed { head: 8, tail: [1, 2] }, 2);
    check_dst_len!(Tailed<u32, [u8]>, Tailed { head: 42, tail: [1, 2, 3] }, 3);
    check_dst_len!(Tailed<u32, [u32]>, Tailed { head: 0xFFFF, tail: [1, 2, 3] }, 3);
};

/// A custom DST type.
///
/// One of the main usages is `Tailed<H, [T]>`, where the type has
/// a *flexible array member*.
#[derive(PartialEq, Debug)]
#[repr(C)]
pub struct Tailed<Head, Tail: ?Sized> {
    /// Leading, sized data part of the type.
    pub head: Head,
    /// Trailing, unsized data part of the type.
    pub tail: Tail,
}

impl<H, T> Tailed<H, [T]> {
    /// Constructs a fat pointer from a pointer to the header and the **count**
    /// of elements in the **trailing slice**.
    ///
    /// # Safety
    /// It's important to specify the *count of the trailing elements* rather
    /// than the size of the allocated data.
    /// ```
    /// # use tailed::Tailed;
    ///
    /// let slice = &[1, 2, 3, 4, 5];
    /// let (ptr, len) = (slice as *const i32, slice.len());
    /// let pointed = Tailed::<_, [i32]>::from_raw_parts(ptr, 4);
    /// let pointed = unsafe { &*pointed };
    ///
    /// let other = Tailed { head: 1i32, tail: [2, 3, 4, 5] };
    /// assert_eq!(pointed, &other as &Tailed::<_, [i32]>);
    /// assert_eq!(std::mem::size_of_val(pointed), std::mem::size_of_val(&other));
    /// ```
    pub fn from_raw_parts(data: *const H, count: usize) -> *const Self {
        // https://users.rust-lang.org/t/construct-fat-pointer-to-struct/29198/9
        // Requirements of slice::from_raw_parts.
        assert!(!data.is_null());
        assert!(count * mem::size_of::<T>() <= core::isize::MAX as usize);

        let slice = unsafe { slice::from_raw_parts(data as *const (), count) };
        slice as *const [()] as *const Self
    }

    /// Constructs a fat pointer from a pointer to the header and the count
    /// of **elements** in the **trailing slice**.
    ///
    /// # Safety
    /// The pointer to header must be correctly aligned.
    /// ```
    /// # use tailed::Tailed;
    /// use std::boxed::Box;
    ///
    /// let slice = vec![1, 2, 3, 4, 5].into_boxed_slice();
    /// let (len, ptr) = (slice.len(), Box::into_raw(slice));
    /// let pointed = Tailed::<_, [i32]>::from_raw_parts_mut(ptr as *mut i32, 4);
    /// let pointed = unsafe { &mut *pointed };
    ///
    /// let other = Tailed { head: 1i32, tail: [2, 3, 4, 5] };
    /// assert_eq!(pointed, &other as &Tailed::<_, [i32]>);
    /// assert_eq!(std::mem::size_of_val(pointed), std::mem::size_of_val(&other));
    /// ```
    pub fn from_raw_parts_mut(data: *mut H, count: usize) -> *mut Self {
        // https://users.rust-lang.org/t/construct-fat-pointer-to-struct/29198/9
        // Requirements of slice::from_raw_parts.
        assert!(!data.is_null());
        assert!(count * mem::size_of::<T>() <= core::isize::MAX as usize);

        let slice = unsafe { slice::from_raw_parts_mut(data as *mut (), count) };
        slice as *mut [()] as *mut Self
    }
}

impl<H> Tailed<mem::MaybeUninit<H>, [u8]> {
    /// Creates a Tailed view into a slice of bytes.
    /// ```
    /// #![feature(maybe_uninit_extra)]
    /// # use tailed::Tailed;
    /// use core::mem::MaybeUninit;
    ///
    /// #[derive(PartialEq, Debug)]
    /// #[repr(C)]
    /// struct Header { a: u16, b: u8 };
    ///
    /// let bytes: Box<[u8]> = vec![0x01, 0x01, 0x02, 0xFF, 0x03, 0x04].into();
    ///
    /// let tailed = Tailed::<MaybeUninit<Header>, _>::from_bytes(&bytes);
    /// assert_eq!(unsafe { tailed.head.read() }, Header {a: 0x0101, b: 0x02 });
    /// assert_eq!(&tailed.tail, &[0x03, 0x04]);
    /// ```
    ///
    /// # Safety
    /// The passed reference **MUST** be aligned in a compatible fashion, as if
    /// it was an reference to dynamically-sized `Self`.
    ///
    /// The data buffer also **MUST** be *at least* `mem::size_of::<H>()` bytes
    /// long and be *properly aligned* (e.g. to account for trailing padding).
    ///
    /// Moreover, since we can't guarantee that the raw bytes correspond to a
    /// correctly initialized value of type `H`, it is the caller's
    /// responsibility to assert that.
    ///
    /// # Panics
    /// When any of the above safety preconditions are violated.
    pub fn from_bytes(data: &[u8]) -> &Self {
        Self::from_bytes_with_length(data, core::usize::MAX)
    }

    /// Creates a Tailed view into a slice of bytes with specifically `len`
    /// trailing bytes (any bytes after that are simply treated as padding).
    ///
    /// Valid trailing byte count range is `[0; mem::size_of_val(data) - mem::size_of::<H>()]`.
    /// Specify `usize::MAX` to include as many bytes in the tail byte slice as possible.
    ///
    /// ```
    /// #![feature(maybe_uninit_extra)]
    /// # use tailed::Tailed;
    /// use core::mem::MaybeUninit;
    ///
    /// #[derive(PartialEq, Debug)]
    /// #[repr(C)]
    /// struct Header { a: u16, b: u8 };
    ///
    /// let bytes: Box<[u8]> = vec![0x01, 0x01, 0x02, 0xFF, 0x03, 0xFF].into();
    ///
    /// let tailed = Tailed::<MaybeUninit<Header>, _>::from_bytes_with_length(&bytes, 1);
    /// assert_eq!(unsafe { tailed.head.read() }, Header {a: 0x0101, b: 0x02 });
    /// assert_eq!(&tailed.tail, &[0x03]);
    /// // Header is 4 bytes and there are 2 trailing bytes, despite tail having 1.
    /// assert_eq!(core::mem::size_of_val(tailed), 6);
    /// let tailed = Tailed::<MaybeUninit<Header>, _>::from_bytes_with_length(&bytes, 0);
    /// assert_eq!(&tailed.tail, &[]);
    /// let tailed = Tailed::<MaybeUninit<Header>, _>::from_bytes_with_length(&bytes, core::usize::MAX);
    /// assert_eq!(&tailed.tail, &[0x03, 0xFF]);
    /// ```
    ///
    /// # Safety
    /// In addition to upholding safety preconditions outlined in `from_bytes`,
    /// the passed `len` must be not bigger than the trailing byte count after
    /// header `H` type (including its padding).
    ///
    /// # Panics
    /// When any of the above preconditions are violated.
    pub fn from_bytes_with_length(data: &[u8], len: usize) -> &Self {
        // Every reference must be well-aligned, and DSTs are no exception. We
        // basically transmute the input reference, so make sure this operation
        // is well-defined.
        // NOTE: Due to run-time nature of DSTs, we can't simply calculate
        // `mem::align_of::<&Self>` here and must use run-time version, instead.
        let empty: &Self = &Tailed {
            head: mem::MaybeUninit::uninit(),
            tail: [],
        };
        assert!(
            data.as_ptr() as usize % mem::align_of_val(empty) == 0,
            "the passed `data` reference is not correctly aligned"
        );
        // In order to create a valid reference, the memory region referred by
        // it, even if not accessed, must be valid for a single allocated object.
        // Because of this, we need to make sure that the possible trailing
        // padding bytes, as possibly required by the ABI, are in fact in the
        // input buffer and not at the allocation boundaries.
        assert!(
            mem::size_of_val(data) % mem::align_of_val(empty) == 0,
            "the passed `data` buffer is not correctly aligned wrt. padding"
        );
        // Explicitly account for size of header type `H`, including its
        // possible trailing padding, not to mistakingly include any
        // layout-specific bytes in the tail.
        assert!(
            mem::size_of_val(data) >= mem::size_of::<H>(),
            "the passed buffer is not big enough to contain header of type `H`"
        );

        let tail_bytes = mem::size_of_val(data) - mem::size_of::<H>();
        let tail_bytes = if len == core::usize::MAX {
            tail_bytes
        } else {
            assert!(len <= tail_bytes, "trailing byte count is invalid (too big");
            len
        };

        unsafe { Self::from_bytes_unchecked_with_length(data, tail_bytes) }
    }

    /// Unchecked version of `from_bytes` that can also specify the tail byte
    /// length manually.
    pub unsafe fn from_bytes_unchecked_with_length(data: &[u8], len: usize) -> &Self {
        let ptr = data as *const _ as *const H;
        let result = &*Self::from_raw_parts(ptr as *const _, len);

        result
    }

    /// Assumes that the header part of the DST is correctly initialized,
    /// yielding a read-only typed view into underlying storage.
    ///
    /// This does not invoke any drop glue for the inner type and only provides
    /// read access to the underlying value.
    /// ```
    /// # use tailed::Tailed;
    /// use core::mem::MaybeUninit;
    ///
    /// #[derive(PartialEq, Debug)]
    /// #[repr(C)]
    /// struct Header { a: u16, b: u8 };
    ///
    /// let bytes: Box<[u8]> = vec![0x01, 0x01, 0x02, 0xFF, 0x03, 0x04].into();
    ///
    /// let tailed = Tailed::<MaybeUninit<Header>, _>::from_bytes(&bytes);
    /// let init: &Tailed<Header, _> = unsafe { Tailed::from_bytes(&bytes).assume_init() };
    /// assert_eq!(&init.head, &Header { a: 0x0101, b: 0x02});
    /// assert_eq!(&init.tail, &[0x03, 0x04]);
    /// ```
    pub unsafe fn assume_init(&self) -> &Tailed<H, [u8]> {
        // `MaybeUninit<H>` is safe to transmute to `H` and is *not* undefined
        // behaviour, as long as the underlying value is properly initialized.
        mem::transmute(self)
    }
}
