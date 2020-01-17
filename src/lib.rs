#![cfg_attr(feature = "static-assert", feature(const_transmute))]
#![no_std]

#[cfg(feature = "static-assert")]
const _: () = {
    // As of writing, only the pointer layout to slices (`&[u8]`) and singular
    // trait objects (`&dyn Trait`) are defined, so make sure at compile-time
    // that the layout of such types isn't accidentally broken.
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

#[repr(C)]
pub struct Tailed<Head, Tail: ?Sized> {
    pub head: Head,
    pub tail: Tail,
}
