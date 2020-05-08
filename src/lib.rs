//! Embedded friendly smart pointers for `no_std` applications without heap
//! allocators.
//!
//! # Usage
//!
//! `no_ptr` can be used to create boxes for dynamically sized types without
//! heap allocation:
//!
//! ```ignore
//! #![no_main]
//! #![no_std]
//!
//! use core::any::Any;
//!
//! use cortex_m_rt::entry;
//! use no_ptr::{boxed_s, BoxS};
//!
//! #[entry]
//! fn main() -> ! {
//!     let boxed: BoxS<dyn Any, [usize; 1]> = boxed_s!(0_isize);
//!     assert_eq!(boxed.downcast_ref::<isize>(), Some(&0));
//!     loop {
//!         // Application logic
//!     }
//! }
//! ```
//!
//! Compile-time assertions are made to ensure that pointers will always be
//! backed by enough memory and have the correct alignment. The following will
//! fail to compile:
//!
//! ```compile_fail
//! use core::any::Any;
//! use no_ptr::BoxS;
//!
//! let _impossible: BoxS<dyn Any, [usize; 0]> = boxed_s!(0_isize);
//! ```
//!
//! For more information, consult the documentation for [`BoxS::new`].
//!
//! [`BoxS::new`]: struct.BoxS.html#method.new
//!
//! # Dependencies
//!
//! `no_ptr` has no runtime dependencies.
//!
//! [`heapless`] can be optionally brought in to add support for boxes backed by
//! global memory pools by activating the `pool` feature.
//!
//! [`heapless`]: https://docs.rs/heapless
//!
//! # Features
//!
//! * `coerce_unsized` (requires a nightly toolchain)
//!
//!   Implements [`CoerceUnsized`] for [`BoxS`], circumventing the requirement
//!   for the [`boxed_s`] macro:
//!
//!   ```
//!   # #[cfg(feature = "coerce_unsized")]
//!   # {
//!   use core::any::Any;
//!   use no_ptr::BoxS;
//!
//!   let boxed: BoxS<dyn Any, [usize; 1]> = BoxS::new(0_isize);
//!   # }
//!   ```
//!
//!   [`CoerceUnsized`]: https://doc.rust-lang.org/stable/core/ops/trait.CoerceUnsized.html
//!   [`BoxS`]: struct.BoxS.html
//!   [`boxed_s`]: macro.boxed.html
//!
//! # Safety
//!
//! Safety is paramount to `no_ptr`.
//!
//! It works on top of a lot of unsafe code, but the exposed APIs are 100% safe.
//!
//! The crate is extensively tested, and these tests are run through [**Miri**]
//! as part of the CI for the crate. Commits that fail the [**Miri**] stage
//! cannot be merged to master and are forbidden from being released to
//! [crates.io].
//!
//! [**Miri**]: https://github.com/rust-lang/miri
//! [crates.io]: https://crates.io

#![no_std]
#![cfg_attr(rustdoc, feature(doc_cfg))]
#![cfg_attr(feature = "coerce_unsized", feature(coerce_unsized, unsize))]

mod assert;
mod boxed_s;
mod mem;

pub use boxed_s::BoxS;
pub use mem::Memory;

#[cfg(feature = "pool")]
mod arc;
#[cfg(feature = "pool")]
mod boxed;

#[cfg(feature = "pool")]
pub use arc::Arc;
#[cfg(feature = "pool")]
pub use boxed::Box;

/*
    Unit tests
*/

#[cfg(test)]
mod tests {
    use super::*;

    use core::any::Any;
    use core::sync::atomic::{AtomicBool, Ordering};

    #[cfg(feature = "pool")]
    use heapless::pool::singleton::Pool;

    #[cfg(feature = "pool")]
    macro_rules! pool {
        ($(#[$($attr:tt)*])* $ident:ident: $ty:ty) => {
            pub struct $ident { inner: heapless::pool::Pool<$ty> }
            unsafe impl Sync for $ident {}
            impl heapless::pool::singleton::Pool for $ident {
                type Data = $ty;
                fn ptr() -> &'static heapless::pool::Pool<$ty> {
                    $(#[$($attr)*])*
                    static $ident: $ident = $ident { inner: heapless::pool::Pool::new() };
                    &$ident.inner
                }
            }
        }
    }

    #[test]
    fn smoke() {
        let mut boxed = BoxS::<usize, [usize; 1]>::new(0);
        assert_eq!(*boxed, 0);
        *boxed = 1;
        assert_eq!(*boxed, 1);
    }

    #[test]
    fn boxed_s_macro() {
        let _boxed: BoxS<dyn Any, [usize; 1]> = boxed_s!(0_usize);
    }

    #[cfg(feature = "coerce_unsized")]
    #[test]
    fn coerce_unsized() {
        let _boxed: BoxS<dyn Any, [usize; 1]> = BoxS::new(0_usize);
    }

    #[test]
    fn zst() {
        let mut boxed = BoxS::<(), [usize; 0]>::new(());
        assert_eq!(*boxed, ());
        *boxed = ();
    }

    #[test]
    fn drop() {
        struct Foo<'a>(&'a AtomicBool);
        impl Drop for Foo<'_> {
            fn drop(&mut self) {
                self.0.store(true, Ordering::Relaxed);
            }
        }

        let dropped = AtomicBool::new(false);
        let foo = Foo(&dropped);
        let boxed = BoxS::<_, [usize; 1]>::new(foo);
        assert!(!dropped.load(Ordering::Relaxed));
        core::mem::drop(boxed);
        assert!(dropped.load(Ordering::Relaxed));
    }

    #[test]
    fn any() {
        let boxed: BoxS<dyn Any, [usize; 1]> = boxed_s!(0_usize);
        assert_eq!(*boxed.downcast::<usize>().ok().unwrap(), 0);
        let boxed: BoxS<dyn Any + Send, [usize; 1]> = boxed_s!(0_usize);
        assert_eq!(*boxed.downcast::<usize>().ok().unwrap(), 0);
    }

    #[cfg(feature = "pool")]
    #[test]
    fn box_smoke() {
        pool!(P: [usize; 1]);
        static mut DATA: [u8; 32] = [0; 32];
        assert!(P::grow(unsafe { &mut DATA }) >= 1);
        let mut boxed = Box::<usize, P>::new(0).unwrap();
        assert_eq!(*boxed, 0);
        *boxed = 1;
        assert_eq!(*boxed, 1);
    }

    #[cfg(feature = "pool")]
    #[test]
    fn box_drop() {
        pool!(P: [usize; 1]);
        static mut DATA: [u8; 2 * core::mem::size_of::<usize>()] = [0; 2 * core::mem::size_of::<usize>()];
        assert!(P::grow(unsafe { &mut DATA }) >= 1);

        #[derive(Debug)]
        struct Foo<'a>(&'a AtomicBool);
        impl Drop for Foo<'_> {
            fn drop(&mut self) {
                self.0.store(true, Ordering::Relaxed);
            }
        }

        let dropped = AtomicBool::new(false);
        let foo = Foo(&dropped);
        let boxed = Box::<_, P>::new(foo).unwrap();
        assert!(!dropped.load(Ordering::Relaxed));
        core::mem::drop(boxed);
        assert!(dropped.load(Ordering::Relaxed));
    }
}
