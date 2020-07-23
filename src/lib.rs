//! Static memory allocators for applications without heap.
//!
//! # Usage
//!
//! `no_alloc` can be used to create boxes for dynamically sized types without
//! heap allocation:
//!
//! ```ignore
//! #![no_std]
//! #![no_main]
//!
//! extern crate libc;
//!
//! use core::any::Any;
//! use no_alloc::{stack_boxed, StackBox};
//!
//! #[no_mangle]
//! pub extern "C" fn main(_argc: isize, _argv: *const *const u8) -> isize {
//!     let boxed: StackBox<dyn Any, [usize; 1]> = stack_boxed!(0_isize);
//!     if let Ok(_) = boxed.downcast::<isize>().map(|v| *v) {
//!         0
//!     } else {
//!         1
//!     }
//! }
//!
//! #[panic_handler]
//! fn my_panic(_info: &core::panic::PanicInfo) -> ! {
//!     loop {}
//! }
//! ```
//!
//! Compile-time assertions are made to ensure that pointers will always be
//! backed by enough memory and have the correct alignment. The following will
//! fail to compile:
//!
//! ```compile_fail
//! use core::any::Any;
//! use no_alloc::StackBox;
//!
//! let _impossible: StackBox<dyn Any, [usize; 0]> = stack_boxed!(0_isize);
//! ```
//!
//! For more information, consult the documentation for [`StackBox::new`].
//!
//! [`StackBox::new`]: struct.StackBox.html#method.new
//!
//! # Dependencies
//!
//! `no_alloc` has no runtime dependencies.
//!
//! # Features
//!
//! * `coerce_unsized`
//!
//!   **This feature requires a nightly toolchain**
//!
//!   Implements [`CoerceUnsized`] for [`StackBox`], circumventing the requirement
//!   for the [`stack_boxed`] macro:
//!
//!   ```
//!   # #[cfg(feature = "coerce_unsized")]
//!   # {
//!   use core::any::Any;
//!   use no_alloc::StackBox;
//!
//!   let boxed: StackBox<dyn Any, [usize; 1]> = StackBox::new(0_isize);
//!   # }
//!   ```
//!
//!   [`CoerceUnsized`]: https://doc.rust-lang.org/stable/core/ops/trait.CoerceUnsized.html
//!   [`StackBox`]: struct.StackBox.html
//!   [`stack_boxed`]: macro.boxed.html
//!
//! * `const_generics`
//!
//!   **This feature requires a nightly toolchain**
//!
//!   Implements [`Memory`] for arrays of any aribtrary length, rather than
//!   a few select lengths.
//!
//!   [`Memory`]: trait.Memory.html
//!
//! # Safety
//!
//! Safety is paramount to `no_alloc`.
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
#![cfg_attr(feature = "const_generics", feature(const_generics))]

mod allocator;
mod assert;
mod assert_unsync_safe;
mod boxed;
mod capacity_error;
mod global_allocator;
mod layout;
mod mem;
mod pad_to_alignment;
mod ptr;
mod raw;
mod stack_boxed;
mod static_buf;
mod unsync_linear_allocator;

use pad_to_alignment::PadToAlignment;

pub use allocator::Allocator;
pub use assert_unsync_safe::AssertUnsyncSafe;
pub use boxed::Box;
pub use capacity_error::CapacityError;
pub use global_allocator::GlobalAllocator;
pub use layout::Layout;
pub use mem::Memory;
pub use stack_boxed::StackBox;
pub use unsync_linear_allocator::UnsyncLinearAllocator;
