use super::{CapacityError, Layout};

use core::ptr::NonNull;

/// A memory allocator.
pub trait Allocator {
    /// Allocates a memory block described by the given layout.
    unsafe fn alloc(
        &self,
        layout: Layout,
    ) -> Result<NonNull<u8>, CapacityError>;

    /// Deallocates the memory block.
    unsafe fn dealloc(&self, node: NonNull<u8>);
}
