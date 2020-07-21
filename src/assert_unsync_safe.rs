use super::{Allocator, CapacityError, Layout};

use core::cell::UnsafeCell;
use core::ops::{Deref, DerefMut};
use core::ptr::NonNull;

/// A simple wrapper type to permit static usage of `!Sync` types.
#[derive(Debug, Default)]
pub struct AssertUnsyncSafe<T>(UnsafeCell<T>);

unsafe impl<T> Sync for AssertUnsyncSafe<T> {}

impl<T> AssertUnsyncSafe<T> {
    /// Creates a new wrapper to assert that an item is in fact going to be
    /// safely used in cases where it would otherwise need to be `Sync`.
    ///
    /// # Safety
    ///
    /// This function itself isn't inherently unsafe, however it permits
    /// otherwise unsafe usage of `T` if used improperly.
    #[inline]
    pub const unsafe fn new(inner: T) -> Self { Self(UnsafeCell::new(inner)) }
}

impl<T> Deref for AssertUnsyncSafe<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target { unsafe { &*self.0.get() } }
}

impl<T> DerefMut for AssertUnsyncSafe<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut <Self as Deref>::Target {
        unsafe { &mut *self.0.get() }
    }
}

impl<T: Allocator> Allocator for AssertUnsyncSafe<T> {
    unsafe fn alloc(
        &self,
        layout: Layout,
    ) -> Result<NonNull<u8>, CapacityError> {
        Allocator::alloc(&**self, layout)
    }

    unsafe fn dealloc(&self, node: NonNull<u8>) {
        Allocator::dealloc(&**self, node)
    }
}
