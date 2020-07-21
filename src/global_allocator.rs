use super::{Allocator, CapacityError, Layout};

use core::ptr::NonNull;

/// A memory allocator that is global accessible.
pub trait GlobalAllocator {
    /// The underlying allocator that this global allocator defers to.
    type Delegate: Allocator + 'static;

    /// Obtains a static reference to the delegate allocator.
    fn static_ref() -> &'static Self::Delegate;

    /// Allocates a memory block described by the given layout.
    unsafe fn alloc(layout: Layout) -> Result<NonNull<u8>, CapacityError> {
        Allocator::alloc(Self::static_ref(), layout)
    }

    /// Deallocates the memory block.
    unsafe fn dealloc(node: NonNull<u8>) {
        Allocator::dealloc(Self::static_ref(), node)
    }
}

/// Creates a global allocator.
#[macro_export]
macro_rules! global_allocator {
    (
        type $allocator:ident = $delegate:ty;
        const unsafe fn $init:ident() -> $_:ty $delegate_init:block
    ) => {
        enum $allocator {}
        $crate::__global_allocator_impl! {
            @unsafe $allocator, $delegate, $init, $delegate_init
        }
    };
    (type $allocator:ident = $delegate:ty;) => {
        enum $allocator {}
        $crate::__global_allocator_impl! { $allocator, $delegate }
    };
    (pub type $allocator:ident = $delegate:ty;) => {
        pub enum $allocator {}
        $crate::__global_allocator_impl! { $allocator, $delegate }
    };
    (pub($($vis:tt)+) type $allocator:ident = $delegate:ty;) => {
        pub($($vis)+) enum $allocator {}
        $crate::__global_allocator_impl! { $allocator, $delegate }
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! __global_allocator_impl {
    (@unsafe $allocator:ident, $delegate:ty, $init:ident, $delegate_init:block) => {
        const unsafe fn $init() -> $delegate $delegate_init
        impl $crate::GlobalAllocator for $allocator {
            type Delegate = $delegate;
            fn static_ref() -> &'static Self::Delegate {
                static _DELEGATE: $delegate = unsafe { $init() };
                &_DELEGATE
            }
        }
    };
}

#[cfg(test)]
mod tests {
    use super::{
        super::{static_buf, AssertUnsyncSafe, UnsyncLinearAllocator},
        *,
    };

    use core::mem;

    #[test]
    fn smoke() {
        global_allocator! {
            type A = AssertUnsyncSafe<UnsyncLinearAllocator>;
            const unsafe fn init() -> A {
                AssertUnsyncSafe::new(UnsyncLinearAllocator::uninit())
            }
        }

        A::static_ref().init(static_buf![0; 2 * mem::size_of::<i32>() - 1]);
        let layout = Layout::new::<i32>();

        unsafe {
            let ptr = A::alloc(layout).unwrap();
            assert!(A::alloc(layout).is_err());
            A::dealloc(ptr);
            let _ptr = A::alloc(layout).unwrap();
        }
    }
}
