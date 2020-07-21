use super::{Allocator, CapacityError, Layout, PadToAlignment};

use core::cell::Cell;
use core::ptr::NonNull;

/// A `!Sync` linear allocator using purely static memory.
pub struct UnsyncLinearAllocator {
    start:    Cell<usize>,
    tail:     Cell<usize>,
    capacity: Cell<usize>,
    counter:  Cell<usize>,
}

impl UnsyncLinearAllocator {
    /// Creates a new `!Sync` linear allocator.
    pub const fn uninit() -> Self {
        Self {
            start:    Cell::new(0x0),
            tail:     Cell::new(0x0),
            capacity: Cell::new(0),
            counter:  Cell::new(0),
        }
    }

    /// Initializes the allocator with the given memory block.
    ///
    /// # Panics
    ///
    /// Panics if the allocator has already been initialized.
    pub fn init(&self, buf: &'static mut [u8]) {
        assert_eq!(self.start.get(), 0x0, "already initialized");
        self.start.set(buf.as_ptr() as _);
        self.tail.set(buf.as_ptr() as _);
        self.capacity.set(buf.len());
    }
}

impl Allocator for UnsyncLinearAllocator {
    unsafe fn alloc(
        &self,
        layout: Layout,
    ) -> Result<NonNull<u8>, CapacityError> {
        assert_ne!(self.start.get(), 0x0, "uninitialized allocator");

        let new_head = self.tail.get().pad_to_alignment(layout.align());
        debug_assert_ne!(new_head, 0x0);
        debug_assert_eq!(new_head % layout.align(), 0);

        if new_head + layout.size() - self.capacity.get() <= self.start.get() {
            self.tail.set(new_head + layout.size());
            self.counter.set(self.counter.get() + 1);
            Ok(NonNull::new_unchecked(new_head as _))
        } else {
            Err(CapacityError::new())
        }
    }

    unsafe fn dealloc(&self, _: NonNull<u8>) {
        let count = self.counter.get();
        self.counter.set(count - 1);
        if count == 1 {
            self.tail.set(self.start.get());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{super::static_buf, *};

    use core::mem;

    #[test]
    fn smoke() {
        let a = UnsyncLinearAllocator::uninit();
        a.init(static_buf![0; 3 * mem::size_of::<i32>() - 1]);
        let layout = Layout::new::<i32>();
        unsafe {
            let ptr = a.alloc(layout).unwrap();
            let ptr2 = a.alloc(layout).unwrap();
            assert!(a.alloc(layout).is_err());
            a.dealloc(ptr2);
            assert!(a.alloc(layout).is_err());
            a.dealloc(ptr);
            let _ptr = a.alloc(layout).unwrap();
            let _ptr2 = a.alloc(layout).unwrap();
        }
    }

    #[test]
    #[should_panic]
    fn already_initialized() {
        let a = UnsyncLinearAllocator::uninit();
        a.init(static_buf![0; 0]);
        a.init(static_buf![0; 0]);
    }
}
