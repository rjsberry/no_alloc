use core::mem;

/// The layout of a block of memory.
///
/// This is, for the most part, a copy of the [same type from `alloc`].
///
/// [same type from `alloc`]: https://doc.rust-lang.org/stable/alloc/alloc/struct.Layout.html
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Layout {
    size:  usize,
    align: usize,
}

impl Layout {
    /// Constructs a `Layout` suitable for holding a value of type `T`.
    pub const fn new<T>() -> Self {
        Self { size: mem::size_of::<T>(), align: mem::align_of::<T>() }
    }

    /// The minimum size in bytes for a memory block of this layout.
    pub fn size(&self) -> usize { self.size }

    /// The minimum byte alignment for a memory block of this layout.
    pub fn align(&self) -> usize { self.align }
}
