use crate::assert::StaticAssertions;
use crate::mem::{write_ptr_addr, Memory};

use core::any::Any;
use core::fmt;
use core::mem::{self, ManuallyDrop, MaybeUninit};
use core::ops;
use core::ptr;

#[cfg(feature = "coerce_unsized")]
use core::marker::Unsize;
#[cfg(feature = "coerce_unsized")]
use core::ops::CoerceUnsized;

use heapless::pool::{
    singleton::{Box as HBox, Pool},
    Init,
};

/// A box belonging to the global memory pool.
#[cfg_attr(rustdoc, doc(cfg(feature = "pool")))]
pub struct Box<T, P>
where
    T: ?Sized,
    P: Pool,
    P::Data: Memory,
{
    buf: ManuallyDrop<HBox<P, Init>>,
    ptr: *mut T,
}

/// Box a value with the global memory pool.
///
/// This macro behaves exactly the same as [`boxed_s`], but the memory is
/// claimed from the global memory pool rather than acquired from the stack.
///
/// If the global pool is exhausted, the macro will return the original value.
///
/// [`boxed_s`]: macro.boxed_s.html
///
/// # Examples
///
/// ```ignore
/// use core::any::Any;
/// use core::mem::size_of;
///
/// use heapless::pool;
/// use no_ptr::{boxed, Box};
///
/// pool!(P: [usize; 1]);
///
/// static mut MEMORY: [u8; 256] = [0; 256];
/// assert!(P::grow(unsafe { &mut MEMORY }) >= 1);
///
/// let boxed: Box<dyn Any, P> = boxed!(0_isize).unwrap();
/// assert!(boxed!(0_isize).is_err());
/// ```
#[cfg_attr(rustdoc, doc(cfg(feature = "pool")))]
#[macro_export]
macro_rules! boxed {
    ($val:expr) => {{
        let mut val = $val;
        let ptr = &mut val as *mut _;
        unsafe { $crate::Box::__new(val, ptr) }
    }};
}

/*
    impl Box
*/

#[cfg(feature = "pool")]
impl<T, P> Box<T, P>
where
    P: Pool,
    P::Data: Memory,
{
    /// Acquires memory on the stack and places `x` into it.
    ///
    /// The acquired memory is backed by `N`. If the size or alignment of `T`
    /// is greater than that of `N` the box cannot be constructed. `T` will be
    /// returned in the error variant.
    ///
    /// If `T` is zero-sized then no memory is required; `N` may also be zero
    /// sized in this case.
    ///
    /// # Examples
    ///
    /// Creating a boxed value:
    ///
    /// ```
    /// use no_ptr::BoxS;
    ///
    /// let boxed: BoxS<isize, [usize; 1]> = BoxS::new(0);
    /// ```
    ///
    /// Creating a boxed ZST (zero-sized type):
    ///
    /// ```
    /// use no_ptr::BoxS;
    ///
    /// let boxed: BoxS<(), [usize; 0]> = BoxS::new(());
    /// ```
    ///
    /// Failing to create a boxed value due to size error (this results in a
    /// _compile_ error):
    ///
    /// ```compile_fail
    /// use no_ptr::BoxS;
    ///
    /// let _impossible = BoxS::<isize, [u8; 0]>::new(0);
    /// ```
    ///
    /// Failing to create a boxed value due to alignment error (this results
    /// in a _compile_ error):
    ///
    /// ```compile_fail
    /// use core::mem::size_of;
    /// use no_ptr::BoxS;
    ///
    /// let _impossible = BoxS::<isize, [u8; size_of::<isize>()]>::new(0);
    /// ```
    ///
    /// Coercing to a boxed DST (dynamically-sized type) (requires the
    /// `coerce_unsized` feature):
    ///
    /// ```
    /// use core::any::Any;
    /// use no_ptr::BoxS;
    ///
    /// # #[cfg(feature = "coerce_unsized")]
    /// # {
    /// let boxed: BoxS<dyn Any, [usize; 1]> = BoxS::new(0_isize);
    /// # }
    /// ```
    pub fn new(x: T) -> Result<Self, T> {
        boxed!(x)
    }
}

#[cfg(feature = "pool")]
impl<T, P> Box<T, P>
where
    T: ?Sized,
    P: Pool,
    P::Data: Memory,
{
    #[doc(hidden)]
    pub unsafe fn __new<U>(val: U, ptr: *mut T) -> Result<Self, U> {
        let _ = StaticAssertions::<T, U, P::Data>::new();
        if let Some(boxed) = Box::<T, P>::from_ptrs(&val, ptr) {
            mem::forget(val);
            Ok(boxed)
        } else {
            Err(val)
        }
    }
}

#[cfg(feature = "pool")]
impl<T, P> Box<T, P>
where
    T: ?Sized,
    P: Pool,
    P::Data: Memory,
{
    unsafe fn from_ptrs<U: ?Sized>(ptr_u: *const U, ptr_t: *mut T) -> Option<Self> {
        let mut buf = P::alloc().map(|block| {
            // Ideally we want to be able to use `MaybeUninit::uninit` here.
            // However, there is currently no way to go from an initialized
            // `heapless` box to an uninitialized `heapless` box. The current
            // implementation will drop the data if it is initialized, which
            // it must be for us to dereference in order to access the inner
            // data.
            // SAFETY: Pool::Data implements `Memory`; zeroing is a valid init.
            ManuallyDrop::new(block.init(MaybeUninit::zeroed().assume_init()))
        })?;
        let dst: *mut u8 = &mut **buf as *mut P::Data as *mut _;
        ptr::copy_nonoverlapping(ptr_u as *const u8, dst, mem::size_of_val(&*ptr_u));
        Some(Self {
            buf,
            ptr: write_ptr_addr(ptr_t, 0),
        })
    }

    fn as_ptr(&self) -> *const T {
        unsafe { write_ptr_addr(self.ptr, &**self.buf as *const P::Data as _) }
    }

    fn as_mut_ptr(&mut self) -> *mut T {
        unsafe { write_ptr_addr(self.ptr, &mut **self.buf as *mut P::Data as _) }
    }
}

#[cfg(all(feature = "pool", feature = "coerce_unsized"))]
impl<T, U, P> CoerceUnsized<Box<U, P>> for Box<T, P>
where
    T: ?Sized + Unsize<U>,
    U: ?Sized,
    P: Pool,
    P::Data: Memory,
{
}

#[cfg(feature = "pool")]
impl<T, P> ops::Deref for Box<T, P>
where
    T: ?Sized,
    P: Pool,
    P::Data: Memory,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.as_ptr() }
    }
}

#[cfg(feature = "pool")]
impl<T, P> ops::DerefMut for Box<T, P>
where
    T: ?Sized,
    P: Pool,
    P::Data: Memory,
{
    fn deref_mut(&mut self) -> &mut <Self as ops::Deref>::Target {
        unsafe { &mut *self.as_mut_ptr() }
    }
}

#[cfg(feature = "pool")]
impl<T, P> Drop for Box<T, P>
where
    T: ?Sized,
    P: Pool,
    P::Data: Memory,
{
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(self.as_mut_ptr());
            ManuallyDrop::drop(&mut self.buf);
        }
    }
}

#[cfg(feature = "pool")]
impl<T, P> fmt::Debug for Box<T, P>
where
    T: ?Sized + fmt::Debug,
    P: Pool,
    P::Data: Memory,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as fmt::Debug>::fmt(self, f)
    }
}

#[cfg(feature = "pool")]
impl<T, P> fmt::Display for Box<T, P>
where
    T: ?Sized + fmt::Display,
    P: Pool,
    P::Data: Memory,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as fmt::Display>::fmt(self, f)
    }
}

#[cfg(feature = "pool")]
impl<T, P> fmt::Pointer for Box<T, P>
where
    T: ?Sized,
    P: Pool,
    P::Data: Memory,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_ptr().fmt(f)
    }
}

#[cfg(feature = "pool")]
unsafe impl<T, P> Send for Box<T, P>
where
    T: ?Sized + Send,
    P: Pool,
    P::Data: Memory,
{
}

#[cfg(feature = "pool")]
unsafe impl<T, P> Sync for Box<T, P>
where
    T: ?Sized + Sync,
    P: Pool,
    P::Data: Memory,
{
}
