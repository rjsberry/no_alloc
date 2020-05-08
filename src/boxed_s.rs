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

/// A box that exists entirely on the stack.
pub struct BoxS<T, M>
where
    T: ?Sized,
    M: Memory,
{
    buf: ManuallyDrop<M>,
    ptr: *mut T,
}

/// Box a value on the stack.
///
/// This macro exists as DST coercion currently requires a nightly compiler.
/// It will be deprecated once this hits stable.
///
/// For more info, see [#27732].
///
/// Note that just like [`BoxS::new`] the space and alignment demands for the
/// box are evaluated at compile time. Attempting to use this macro to construct
/// a boxed value with invalid backing storage will result in a compilation
/// failure.
///
/// [#27732]: https://github.com/rust-lang/rust/issues/27732
/// [`BoxS::new`]: struct.BoxS.html#method.new
///
/// # Examples
///
/// Boxing a value on the stack, coercing to a DST:
///
/// ```
/// use core::any::Any;
/// use no_ptr::{boxed_s, BoxS};
///
/// let boxed: BoxS<dyn Any, [usize; 1]> = boxed_s!(0_isize);
/// ```
#[macro_export]
macro_rules! boxed_s {
    ($val:expr) => {{
        let mut val = $val;
        let ptr = &mut val as *mut _;
        unsafe { $crate::BoxS::__new(val, ptr) }
    }};
}

/*
    impl BoxS
*/

#[cfg(feature = "coerce_unsized")]
impl<T, U, M> CoerceUnsized<BoxS<U, M>> for BoxS<T, M>
where
    T: ?Sized + Unsize<U>,
    U: ?Sized,
    M: Memory,
{
}

impl<T, M> ops::Deref for BoxS<T, M>
where
    T: ?Sized,
    M: Memory,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.as_ptr() }
    }
}

impl<T, M> ops::DerefMut for BoxS<T, M>
where
    T: ?Sized,
    M: Memory,
{
    fn deref_mut(&mut self) -> &mut <Self as ops::Deref>::Target {
        unsafe { &mut *self.as_mut_ptr() }
    }
}

impl<T, M> Drop for BoxS<T, M>
where
    T: ?Sized,
    M: Memory,
{
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(self.as_mut_ptr());
        }
    }
}

impl<T, M> fmt::Debug for BoxS<T, M>
where
    T: ?Sized + fmt::Debug,
    M: Memory,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as fmt::Debug>::fmt(self, f)
    }
}

impl<T, M> fmt::Display for BoxS<T, M>
where
    T: ?Sized + fmt::Display,
    M: Memory,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as fmt::Display>::fmt(self, f)
    }
}

impl<T, M> fmt::Pointer for BoxS<T, M>
where
    T: ?Sized,
    M: Memory,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_ptr().fmt(f)
    }
}

impl<T, M> BoxS<T, M>
where
    M: Memory,
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
    pub fn new(x: T) -> Self {
        boxed_s!(x)
    }
}

impl<M> BoxS<dyn Any + 'static, M>
where
    M: Memory,
{
    /// Attempts to downcast the box to a concrete type.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::any::Any;
    /// use core::fmt;
    ///
    /// use no_ptr::{BoxS, Memory};
    ///
    /// fn write_if_str<W: fmt::Write, M: Memory>(
    ///     mut wtr: W,
    ///     boxed: BoxS<dyn Any + 'static, M>
    /// ) -> fmt::Result {
    ///     if let Ok(s) = boxed.downcast::<&str>() {
    ///         wtr.write_str(&s)?;
    ///     }
    ///     Ok(())
    /// }
    /// ```
    pub fn downcast<T>(self) -> Result<BoxS<T, M>, Self>
    where
        T: Any,
    {
        if self.is::<T>() {
            Ok(unsafe { self.downcast_unchecked() })
        } else {
            Err(self)
        }
    }
}

impl<M> BoxS<dyn Any + Send + 'static, M>
where
    M: Memory,
{
    /// Attempts to downcast the box to a concrete type.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::any::Any;
    /// use core::fmt;
    ///
    /// use no_ptr::{BoxS, Memory};
    ///
    /// fn write_if_str<W: fmt::Write, M: Memory>(
    ///     mut wtr: W,
    ///     boxed: BoxS<dyn Any + Send + 'static, M>
    /// ) -> fmt::Result {
    ///     if let Ok(s) = boxed.downcast::<&str>() {
    ///         wtr.write_str(&s)?;
    ///     }
    ///     Ok(())
    /// }
    /// ```
    pub fn downcast<T>(self) -> Result<BoxS<T, M>, Self>
    where
        T: Any,
    {
        if self.is::<T>() {
            Ok(unsafe { self.downcast_unchecked() })
        } else {
            Err(self)
        }
    }
}

impl<T, M> BoxS<T, M>
where
    T: ?Sized,
    M: Memory,
{
    #[doc(hidden)]
    pub unsafe fn __new<U>(val: U, ptr: *mut T) -> Self {
        let _ = StaticAssertions::<T, U, M>::new();
        let boxed = BoxS::<T, M>::from_ptrs(&val, ptr);
        mem::forget(val);
        boxed
    }
}

impl<T, M> BoxS<T, M>
where
    T: ?Sized,
    M: Memory,
{
    unsafe fn from_ptrs<U>(ptr_u: *const U, ptr_t: *mut T) -> Self
    where
        U: ?Sized,
    {
        let mut buf = ManuallyDrop::new(MaybeUninit::uninit().assume_init());
        let dst: *mut u8 = &mut *buf as *mut M as *mut _;
        ptr::copy_nonoverlapping(ptr_u as *const u8, dst, mem::size_of_val(&*ptr_u));
        Self {
            buf,
            ptr: write_ptr_addr(ptr_t, 0),
        }
    }

    fn as_ptr(&self) -> *const T {
        unsafe { write_ptr_addr(self.ptr, &*self.buf as *const M as _) }
    }

    fn as_mut_ptr(&mut self) -> *mut T {
        unsafe { write_ptr_addr(self.ptr, &mut *self.buf as *mut M as _) }
    }

    unsafe fn downcast_unchecked<U: Any>(self) -> BoxS<U, M> {
        let mut buf = ManuallyDrop::new(MaybeUninit::uninit().assume_init());
        let src: *const u8 = &*self.buf as *const M as *const _;
        let dst: *mut u8 = &mut *buf as *mut M as *mut _;
        ptr::copy_nonoverlapping(src, dst, mem::size_of::<U>());
        let ptr = self.ptr as *mut _;
        mem::forget(self);
        BoxS { buf, ptr }
    }
}

unsafe impl<T, M> Send for BoxS<T, M>
where
    T: ?Sized + Send,
    M: Memory,
{
}

unsafe impl<T, M> Sync for BoxS<T, M>
where
    T: ?Sized + Sync,
    M: Memory,
{
}
