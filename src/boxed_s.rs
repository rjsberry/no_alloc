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
        let val = $val;
        let ptr = &val as *const _;
        let boxed = unsafe { $crate::BoxS::__new(&val, ptr) };
        ::core::mem::forget(val);
        boxed
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
    /// The acquired memory is backed by `M`. If the size or alignment of `T`
    /// is greater than that of `M` the box cannot be constructed. This will
    /// reuslt in a compile fail.
    ///
    /// If `T` is zero-sized then no memory is required; `M` may also be zero
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
    pub unsafe fn __new<U>(val: &U, ptr: *const T) -> Self {
        let _ = StaticAssertions::<T, U, M>::new();
        let extra = crate::__retrieve_extra_addr(ptr);
        let boxed = BoxS::<T, M>::from_ptr(val, extra);
        boxed
    }
}

impl<T, M> BoxS<T, M>
where
    T: ?Sized,
    M: Memory,
{
    unsafe fn from_ptr<U>(ptr_u: &U, extra: Option<usize>) -> Self
    where
        U: ?Sized,
    {
        let mut buf: MaybeUninit<M> = MaybeUninit::uninit();
        let dst: *mut u8 = buf.as_mut_ptr() as *mut _;
        ptr::copy_nonoverlapping(
            ptr_u as *const _ as *const u8,
            dst,
            mem::size_of_val::<U>(&ptr_u),
        );

        let mut ptr = MaybeUninit::uninit();
        let ptr_ptr: *mut usize = ptr.as_mut_ptr() as *mut _;
        if let Some(addr) = extra {
            ptr_ptr.add(1).write(addr);
        }
        ptr_ptr.write(0);

        Self {
            buf: ManuallyDrop::new(buf.assume_init()),
            ptr: ptr.assume_init(),
        }
    }

    fn as_ptr(&self) -> *const T {
        unsafe { write_ptr_addr(self.ptr, &*self.buf as *const M as _) }
    }

    fn as_mut_ptr(&mut self) -> *mut T {
        unsafe { write_ptr_addr(self.ptr, &mut *self.buf as *mut M as _) }
    }

    unsafe fn downcast_unchecked<U: Any>(mut self) -> BoxS<U, M> {
        let buf = mem::replace(&mut self.buf, MaybeUninit::uninit().assume_init());
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

/*
    Unit tests
*/

#[cfg(test)]
mod tests {
    use super::*;

    use core::any::Any;
    use core::sync::atomic::{AtomicBool, Ordering};

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
        mem::drop(boxed);
        assert!(dropped.load(Ordering::Relaxed));
    }

    #[test]
    fn any() {
        let boxed: BoxS<dyn Any, [usize; 1]> = boxed_s!(0_usize);
        assert_eq!(*boxed.downcast::<usize>().ok().unwrap(), 0);
        let boxed: BoxS<dyn Any + Send, [usize; 1]> = boxed_s!(0_usize);
        assert_eq!(*boxed.downcast::<usize>().ok().unwrap(), 0);
    }

    #[test]
    fn slice() {
        let boxed: BoxS<[u8], [usize; 1]> = boxed_s!([0_u8; 4]);
        assert_eq!(&*boxed, &[0_u8; 4][..]);
    }
}
