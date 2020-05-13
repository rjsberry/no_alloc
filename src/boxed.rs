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
/// ```
/// use core::any::Any;
/// use core::mem::size_of;
///
/// use heapless::{pool, pool::singleton::Pool};
/// use no_ptr::{boxed, Box};
///
/// pool!(P: [usize; 1]);
///
/// static mut MEMORY: [u8; 2 * size_of::<usize>()] = [0; 2 * size_of::<usize>()];
/// assert!(P::grow(unsafe { &mut MEMORY }) == 1);
///
/// let boxed: Box<dyn Any, P> = boxed!(0_isize).unwrap();
/// ```
#[cfg_attr(rustdoc, doc(cfg(feature = "pool")))]
#[macro_export]
macro_rules! boxed {
    ($val:expr) => {{
        let val = $val;
        let ptr = &val as *const _ as *const _;
        if let Some(boxed) = unsafe { $crate::Box::__new(&val, ptr) } {
            ::core::mem::forget(val);
            Ok(boxed)
        } else {
            Err(val)
        }
    }};
}

/*
    impl Box
*/

impl<T, P> Box<T, P>
where
    P: Pool,
    P::Data: Memory,
{
    /// Attempts to acquire a memory block from the global pool, and places `x`
    /// into it.
    ///
    /// If the pool is exhausted then `x` will be returned as an error.
    ///
    /// If `T` is zero-sized then no memory is required; `P::Data` may also be
    /// zero sized in this case.
    ///
    /// # Examples
    ///
    /// Creating a boxed value:
    ///
    /// ```
    /// use core::mem::size_of;
    ///
    /// use heapless::{pool, pool::singleton::Pool};
    /// use no_ptr::Box;
    ///
    /// pool!(P: [usize; 1]);
    /// static mut MEMORY: [u8; 2 * size_of::<usize>()] = [0; 2 * size_of::<usize>()];
    /// assert!(P::grow(unsafe { &mut MEMORY }) >= 1);
    ///
    /// let boxed: Box<isize, P> = Box::new(0).unwrap();
    /// ```
    ///
    /// Creating a boxed ZST (zero-sized type):
    ///
    /// ```
    /// use heapless::{pool, pool::singleton::Pool};
    /// use no_ptr::Box;
    ///
    /// pool!(P: [usize; 0]);
    ///
    /// // We don't need to grow P at all, our data is zero sized
    /// let boxed: Box<(), P> = Box::new(()).unwrap();
    /// ```
    ///
    /// Failing to create a boxed value due to size error (this results in a
    /// _compile_ error):
    ///
    /// ```compile_fail
    /// use heapless::{pool, pool::singleton::Pool};
    /// use no_ptr::Box;
    ///
    /// pool!(P: [usize; 0]);
    ///
    /// let _impossible = Box::<isize, P>::new(0).unwrap();
    /// ```
    ///
    /// Failing to create a boxed value due to alignment error (this results
    /// in a _compile_ error):
    ///
    /// ```compile_fail
    /// use core::mem::size_of;
    ///
    /// use heapless::{pool, pool::singleton::Pool};
    /// use no_ptr::Box;
    ///
    /// pool!(P: [u8; size_of::<isize>()]);
    ///
    /// let _impossible = Box::<isize, P>::new(0).unwrap();
    /// ```
    ///
    /// Coercing to a boxed DST (dynamically-sized type) (requires the
    /// `coerce_unsized` feature):
    ///
    /// ```
    /// use core::any::Any;
    /// use core::mem::size_of;
    ///
    /// use heapless::{pool, pool::singleton::Pool};
    /// use no_ptr::Box;
    ///
    /// pool!(P: [usize; 1]);
    /// static mut MEMORY: [u8; 2 * size_of::<usize>()] = [0; 2 * size_of::<usize>()];
    ///
    /// # #[cfg(feature = "coerce_unsized")]
    /// # {
    /// let boxed: Box<dyn Any, P> = Box::new(0_isize).unwrap();
    /// # }
    /// ```
    pub fn new(x: T) -> Result<Self, T> {
        boxed!(x)
    }
}

impl<T, P> Box<T, P>
where
    T: ?Sized,
    P: Pool,
    P::Data: Memory,
{
    #[doc(hidden)]
    pub unsafe fn __new<U>(val: &U, ptr: *const T) -> Option<Self> {
        let _ = StaticAssertions::<T, U, P::Data>::new();
        let extra = crate::__retrieve_extra_addr(ptr);
        Box::<T, P>::from_ptr(val, extra)
    }
}

impl<T, P> Box<T, P>
where
    T: ?Sized,
    P: Pool,
    P::Data: Memory,
{
    unsafe fn from_ptr<U>(ptr_u: &U, extra: Option<usize>) -> Option<Self>
    where
        U: ?Sized,
    {
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

        Some(Self {
            buf,
            ptr: ptr.assume_init(),
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

unsafe impl<T, P> Send for Box<T, P>
where
    T: ?Sized + Send,
    P: Pool,
    P::Data: Memory,
{
}

unsafe impl<T, P> Sync for Box<T, P>
where
    T: ?Sized + Sync,
    P: Pool,
    P::Data: Memory,
{
}

/*
    Unit tests
*/

#[cfg(test)]
mod tests {
    use super::*;

    use core::sync::atomic::{AtomicBool, Ordering};

    use heapless::{pool, pool::singleton::Pool};

    #[test]
    fn smoke() {
        pool!(P: [usize; 1]);
        static mut DATA: [u8; 32] = [0; 32];
        assert!(P::grow(unsafe { &mut DATA }) >= 1);
        let mut boxed = Box::<usize, P>::new(0).unwrap();
        assert_eq!(*boxed, 0);
        *boxed = 1;
        assert_eq!(*boxed, 1);
    }

    #[test]
    fn boxed_macro() {
        pool!(P: [usize; 1]);
        static mut DATA: [u8; 32] = [0; 32];
        assert!(P::grow(unsafe { &mut DATA }) >= 1);
        let _boxed: Box<dyn Any, P> = boxed!(0_usize).unwrap();
    }

    #[cfg(feature = "coerce_unsized")]
    #[test]
    fn coerce_unsized() {
        pool!(P: [usize; 1]);
        static mut DATA: [u8; 32] = [0; 32];
        assert!(P::grow(unsafe { &mut DATA }) >= 1);
        let _boxed: Box<dyn Any, P> = Box::new(0_usize).unwrap();
    }

    #[test]
    fn zst() {
        pool!(P: [usize; 0]);
        let mut boxed = Box::<(), P>::new(()).unwrap();
        assert_eq!(*boxed, ());
        *boxed = ();
    }

    #[test]
    fn drop() {
        pool!(P: [usize; 1]);
        static mut DATA: [u8; 2 * mem::size_of::<usize>()] = [0; 2 * mem::size_of::<usize>()];
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
        mem::drop(boxed);
        assert!(dropped.load(Ordering::Relaxed));
    }
}
