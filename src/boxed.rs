use super::{GlobalAllocator, Layout};

use crate::ptr::write_addr;
use crate::raw::FatPointer;

use core::any::Any;
use core::fmt;
use core::marker::PhantomData;
use core::mem::{self, MaybeUninit};
use core::ops;
use core::ptr::{self, NonNull};

#[cfg(feature = "coerce_unsized")]
use core::marker::Unsize;
#[cfg(feature = "coerce_unsized")]
use core::ops::CoerceUnsized;

/// A box belonging to the global memory pool.
#[cfg_attr(rustdoc, doc(cfg(feature = "pool")))]
pub struct Box<T: ?Sized, A: GlobalAllocator> {
    buf:     NonNull<u8>,
    ptr:     *mut T,
    _marker: PhantomData<A>,
}

/// Box a value global memory pool.
///
/// This macro behaves exactly the same as [`boxed_s`], but the memory is
/// claimed from the global memory pool rather than acquired from the stack.
///
/// If the global pool is exhausted, the macro will return the original value.
///
/// [`boxed_s`]: macro.boxed_s.html
#[cfg_attr(rustdoc, doc(cfg(feature = "pool")))]
#[macro_export]
macro_rules! boxed {
    ($val:expr) => {{
        let mut val = $val;
        let ptr = &mut val as *mut _;
        if let Some(boxed) = unsafe { $crate::Box::__new(&mut val, ptr) } {
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

impl<T, A: GlobalAllocator> Box<T, A> {
    /// Attempts to acquire a memory block from the global allocator, and places
    /// `x` into it.
    ///
    /// If the allocator is exhausted then `x` will be returned as an error.
    ///
    /// If `T` is zero-sized no memory will be requested from the allocator. In
    /// this case the function will never fail.
    pub fn new(x: T) -> Result<Self, T> { boxed!(x) }
}

impl<A: GlobalAllocator> Box<dyn Any + 'static, A> {
    /// Attempts to downcast the box to a concrete type.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::any::Any;
    /// use core::fmt;
    ///
    /// use no_alloc::{Box, GlobalAllocator};
    ///
    /// fn write_if_str<W: fmt::Write, A: GlobalAllocator>(
    ///     mut wtr: W,
    ///     boxed: Box<dyn Any + 'static, A>
    /// ) -> fmt::Result {
    ///     if let Ok(s) = boxed.downcast::<&str>() {
    ///         wtr.write_str(&s)?;
    ///     }
    ///     Ok(())
    /// }
    /// ```
    pub fn downcast<T>(self) -> Result<Box<T, A>, Self>
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

impl<A: GlobalAllocator> Box<dyn Any + Send + 'static, A> {
    /// Attempts to downcast the box to a concrete type.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::any::Any;
    /// use core::fmt;
    ///
    /// use no_alloc::{Box, GlobalAllocator};
    ///
    /// fn write_if_str<W: fmt::Write, A: GlobalAllocator>(
    ///     mut wtr: W,
    ///     boxed: Box<dyn Any + Send + 'static, A>
    /// ) -> fmt::Result {
    ///     if let Ok(s) = boxed.downcast::<&str>() {
    ///         wtr.write_str(&s)?;
    ///     }
    ///     Ok(())
    /// }
    /// ```
    pub fn downcast<T>(self) -> Result<Box<T, A>, Self>
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

impl<T: ?Sized, A: GlobalAllocator> Box<T, A> {
    #[doc(hidden)]
    pub unsafe fn __new<U>(val: &mut U, ptr: *mut T) -> Option<Self> {
        Box::<T, A>::from_ptr(
            val,
            FatPointer::from_raw(ptr).map(|fat| fat.meta),
        )
    }
}

impl<T: ?Sized, A: GlobalAllocator> Box<T, A> {
    unsafe fn from_ptr<U>(ptr_u: &mut U, meta: Option<usize>) -> Option<Self> {
        let mut buf = A::alloc(Layout::new::<U>()).ok()?;
        ptr::copy_nonoverlapping(
            ptr_u as *const _ as *const u8,
            buf.as_mut() as *mut _,
            mem::size_of_val::<U>(&ptr_u),
        );

        let mut ptr = MaybeUninit::zeroed();
        let ptr_ptr: *mut usize = ptr.as_mut_ptr() as *mut _;
        if let Some(meta) = meta {
            ptr_ptr.add(1).write(meta);
        }

        Some(Self { buf, ptr: ptr.assume_init(), _marker: PhantomData })
    }

    fn as_ptr(&self) -> *const T {
        write_addr(self.ptr, self.buf.as_ptr() as _)
    }

    fn as_mut_ptr(&mut self) -> *mut T {
        write_addr(self.ptr, self.buf.as_ptr() as _)
    }

    unsafe fn downcast_unchecked<U: Any>(self) -> Box<U, A> {
        let Self { buf, ptr, .. } = self;
        mem::forget(self);
        Box { buf, ptr: ptr as *mut _, _marker: PhantomData }
    }
}

#[cfg(all(feature = "pool", feature = "coerce_unsized"))]
impl<T: ?Sized + Unsize<U>, U: ?Sized, A: GlobalAllocator>
    CoerceUnsized<Box<U, P>> for Box<T, A>
{
}

impl<T: ?Sized, A: GlobalAllocator> ops::Deref for Box<T, A> {
    type Target = T;

    fn deref(&self) -> &Self::Target { unsafe { &*self.as_ptr() } }
}

impl<T: ?Sized, A: GlobalAllocator> ops::DerefMut for Box<T, A> {
    fn deref_mut(&mut self) -> &mut <Self as ops::Deref>::Target {
        unsafe { &mut *self.as_mut_ptr() }
    }
}

impl<T: ?Sized, A: GlobalAllocator> Drop for Box<T, A> {
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(self.as_mut_ptr());
            A::dealloc(self.buf);
        }
    }
}

impl<T: ?Sized + fmt::Debug, A: GlobalAllocator> fmt::Debug for Box<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as fmt::Debug>::fmt(self, f)
    }
}

impl<T: ?Sized + fmt::Display, A: GlobalAllocator> fmt::Display for Box<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as fmt::Display>::fmt(self, f)
    }
}

impl<T: ?Sized, A: GlobalAllocator> fmt::Pointer for Box<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_ptr().fmt(f)
    }
}

unsafe impl<T: ?Sized + Send, A: GlobalAllocator> Send for Box<T, A> {}

unsafe impl<T: ?Sized + Sync, A: GlobalAllocator> Sync for Box<T, A> {}

/*
    Unit tests
*/

#[cfg(test)]
mod tests {
    use super::{
        super::{
            global_allocator, static_buf, AssertUnsyncSafe,
            UnsyncLinearAllocator,
        },
        *,
    };

    #[test]
    fn smoke() {
        global_allocator! {
            type A = AssertUnsyncSafe<UnsyncLinearAllocator>;
            const unsafe fn init() -> A {
                AssertUnsyncSafe::new(UnsyncLinearAllocator::uninit())
            }
        }
        A::static_ref().init(static_buf![0; 2 * mem::size_of::<i32>() - 1]);
        let mut boxed = Box::<i32, A>::new(0).unwrap();
        assert_eq!(*boxed, 0);
        *boxed = 1;
        assert_eq!(*boxed, 1);
    }

    #[test]
    fn boxed_macro() {
        global_allocator! {
            type A = AssertUnsyncSafe<UnsyncLinearAllocator>;
            const unsafe fn init() -> A {
                AssertUnsyncSafe::new(UnsyncLinearAllocator::uninit())
            }
        }
        A::static_ref().init(static_buf![0; 2 * mem::size_of::<i32>() - 1]);
        let _boxed: Box<dyn Any, A> = boxed!(0_i32).unwrap();
    }

    #[cfg(feature = "coerce_unsized")]
    #[test]
    fn coerce_unsized() {
        global_allocator! {
            type A = AssertUnsyncSafe<UnsyncLinearAllocator>;
            const unsafe fn init() -> A {
                AssertUnsyncSafe::new(UnsyncLinearAllocator::uninit())
            }
        }
        A::static_ref().init(static_buf![0; 2 * mem::size_of::<i32>() - 1]);
        let _boxed: Box<dyn Any, A> = Box::new(0_i32).unwrap();
    }

    /* FIXME
    #[test]
    fn zst() {
        pool!(P: [usize; 0]);
        let mut boxed = Box::<(), P>::new(()).unwrap();
        assert_eq!(*boxed, ());
        *boxed = ();
    }
    */

    #[test]
    fn drop() {
        global_allocator! {
            type A = AssertUnsyncSafe<UnsyncLinearAllocator>;
            const unsafe fn init() -> A {
                AssertUnsyncSafe::new(UnsyncLinearAllocator::uninit())
            }
        }

        #[derive(Debug)]
        struct Foo<'a>(&'a mut bool);
        impl Drop for Foo<'_> {
            fn drop(&mut self) { *self.0 = true; }
        }

        A::static_ref().init(static_buf![0; 2 * mem::size_of::<Foo<'_>>() - 1]);
        let mut dropped = false;
        let foo = Foo(&mut dropped);
        let boxed = Box::<_, A>::new(foo).unwrap();
        mem::drop(boxed);
        assert!(dropped);
    }

    #[test]
    fn any() {
        global_allocator! {
            type A = AssertUnsyncSafe<UnsyncLinearAllocator>;
            const unsafe fn init() -> A {
                AssertUnsyncSafe::new(UnsyncLinearAllocator::uninit())
            }
        }
        A::static_ref().init(static_buf![0; 2 * mem::size_of::<i32>() - 1]);
        let boxed: Box<dyn Any, A> = boxed!(0_i32).unwrap();
        assert_eq!(*boxed.downcast::<i32>().ok().unwrap(), 0);
        let boxed: Box<dyn Any + Send, A> = boxed!(0_i32).unwrap();
        assert_eq!(*boxed.downcast::<i32>().ok().unwrap(), 0);
    }

    #[test]
    fn slice() {
        global_allocator! {
            type A = AssertUnsyncSafe<UnsyncLinearAllocator>;
            const unsafe fn init() -> A {
                AssertUnsyncSafe::new(UnsyncLinearAllocator::uninit())
            }
        }
        A::static_ref().init(static_buf![0; 5 * mem::size_of::<i32>() - 1]);
        let boxed: Box<[i32], A> = boxed!([0_i32; 4]).unwrap();
        assert_eq!(&*boxed, &[0_i32; 4][..]);
    }
}
