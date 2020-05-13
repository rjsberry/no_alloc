use core::mem;

/// Defines the types of backing storage for `no_ptr` smart pointers.
///
/// Backing memory will need to be carefully selected so that it has sufficient
/// size and the correct alignment for the type you need to store.
///
/// Note that memory that fails to meet these demands will trigger a compile
/// time failure.
pub unsafe trait Memory: Sized + 'static {}

pub unsafe fn retrieve_extra_addr<T: ?Sized>(ptr: *const T) -> Option<usize> {
    if mem::size_of::<*const T>() == mem::size_of::<usize>() {
        None
    } else {
        #[repr(C)]
        #[derive(Debug, Copy, Clone)]
        struct Repr {
            data: usize,
            extra: usize,
        }
        let repr: &Repr = mem::transmute::<&*const T, _>(&ptr);
        Some(repr.extra)
    }
}

pub(crate) unsafe fn write_ptr_addr<T: ?Sized>(mut ptr: *mut T, addr: usize) -> *mut T {
    let ptr_ptr = &mut ptr as *mut _ as *mut usize;
    ptr_ptr.write(addr);
    ptr
}

#[cfg(feature = "const_generics")]
unsafe impl<const N: usize> Memory for [u8; N] {}
#[cfg(feature = "const_generics")]
unsafe impl<const N: usize> Memory for [u16; N] {}
#[cfg(feature = "const_generics")]
unsafe impl<const N: usize> Memory for [u32; N] {}
#[cfg(feature = "const_generics")]
unsafe impl<const N: usize> Memory for [u64; N] {}
#[cfg(feature = "const_generics")]
unsafe impl<const N: usize> Memory for [u128; N] {}
#[cfg(feature = "const_generics")]
unsafe impl<const N: usize> Memory for [usize; N] {}

#[cfg(not(feature = "const_generics"))]
macro_rules! impl_array {
    ($item:ty, $($n:literal),* $(,)?) => {
        $(unsafe impl Memory for [$item; $n] {})*
    }
}

#[cfg(not(feature = "const_generics"))]
impl_array!(u8, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192);
#[cfg(not(feature = "const_generics"))]
impl_array!(u16, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192);
#[cfg(not(feature = "const_generics"))]
impl_array!(u32, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192);
#[cfg(not(feature = "const_generics"))]
impl_array!(u64, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192);
#[cfg(not(feature = "const_generics"))]
impl_array!(u128, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192);
#[cfg(not(feature = "const_generics"))]
impl_array!(usize, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192);
