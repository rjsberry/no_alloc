/// Defines the types of backing storage for `no_alloc` smart pointers.
///
/// Backing memory will need to be carefully selected so that it has sufficient
/// size and the correct alignment for the type you need to store.
///
/// Note that memory that fails to meet these demands will trigger a compile
/// time failure.
pub unsafe trait Memory: Sized + 'static {}

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
macro_rules! impl_memory {
    ($item:ty, $($n:literal),* $(,)?) => {
        $(unsafe impl Memory for [$item; $n] {})*
    }
}

#[cfg(not(feature = "const_generics"))]
impl_memory!(
    u8, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192
);
#[cfg(not(feature = "const_generics"))]
impl_memory!(
    u16, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192
);
#[cfg(not(feature = "const_generics"))]
impl_memory!(
    u32, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192
);
#[cfg(not(feature = "const_generics"))]
impl_memory!(
    u64, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192
);
#[cfg(not(feature = "const_generics"))]
impl_memory!(
    u128, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192
);
#[cfg(not(feature = "const_generics"))]
impl_memory!(
    usize, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192
);
