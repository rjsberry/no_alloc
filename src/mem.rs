pub unsafe trait Memory: Sized + 'static {}

pub(crate) unsafe fn write_ptr_addr<T: ?Sized>(mut ptr: *mut T, addr: usize) -> *mut T {
    let ptr_ptr = &mut ptr as *mut _ as *mut usize;
    ptr_ptr.write(addr);
    ptr
}

macro_rules! impl_array {
    ($item:ty, $($n:literal),* $(,)?) => {
        $(unsafe impl Memory for [$item; $n] {})*
    }
}

impl_array!(u8, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192);
impl_array!(u16, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192);
impl_array!(u32, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192);
impl_array!(u64, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192);
impl_array!(u128, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192);
impl_array!(usize, 0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192);
