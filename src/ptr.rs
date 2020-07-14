pub(crate) fn write_addr<T: ?Sized>(mut ptr: *mut T, addr: usize) -> *mut T {
    let ptr_ptr = &mut ptr as *mut _ as *mut usize;
    unsafe { ptr_ptr.write(addr) };
    ptr
}
