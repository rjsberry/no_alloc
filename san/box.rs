use core::mem;

use no_alloc::{
    boxed, global_allocator, static_buf, AssertUnsyncSafe, Box,
    GlobalAllocator, UnsyncLinearAllocator,
};

global_allocator! {
    type A = AssertUnsyncSafe<UnsyncLinearAllocator>;
    const unsafe fn init() -> A {
        AssertUnsyncSafe::new(UnsyncLinearAllocator::uninit())
    }
}

fn main() {
    A::static_ref().init(static_buf![0; 2 * mem::size_of::<i32>() - 1]);
    let mut boxed: Box<i32, A> = boxed!(0_i32).unwrap();
    assert_eq!(*boxed, 0);
    *boxed += 1;
    assert_eq!(*boxed, 1);
}
