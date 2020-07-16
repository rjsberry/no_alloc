use core::mem::size_of;

use heapless::{pool, pool::singleton::Pool};
use no_alloc::{boxed, Box};

pool!(P: [usize; 1]);
static mut MEMORY: [u8; 2 * size_of::<usize>()] = [0; 2 * size_of::<usize>()];

fn main() {
    assert!(unsafe { P::grow(&mut MEMORY) } >= 1);
    let mut boxed: Box<isize, P> = boxed!(0_isize).unwrap();
    assert_eq!(*boxed, 0);
    *boxed += 1;
    assert_eq!(*boxed, 1);
}
