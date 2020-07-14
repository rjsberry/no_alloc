use no_ptr::{boxed_s, BoxS};

fn main() {
    let mut boxed: BoxS<isize, [usize; 1]> = boxed_s!(0_isize);
    assert_eq!(*boxed, 0);
    *boxed += 1;
    assert_eq!(*boxed, 1);
}
