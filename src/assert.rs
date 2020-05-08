use core::marker::PhantomData;
use core::mem;

pub(crate) struct StaticAssertions<T: ?Sized, U, N>(PhantomData<(*mut T, U, N)>);

/*
    impl StaticAssertions
*/

impl<T: ?Sized, U, N> StaticAssertions<T, U, N> {
    const SIZE_CHECK: usize = 0 - !(
        // Size check fail!
        // The following case does not hold:
        mem::size_of::<U>() <= mem::size_of::<N>()
        // The box cannot be constructed.
    ) as usize;

    const ALIGN_CHECK: usize = 0 - !(
        // Align check fail!
        // The following case does not hold:
        mem::align_of::<U>() <= mem::align_of::<N>()
        // The box cannot be constructed.
    ) as usize;

    pub(crate) fn new() -> Self {
        let _ = Self::SIZE_CHECK;
        let _ = Self::ALIGN_CHECK;
        Self(PhantomData)
    }
}
