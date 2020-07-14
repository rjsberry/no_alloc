use core::mem;

#[repr(C)]
#[derive(Copy, Clone)]
pub(crate) struct FatPointer {
    pub(crate) data: *mut (),
    pub(crate) meta: usize,
}

impl FatPointer {
    pub(crate) fn from_raw<T: ?Sized>(raw: *mut T) -> Option<Self> {
        if mem::size_of::<*mut T>() == mem::size_of::<Self>() {
            unsafe { Some(*mem::transmute::<&*mut T, &Self>(&raw)) }
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use core::any::Any;

    #[test]
    fn smoke() {
        assert!(FatPointer::from_raw::<i32>(&mut 0).is_none());
        assert!(FatPointer::from_raw::<[i32]>(&mut [0][..]).is_some());
        assert!(FatPointer::from_raw::<dyn Any>(&mut 0).is_some());
    }
}
