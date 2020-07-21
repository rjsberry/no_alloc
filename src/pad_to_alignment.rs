pub trait PadToAlignment {
    fn pad_to_alignment(self, align: usize) -> Self;
}

impl PadToAlignment for usize {
    #[inline]
    fn pad_to_alignment(self, align: usize) -> Self {
        debug_assert_ne!(align, 0);
        ((self + align - 1) / align) * align
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn smoke() {
        assert_eq!(1_usize.pad_to_alignment(4), 4);
        assert_eq!(2_usize.pad_to_alignment(4), 4);
        assert_eq!(3_usize.pad_to_alignment(4), 4);
        assert_eq!(4_usize.pad_to_alignment(4), 4);
        assert_eq!(5_usize.pad_to_alignment(4), 8);
    }
}
