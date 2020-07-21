/// Safely obtains a single mutable reference to some initialized static memory.
///
/// # Examples
///
/// Initializing a static buffer:
///
/// ```
/// use no_alloc::static_buf;
///
/// let buf: &'static mut [u8] = static_buf![0; 128];
/// ```
///
/// Initializing a static buffer in a custom link section:
///
/// ```no_run
/// use no_alloc::static_buf;
///
/// let buf: &'static mut [u8] = static_buf! {
///     #[link_section = ".custom_section"]
///     [0; 128]
/// };
/// ```
#[macro_export]
macro_rules! static_buf {
    ($init:literal; $len:expr) => { static_buf!([$init; $len]) };
    ($(#[$m:meta])* [$init:literal; $len:expr]) => {{
        $(#[$m])*
        #[allow(unsafe_code)]
        static _DATA: $crate::AssertUnsyncSafe<
            core::cell::UnsafeCell<
                [u8; $len]
            >
        > = unsafe {
                // SAFETY: We are controlling precise usage of the UnsafeCell in
                //   a static location - there will be no shared immutable
                //   references to the wrapped value.
                $crate::AssertUnsyncSafe::new(core::cell::UnsafeCell::new(
                    [$init; $len],
                ))
            };
        #[allow(unsafe_code)]
        unsafe {
            // SAFETY: We've just initialized the UnsafeCell and there is no
            //   possibility that any other references can be created to the
            //   wrapped value.
            &mut *_DATA.get()
        }
    }};
}

#[cfg(test)]
mod tests {
    #[test]
    fn smoke() {
        let data = static_buf! {
            #[cfg(test)]
            [0; 1]
        };
        assert_eq!(data, &[0][..]);
    }
}
