use core::fmt;

/// The error returned when an allocation fails.
pub struct CapacityError {
    _priv: (),
}

impl CapacityError {
    pub(super) fn new() -> Self { Self { _priv: () } }
}

impl fmt::Debug for CapacityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CapacityError").finish()
    }
}

impl fmt::Display for CapacityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("capacity error: allocator is out of usable memory")
    }
}
