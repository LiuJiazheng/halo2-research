pub const MEM_RANGE_BITS: usize = 4;
pub const VALUE_RANGE_BITS: usize = 4;

// Define a macro that takes a buffer and a tuple of variable names and destructures the buffer into those variables.
#[macro_export]
macro_rules! destructure_buffer {
    ($buffer_name:expr, ($($var_name:ident),*)) => {
        // We use the 'if let' pattern to destructure the buffer.
        if let [$($var_name),*] = $buffer_name[..] {
            ($($var_name),*)
        } else {
            // If the pattern doesn't match, we panic.
            panic!("buffer does not match expected pattern")
        }
    };
}
