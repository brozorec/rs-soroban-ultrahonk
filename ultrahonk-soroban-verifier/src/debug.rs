/// trace! macro is a lightweight debug print macro that only outputs when the `trace` feature is enabled.
#[macro_export]
macro_rules! trace {
    ($($arg:tt)*) => {
        #[cfg(all(feature = "trace", feature = "std"))]
        {
            println!($($arg)*);
        }
    };
}
