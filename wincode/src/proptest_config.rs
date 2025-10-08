use proptest::test_runner::Config;

/// Configuration for proptest tests.
///
/// Disable FS I/O in Miri.
pub(crate) fn proptest_cfg() -> Config {
    #[cfg(miri)]
    {
        Config {
            failure_persistence: None,
            // Avoid excruciatingly long test times in Miri.
            cases: 5,
            ..Config::default()
        }
    }
    #[cfg(not(miri))]
    {
        Config::default()
    }
}
