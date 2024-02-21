//! A powerful property-based testing library with a tiny API and a small implementation.
//!
//! ```rust
//! use arbtest::arbtest;
//!
//! #[test]
//! fn all_numbers_are_even() {
//!     arbtest(|u| {
//!         let number: u32 = u.arbitrary()?;
//!         assert!(number % 2 == 0);
//!         Ok(())
//!     });
//! }
//! ```
//!
//! Features:
//!
//! - single-function public API,
//! - no macros,
//! - automatic minimization,
//! - time budgeting,
//! - fuzzer-compatible tests.
//!
//! The entry point is the [`arbtest`] function. It accepts a single argument --- a property to
//! test. A property is a function with the following signature:
//!
//! ```
//! /// Panics if the property does not hold.
//! fn property(u: &mut arbitrary::Unstructured) -> arbitrary::Result<()>
//! # { Ok(drop(u)) }
//! ```
//!
//! The `u` argument is a finite random number generator from the [`arbitrary`] crate. You can use
//! `u` to generate pseudo-random structured data:
//!
//! ```
//! # fn property(u: &mut arbitrary::Unstructured) -> arbitrary::Result<()> {
//! let ints: Vec<u32> = u.arbitrary()?;
//! let fruit: &str = u.choose(&["apple", "banana", "cherimoya"])?;
//! # Ok(()) }
//! ```
//!
//! Or use the derive feature of the arbitrary crate to automatically generate arbitrary types:
//!
//! ```
//! # fn property(u: &mut arbitrary::Unstructured) -> arbitrary::Result<()> {
//! #[derive(arbitrary::Arbitrary)]
//! struct Color { r: u8, g: u8, b: u8 }
//!
//! let random_color = u.arbitrary::<Color>()?;
//! # Ok(()) }
//! ```
//! Property function should use randomly generated data to assert some interesting behavior of the
//! implementation, which should hold for _any_ values. For example, converting a color to string
//! and then parsing it back should result in the same color:
//!
//! ```
//! # type Color = u8; // lol
//! #[test]
//! fn parse_is_display_inverted() {
//!     arbtest(|u| {
//!         let c1: Color = u.arbitrary();
//!         let c2: Color = c1.to_string().parse().unwrap();
//!         assert_eq!(c1, c2);
//!         Ok(())
//!     })
//! }
//! ```
//!
//! After you have supplied the property function, arbtest repeatedly runs it in a loop, passing
//! more and more [`arbitrary::Unstructured`] bytes until the property panics. Upon a failure, a
//! seed is printed. The seed can be used to deterministically replay the failure.
//!
//! ```text
//! thread 'all_numbers_are_even' panicked at src/lib.rs:116:9:
//! assertion failed: number % 2 == 0
//! note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace
//!
//! arbtest failed!
//!     Seed: 0xa88e234400000020
//! ```
//!
//! More features are available with builder-style API on the returned [`ArbTest`] object.
//!
//! ## Time Budgeting
//!
//! ```
//! # use arbtest::arbtest; use std::time::Duration;
//! # fn property(_: &mut arbitrary::Unstructured) -> arbitrary::Result<()> { Ok(()) }
//! arbtest(property).budget_ms(1_000);
//! arbtest(property).budget(Duration::from_secs(1));
//! ```
//!
//! The [`budget`](ArbTest::budget) function controls how long the search loop runs, default is one
//! hundred milliseconds. This default can be overridden with `ARBTEST_BUDGET_MS` environmental
//! variable.
//!
//! ## Size Constraint
//!
//! ```
//! # use arbtest::arbtest;
//! # fn property(_: &mut arbitrary::Unstructured) -> arbitrary::Result<()> { Ok(()) }
//! arbtest(property)
//!     .size_min(1 << 4)
//!     .size_max(1 << 16);
//! ```
//!
//! Internally, [`arbitrary::Unstructured`] is just an `&[u8]` --- a slice of random bytes. The
//! length of this slice determines how much randomness your tests gets to use. A shorter slice
//! contains less entropy and leads to a simpler test case.
//!
//! The [`size_min`](ArbTest::size_min) and [`size_max`](ArbTest::size_max) parameters control the
//! length of this slice: when looking for a failure, `arbtest` progressively increases the size
//! from `size_min` to `size_max`.
//!
//! Note when trying to minimize a known failure, `arbtest` will try to go even smaller than
//! `size_min`.
//!
//! ## Replay and Minimization
//!
//! ```
//! # use arbtest::arbtest;
//! # let property = |_: &mut arbitrary::Unstructured| -> arbitrary::Result<()> { Ok(()) };
//! arbtest(property).seed(0x92);
//! # let property = |_: &mut arbitrary::Unstructured| -> arbitrary::Result<()> { panic!() };
//! arbtest(property).seed(0x92).minimize();
//! ```
//!
//! When a [`seed`](ArbTest::seed) is specified, `arbtest` uses the seed to generate a fixed
//! `Unstructured` and runs the property function once. This is useful to debug a test failure after
//! a failing seed is found through search.
//!
//! If in addition to `seed` [`minimize`](ArbTest::minimize) is set, then `arbtest` will try to find
//! a smaller seed which still triggers a failure. You could use [`budget`](ArbTest::budget) to
//! control how long the minimization runs.
//!
//! ## When the Code Gets Run
//!
//! The [`arbtest`] function doesn't immediately run the code. Instead, it returns an [`ArbTest`]
//! builder object that can be used to further tweak the behavior. The actual execution is triggered
//! from the [`ArbTest::drop`]. If panicking in `drop` is not your thing, you can trigger
//! the execution explicitly using [`ArbTest::run`] method:
//!
//! ```
//! # use arbtest::arbtest;
//! # fn property(_: &mut arbitrary::Unstructured) -> arbitrary::Result<()> { Ok(()) }
//! let builder = arbtest(property);
//! drop(builder); // This line actually runs the tests.
//!
//! arbtest(property).run(); // Request the run explicitly.
//! ```
//!
//! ## Errors
//!
//! Property failures should be reported via a panic, for example, using `assert_eq!` macros.
//! Returning an `Err(arbitrary::Error)` doesn't signal a test failure, it just means that there
//! isn't enough entropy left to complete the test. Instead of returning an [`arbitrary::Error`], a
//! test might choose to continue in a non-random way. For example, when testing a distributed
//! system you might use the following template:
//!
//! ```text
//! while !u.is_empty() && network.has_messages_in_flight() {
//!     network.drop_and_permute_messages(u);
//!     network.deliver_next_message();
//! }
//! while network.has_messages_in_flight() {
//!     network.deliver_next_message();
//! }
//! ```
//!
//! ## Imports
//!
//! Recommended way to import:
//!
//! ```toml
//! [dev-dependencies]
//! arbtest = "0.3"
//! ```
//!
//! ```
//! #[cfg(test)]
//! mod tests {
//!     use arbtest::{arbtest, arbitrary};
//!
//!     fn my_property(u: &mut arbitrary::Unstructured) -> arbitrary::Result<()> { Ok(()) }
//! }
//! ```
//!
//! If you want to `#[derive(Arbitrary)]`, you need to explicitly add Cargo.toml dependency for the
//! [`arbitrary`] crate:
//!
//! ```toml
//! [dependencies]
//! arbitrary = { version = "1", features = ["derive"] }
//!
//! [dev-dependencies]
//! arbtest = "0.3"
//! ```
//!
//! ```
//! #[derive(arbitrary::Arbitrary)]
//! struct Color { r: u8, g: u8, b: u8 }
//!
//! #[cfg(test)]
//! mod tests {
//!     use arbtest::arbtest;
//!
//!     #[test]
//!     fn display_parse_identity() {
//!         arbtest(|u| {
//!             let c1: Color = u.arbitrary()?;
//!             let c2: Color = c1.to_string().parse();
//!             assert_eq!(c1, c2);
//!             Ok(())
//!         });
//!     }
//! }
//! ```
//!
//! Note that `arbitrary` is a non-dev dependency. This is not strictly required, but is helpful to
//! allow downstream crates to run their tests with arbitrary values of `Color`.
//!
//! ## Design
//!
//! Most of the heavy lifting is done by the [`arbitrary`] crate. Its [`arbitrary::Unstructured`] is
//! a brilliant abstraction which works both for coverage-guided fuzzing as well as for automated
//! minimization. That is, you can plug `arbtest` properties directly into `cargo fuzz`, API is
//! fully compatible.
//!
//! Property function uses `&mut Unstructured` as an argument instead of `T: Arbitrary`, allowing
//! the user to generate any `T` they want imperatively. The smaller benefit here is implementation
//! simplicity --- the property type is not generic. The bigger benefit is that this API is more
//! expressive, as it allows for _interactive_ properties. For example, a network simulation for a
//! distributed system doesn't have to generate "failure plan" upfront, it can use `u` during the
//! test run to make _dynamic_ decisions about which existing network packets to drop!
//!
//! A "seed" is an `u64`, by convention specified in hexadecimal. The low 32 bits of the seed
//! specify the length of the underlying `Unstructured`. The high 32 bits are the random seed
//! proper, which is feed into a simple xor-shift to generate `Unstructured` of the specified
//! length.
//!
//! If you like this crate, you might enjoy <https://github.com/graydon/exhaustigen-rs> as well.
#![deny(missing_docs)]

use std::{
    collections::hash_map::RandomState,
    fmt,
    hash::{BuildHasher, Hasher},
    panic::AssertUnwindSafe,
    time::{Duration, Instant},
};

#[doc(no_inline)]
pub use arbitrary;

/// Repeatedly test `property` with different random seeds.
///
/// Return value is a builder object which can be used to tweak behavior.
pub fn arbtest<P>(property: P) -> ArbTest<P>
where
    P: FnMut(&mut arbitrary::Unstructured<'_>) -> arbitrary::Result<()>,
{
    let options =
        Options { size_min: 32, size_max: 65_536, budget: None, seed: None, minimize: false };
    ArbTest { property, options }
}

/// A builder for a property-based test.
///
/// This builder allows customizing various aspects of the test, such as the
/// initial random seed, the amount of iterations to try, or the amount of
/// random numbers (entropy) each test run gets.
///
/// For convenience, `ArbTest` automatically runs the test on drop. You can use [`ArbTest::run`]
/// to run the test explicitly.
pub struct ArbTest<P>
where
    P: FnMut(&mut arbitrary::Unstructured<'_>) -> arbitrary::Result<()>,
{
    property: P,
    options: Options,
}

struct Options {
    size_min: u32,
    size_max: u32,
    budget: Option<Duration>,
    seed: Option<Seed>,
    minimize: bool,
}

impl<P> ArbTest<P>
where
    P: FnMut(&mut arbitrary::Unstructured<'_>) -> arbitrary::Result<()>,
{
    /// Sets the lower bound on the amount of random bytes each test run gets.
    ///
    /// Defaults to 32.
    ///
    /// Each randomized test gets an [arbitrary::Unstructured] as a source of
    /// randomness. `Unstructured` can be thought of as a *finite* pseudo random
    /// number generator, or, alternatively, as a finite sequence of random
    /// numbers. The intuition here is that _shorter_ sequences lead to simpler
    /// test cases.
    ///
    /// The `size` parameter controls the length of the initial random sequence.
    /// More specifically, `arbtest` will run the test function multiple times,
    /// increasing the amount of entropy from `size_min` to `size_max`.
    pub fn size_min(mut self, size: u32) -> Self {
        self.options.size_min = size;
        self
    }

    /// Sets the upper bound on the amount of random bytes each test run gets.
    ///
    /// Defaults to 64 536.
    ///
    /// See [`ArbTest::size_min`].
    pub fn size_max(mut self, size: u32) -> Self {
        self.options.size_max = size;
        self
    }

    /// Sets the approximate duration for the tests.
    ///
    /// Defaults to 100ms, can be overridden via `ARBTEST_BUDGET_MS` environmental variable.
    ///
    /// `arbtest` will re-run the test function until the time runs out or until it panics.
    pub fn budget(mut self, value: Duration) -> Self {
        self.options.budget = Some(value);
        self
    }

    /// Sets the approximate duration for the tests, in milliseconds.
    pub fn budget_ms(self, value: u64) -> Self {
        self.budget(Duration::from_millis(value))
    }

    /// Fixes the random seed.
    ///
    /// Normally, `arbtest` runs the test function multiple times, picking a
    /// fresh random seed of an increased complexity every time.
    ///
    /// If the `seed` is set explicitly, the `test` function is run only once.
    pub fn seed(mut self, seed: u64) -> Self {
        self.options.seed = Some(Seed::new(seed));
        self
    }

    /// Whether to try to minimize the seed after failure.
    pub fn minimize(mut self) -> Self {
        self.options.minimize = true;
        self
    }

    /// Runs the test.
    ///
    /// This is equivalent to just dropping `ArbTest`.
    pub fn run(mut self) {
        self.context().run();
    }

    fn context(&mut self) -> Context<'_, '_> {
        Context { property: &mut self.property, options: &self.options, buffer: Vec::new() }
    }
}

impl<P> Drop for ArbTest<P>
where
    P: FnMut(&mut arbitrary::Unstructured<'_>) -> arbitrary::Result<()>,
{
    fn drop(&mut self) {
        self.context().run();
    }
}

type DynProperty<'a> = &'a mut dyn FnMut(&mut arbitrary::Unstructured<'_>) -> arbitrary::Result<()>;

struct Context<'a, 'b> {
    property: DynProperty<'a>,
    options: &'b Options,
    buffer: Vec<u8>,
}

impl<'a, 'b> Context<'a, 'b> {
    fn run(&mut self) {
        let budget = {
            let default = Duration::from_millis(100);
            self.options.budget.or_else(env_budget).unwrap_or(default)
        };

        match (self.options.seed, self.options.minimize) {
            (None, false) => self.run_search(budget),
            (None, true) => panic!("can't minimize without a seed"),
            (Some(seed), false) => self.run_reproduce(seed),
            (Some(seed), true) => self.run_minimize(seed, budget),
        }
    }

    fn run_search(&mut self, budget: Duration) {
        let t = Instant::now();

        let mut last_result = Ok(());
        let mut seen_success = false;

        let mut size = self.options.size_min;
        'search: loop {
            for _ in 0..3 {
                if t.elapsed() > budget {
                    break 'search;
                }

                let seed = Seed::gen(size);
                {
                    let guard = PrintSeedOnPanic::new(seed);
                    last_result = self.try_seed(seed);
                    seen_success = seen_success || last_result.is_ok();
                    guard.defuse()
                }
            }

            let bigger = (size as u64).saturating_mul(5) / 4;
            size = bigger.clamp(0, self.options.size_max as u64) as u32;
        }

        if !seen_success {
            let error = last_result.unwrap_err();
            panic!("no fitting seeds, last error: {error}");
        }
    }

    fn run_reproduce(&mut self, seed: Seed) {
        let guard = PrintSeedOnPanic::new(seed);
        self.try_seed(seed).unwrap_or_else(|error| panic!("{error}"));
        guard.defuse()
    }

    fn run_minimize(&mut self, seed: Seed, budget: Duration) {
        let old_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| ()));

        if !self.try_seed_panics(seed) {
            std::panic::set_hook(old_hook);
            panic!("seed {seed} did not panic")
        }

        let mut seed = seed;
        let t = std::time::Instant::now();

        let minimizers = [|s| s / 2, |s| s * 9 / 10, |s| s - 1];
        let mut minimizer = 0;

        let mut last_minimization = Instant::now();
        'search: loop {
            let size = seed.size();
            eprintln!("seed {seed}, seed size {size}, search time {:0.2?}", t.elapsed());
            if size == 0 {
                break;
            }
            loop {
                if t.elapsed() > budget {
                    break 'search;
                }
                if last_minimization.elapsed() > budget / 5 && minimizer < minimizers.len() - 1 {
                    minimizer += 1;
                }
                let size = minimizers[minimizer](size);
                let candidate_seed = Seed::gen(size);
                if self.try_seed_panics(candidate_seed) {
                    seed = candidate_seed;
                    last_minimization = Instant::now();
                    continue 'search;
                }
            }
        }
        std::panic::set_hook(old_hook);
        let size = seed.size();
        eprintln!("minimized");
        eprintln!("seed {seed}, seed size {size}, search time {:0.2?}", t.elapsed());
    }

    fn try_seed(&mut self, seed: Seed) -> arbitrary::Result<()> {
        seed.fill(&mut self.buffer);
        let mut u = arbitrary::Unstructured::new(&self.buffer);
        (self.property)(&mut u)
    }

    fn try_seed_panics(&mut self, seed: Seed) -> bool {
        let mut me = AssertUnwindSafe(self);
        std::panic::catch_unwind(move || {
            let _ = me.try_seed(seed);
        })
        .is_err()
    }
}

fn env_budget() -> Option<Duration> {
    let var = std::env::var("ARBTEST_BUDGET_MS").ok()?;
    let ms = var.parse::<u64>().ok()?;
    Some(Duration::from_millis(ms))
}

/// Random seed used to generated an `[u8]` underpinning the `Unstructured`
/// instance we pass to user's code.
///
/// The seed is two `u32` mashed together. Low half defines the *length* of the
/// sequence, while the high bits are the random seed proper.
///
/// The reason for this encoding is to be able to print a seed as a single
/// copy-pastable number.
#[derive(Clone, Copy)]
struct Seed {
    repr: u64,
}

impl fmt::Display for Seed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\x1b[1m0x{:016x}\x1b[0m", self.repr)
    }
}

impl Seed {
    fn new(repr: u64) -> Seed {
        Seed { repr }
    }
    fn gen(size: u32) -> Seed {
        let raw = RandomState::new().build_hasher().finish();
        let repr = size as u64 | (raw << u32::BITS);
        Seed { repr }
    }
    fn size(self) -> u32 {
        self.repr as u32
    }
    fn rand(self) -> u32 {
        (self.repr >> u32::BITS) as u32
    }
    fn fill(self, buf: &mut Vec<u8>) {
        buf.clear();
        buf.reserve(self.size() as usize);
        let mut random = self.rand();
        let mut rng = std::iter::repeat_with(move || {
            random ^= random << 13;
            random ^= random >> 17;
            random ^= random << 5;
            random
        });
        while buf.len() < self.size() as usize {
            buf.extend(rng.next().unwrap().to_le_bytes());
        }
    }
}

struct PrintSeedOnPanic {
    seed: Seed,
    active: bool,
}

impl PrintSeedOnPanic {
    fn new(seed: Seed) -> PrintSeedOnPanic {
        PrintSeedOnPanic { seed, active: true }
    }
    fn defuse(mut self) {
        self.active = false
    }
}

impl Drop for PrintSeedOnPanic {
    fn drop(&mut self) {
        if self.active {
            eprintln!("\narbtest failed!\n    Seed: {}\n\n", self.seed)
        }
    }
}
