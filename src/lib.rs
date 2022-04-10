//! arbtest is a minimalist property-based testing library, waiting for me to
//! write proper docs.
//!
//! In the meantime, take a look at the following example:
//!
//! ```rust
//! fn buggy_sort(xs: &mut [u8]) {
//!     for i in 0..xs.len() {
//!         for j in 0..i {
//!             if xs[i] == xs[j] {
//!                 panic!("BUG")
//!             }
//!         }
//!     }
//!     xs.sort()
//! }
//!
//! #[cfg(test)]
//! mod tests {
//!     use super::*;
//!
//!     use arbtest::arbitrary::{self, Unstructured};
//!
//!     fn prop(u: &mut Unstructured<'_>) -> arbitrary::Result<()> {
//!         let mut xs = u.arbitrary::<Vec<u8>>()?;
//!         buggy_sort(&mut xs);
//!         Ok(())
//!     }
//!
//!     #[test]
//!     fn test() {
//!         arbtest::builder().budget_ms(50_000)
//!             .run(|u| prop(u))
//!     }
//!
//!     #[test]
//!     fn reproduce() {
//!         arbtest::builder().seed(0xde0ad94600000001)
//!             .run(|u| prop(u))
//!     }
//!
//!     #[test]
//!     fn minimize() {
//!         arbtest::builder().seed(0x2d5a75df00003e9a).minimize()
//!             .run(|u| prop(u))
//!     }
//! }
//! ```
//!
//! Notes:
//!
//! * You can use `ARBTEST_BUDGET_MS` to adjust time budget without
//!   recompilation.
//! * While we are waiting for the docs, studying the source might be helpful,
//!   it's short!
//! * If you like this crate, you might enjoy
//!   <https://github.com/graydon/exhaustigen-rs> as well.

use std::{
    collections::hash_map::RandomState,
    fmt,
    hash::{BuildHasher, Hasher},
    panic::AssertUnwindSafe,
    time::{Duration, Instant},
};

use arbitrary::Unstructured;

pub use arbitrary;

pub type Property = fn(u: &mut Unstructured<'_>) -> arbitrary::Result<()>;

pub fn builder() -> Builder {
    let env_budget = env_budget();
    Builder {
        env_budget,
        min_size: 32,
        max_size: 65_536,
        budget: None,
        seed: None,
        minimize: false,
        buf: Vec::new(),
    }
}

pub struct Builder {
    env_budget: Option<Duration>,
    min_size: u32,
    max_size: u32,
    budget: Option<Duration>,
    seed: Option<Seed>,
    minimize: bool,
    buf: Vec<u8>,
}

impl Builder {
    pub fn min_size(mut self, size: u32) -> Builder {
        self.min_size = size;
        self
    }
    pub fn max_size(mut self, size: u32) -> Builder {
        self.max_size = size;
        self
    }
    pub fn budget(mut self, value: Duration) -> Builder {
        self.budget = Some(value);
        self
    }
    pub fn budget_ms(self, value: u64) -> Builder {
        self.budget(Duration::from_millis(value))
    }
    pub fn seed(mut self, seed: u64) -> Builder {
        self.seed = Some(Seed::new(seed));
        self
    }
    pub fn minimize(mut self) -> Builder {
        self.minimize = true;
        self
    }

    pub fn run(mut self, prop: Property) {
        if let Some(seed) = self.seed {
            if self.minimize {
                self.do_minimize(seed, prop)
            } else {
                self.reproduce(seed, prop);
            }
            return;
        }

        let budget = self.get_budget(Duration::from_millis(100));
        let t = Instant::now();
        let mut size = self.min_size;
        'search: loop {
            for _ in 0..3 {
                if t.elapsed() > budget {
                    break 'search;
                }

                let seed = Seed::gen(size);
                self.reproduce(seed, prop);
            }

            let bigger = (size as u64).saturating_mul(5) / 4;
            size = if bigger < self.max_size as u64 { bigger as u32 } else { self.max_size };
        }
    }

    fn reproduce(&mut self, seed: Seed, prop: Property) {
        let g = Guard::new(seed);
        self.single_run(seed, prop);
        g.defuse()
    }
    fn do_minimize(&mut self, seed: Seed, prop: Property) {
        std::panic::set_hook(Box::new(|_| ()));
        if !self.fails(seed, prop) {
            panic!("seed {seed} did not fail")
        }
        let mut seed = seed;
        let budget = self.get_budget(Duration::from_secs(50));
        let t = std::time::Instant::now();

        let minimizers = [|s| s / 2, |s| s * 9 / 10, |s| s - 1];
        let mut minimizer = 0;

        let mut last_minimization = Instant::now();
        'search: loop {
            let size = seed.size();
            eprintln!("seed {seed}, size {size}, {:0.2?}", t.elapsed());
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
                if self.fails(candidate_seed, prop) {
                    seed = candidate_seed;
                    last_minimization = Instant::now();
                    continue 'search;
                }
            }
        }
        let size = seed.size();
        eprintln!("minimized");
        eprintln!("seed {seed}, size {size}, {:0.2?}", t.elapsed());
    }

    fn get_budget(&self, default: Duration) -> Duration {
        self.budget.or(self.env_budget).unwrap_or(default)
    }

    fn single_run(&mut self, seed: Seed, prop: Property) {
        seed.fill(&mut self.buf);
        let mut u = Unstructured::new(&self.buf);
        let _ = prop(&mut u);
    }
    fn fails(&mut self, seed: Seed, prop: Property) -> bool {
        let this = AssertUnwindSafe(self);
        std::panic::catch_unwind(move || {
            let that = this;
            that.0.single_run(seed, prop)
        })
        .is_err()
    }
}

fn env_budget() -> Option<Duration> {
    let var = std::env::var("ARBTEST_BUDGET_MS").ok()?;
    let ms = var.parse::<u64>().ok()?;
    Some(Duration::from_millis(ms))
}

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

struct Guard {
    seed: Seed,
    active: bool,
}

impl Guard {
    fn new(seed: Seed) -> Guard {
        Guard { seed, active: true }
    }
    fn defuse(mut self) {
        self.active = false
    }
}

impl Drop for Guard {
    fn drop(&mut self) {
        if self.active {
            eprintln!("\n\narb_test failed!\n    Seed: {}\n\n", self.seed)
        }
    }
}
