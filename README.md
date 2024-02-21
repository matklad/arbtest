# arbtest

A powerful property-based testing library with a tiny API and a small implementation.

```rust
use arbtest::arbtest;

#[test]
fn all_numbers_are_even() {
    arbtest(|u| {
        let number: u32 = u.arbitrary()?;
        assert!(number % 2 == 0);
        Ok(())
    });
}
```
