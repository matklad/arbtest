//! This example uses `arbtest` to find a minimal regex which matches `abba` but
//! not `baab`.
//!
//! With the given seed, we get the following sequence of minimizations:
//!
//! ```
//! (a)|(((a)|(b))|((a(a)|((b)|(((b)*)|(((a)|(b))|((ab)|(((b)*)|(((((a)|(a))|(a))*)|(a))))))))*))a
//! ((b)|(ab)((b)|((a)|(a)))*)|(a)
//! ((((((b)*)|(a))|(a))*)*a)|(a)
//! ((b)|(a))*a
//! ((b)|(a))*a
//! ((b)*a)*
//! ```

use arbtest::{arbitrary, arbtest};
use regex::Regex;

fn arb_regex(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<String> {
    let choices: &[fn(&mut arbitrary::Unstructured<'_>) -> arbitrary::Result<String>] = &[
        |_u| Ok("a".to_string()),
        |_u| Ok("b".to_string()),
        |u| arb_regex(u).map(|r| format!("({r})*")),
        |u| {
            let l = arb_regex(u)?;
            let r = arb_regex(u)?;
            Ok(format!("{l}{r}"))
        },
        |u| {
            let l = arb_regex(u)?;
            let r = arb_regex(u)?;
            Ok(format!("({l})|({r})"))
        },
    ];
    u.choose(choices)?(u)
}

fn main() {
    arbtest(|u| {
        let r = arb_regex(u)?;
        if let Ok(regex) = Regex::new(&format!("^({r})$")) {
            if regex.is_match("abba") && !regex.is_match("baab") {
                eprintln!("{r}");
                panic!()
            }
        }
        Ok(())
    })
    .budget_ms(10_000)
    .seed(0x7abcb62800000020)
    .minimize();
}
