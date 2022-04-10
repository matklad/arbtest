use std::time::Instant;

use xshell::{cmd, Shell};

fn main() -> xshell::Result<()> {
    let sh = Shell::new()?;

    {
        let _s = section("BUILD");
        cmd!(sh, "cargo test --workspace --no-run").run()?;
    }

    {
        let _s = section("TEST");
        cmd!(sh, "cargo test --workspace -- --nocapture").run()?;
    }

    {
        let _s = section("PUBLISH");

        let version = cmd!(sh, "cargo pkgid").read()?.rsplit_once('#').unwrap().1.to_string();
        let tag = format!("v{version}");

        let current_branch = cmd!(sh, "git branch --show-current").read()?;
        let has_tag = cmd!(sh, "git tag --list").read()?.lines().any(|it| it.trim() == tag);
        let dry_run = sh.var("CI").is_err() || has_tag || current_branch != "master";
        eprintln!("Publishing{}!", if dry_run { " (dry run)" } else { "" });

        let dry_run_arg = if dry_run { Some("--dry-run") } else { None };
        cmd!(sh, "cargo publish {dry_run_arg...}").run()?;
        if dry_run {
            eprintln!("{}", cmd!(sh, "git tag {tag}"));
            eprintln!("{}", cmd!(sh, "git push --tags"));
        } else {
            cmd!(sh, "git tag {tag}").run()?;
            cmd!(sh, "git push --tags").run()?;
        }
    }
    Ok(())
}

fn section(name: &'static str) -> impl Drop {
    println!("::group::{name}");
    let start = Instant::now();
    defer(move || {
        let elapsed = start.elapsed();
        eprintln!("{name}: {elapsed:.2?}");
        println!("::endgroup::");
    })
}

fn defer<F: FnOnce()>(f: F) -> impl Drop {
    struct D<F: FnOnce()>(Option<F>);
    impl<F: FnOnce()> Drop for D<F> {
        fn drop(&mut self) {
            if let Some(f) = self.0.take() {
                f()
            }
        }
    }
    D(Some(f))
}
