pub fn buggy_sort(xs: &mut [u8]) {
    for i in 0..xs.len() {
        for j in 0..i {
            if xs[i] == xs[j] {
                panic!("BUG")
            }
        }
    }
    xs.sort()
}

#[cfg(test)]
mod tests {
    use super::*;

    use arbtest::arbitrary::Unstructured;

    fn prop(u: &mut Unstructured<'_>) -> arbitrary::Result<()> {
        let mut xs = u.arbitrary::<Vec<u8>>()?;
        buggy_sort(&mut xs);
        Ok(())
    }

    #[test]
    fn test() {
        arbtest::builder().budget_ms(50_000).run(|u| prop(u))
    }

    #[test]
    fn reproduce() {
        arbtest::builder().seed(0xde0ad94600000001).run(|u| prop(u))
    }

    #[test]
    fn minimize() {
        arbtest::builder().seed(0x2d5a75df00003e9a).minimize().run(|u| prop(u))
    }
}

fn main() {}
