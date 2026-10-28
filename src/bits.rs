//! A bit vector of any width, for the values a counterexample gives a bus. A bus can be wider than
//! any machine integer (a TL-UL request is 110 bits), and its value is shown in hex.

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Bits(Vec<u64>);

impl Bits {
    pub fn set(&mut self, bit: usize) {
        let w = bit / 64;
        if self.0.len() <= w {
            self.0.resize(w + 1, 0);
        }
        self.0[w] |= 1 << (bit % 64);
    }

    pub fn is_zero(&self) -> bool {
        self.0.iter().all(|w| *w == 0)
    }

    /// More than the value 1: shown in hex rather than as a bare 0/1.
    pub fn gt1(&self) -> bool {
        self.0.first().is_some_and(|w| *w > 1) || self.0.iter().skip(1).any(|w| *w != 0)
    }

    /// Lowercase hex, no leading zeros, `0` for zero.
    pub fn hex(&self) -> String {
        let Some(top) = self.0.iter().rposition(|w| *w != 0) else {
            return "0".into();
        };
        let mut s = format!("{:x}", self.0[top]);
        for w in self.0[..top].iter().rev() {
            s.push_str(&format!("{w:016x}"));
        }
        s
    }
}

#[cfg(test)]
mod tests {
    use super::Bits;

    #[test]
    fn hex_spans_words_and_keeps_inner_zeros() {
        let mut b = Bits::default();
        assert_eq!(b.hex(), "0");
        assert!(b.is_zero() && !b.gt1());
        b.set(0);
        assert_eq!(b.hex(), "1");
        assert!(!b.gt1());
        b.set(109);
        assert_eq!(b.hex(), "2000000000000000000000000001");
        assert!(b.gt1());
    }
}
