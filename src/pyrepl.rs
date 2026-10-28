//! A mutant's `replace` text, read the way manifests are written: `\n` and `\t` are a newline and a
//! tab, `\\` is a backslash, `\1`..`\99` and `\g<N>` are the pattern's groups. Any other `\x` is kept
//! as written. `$` is literal (the regex crate's own `$1` syntax is not used).

use regex::Captures;

pub fn expand(template: &str, caps: &Captures) -> String {
    let mut out = String::new();
    let b = template.as_bytes();
    let mut i = 0;
    while i < b.len() {
        if b[i] != b'\\' || i + 1 == b.len() {
            let ch = template[i..].chars().next().unwrap();
            out.push(ch);
            i += ch.len_utf8();
            continue;
        }
        match b[i + 1] {
            b'n' => out.push('\n'),
            b't' => out.push('\t'),
            b'r' => out.push('\r'),
            b'\\' => out.push('\\'),
            b'0'..=b'9' => {
                let mut j = i + 1;
                while j < b.len() && j < i + 3 && b[j].is_ascii_digit() {
                    j += 1;
                }
                let g: usize = template[i + 1..j].parse().unwrap();
                out.push_str(caps.get(g).map(|m| m.as_str()).unwrap_or(""));
                i = j;
                continue;
            }
            b'g' if b.get(i + 2) == Some(&b'<') => {
                if let Some(end) = template[i + 3..].find('>') {
                    let name = &template[i + 3..i + 3 + end];
                    let m = name.parse::<usize>().ok().and_then(|g| caps.get(g)).or_else(|| caps.name(name));
                    out.push_str(m.map(|m| m.as_str()).unwrap_or(""));
                    i += 4 + end;
                    continue;
                }
                out.push_str("\\g");
            }
            c => {
                out.push('\\');
                out.push(c as char);
            }
        }
        i += 2;
    }
    out
}

#[cfg(test)]
mod tests {
    use regex::Regex;

    #[test]
    fn escapes_and_groups_expand_dollar_stays_literal() {
        let re = Regex::new(r"if \((\w+)\)").unwrap();
        let caps = re.captures("if (ready)").unwrap();
        assert_eq!(super::expand(r"if (!\1)\n\t$x \\ \g<1>", &caps), "if (!ready)\n\t$x \\ ready");
    }
}
