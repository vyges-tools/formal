//! Running the programs a campaign drives, and hashing its inputs.

use std::io::Read;
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use sha2::{Digest, Sha256};

pub struct Ran {
    /// The exit code; `None` when it was killed on timeout or by a signal.
    pub code: Option<i32>,
    pub out: String,
    pub err: String,
    pub secs: f64,
    pub timed_out: bool,
}

impl Ran {
    pub fn ok(&self) -> bool {
        self.code == Some(0)
    }
}

/// Run `cmd` in its own process group; on timeout kill the whole group (a solver forks).
pub fn run(cmd: &[String], timeout: Option<Duration>, cwd: Option<&Path>) -> std::io::Result<Ran> {
    let t0 = Instant::now();
    let mut c = Command::new(&cmd[0]);
    c.args(&cmd[1..]).stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::piped());
    if let Some(d) = cwd {
        c.current_dir(d);
    }
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        c.process_group(0);
    }
    let mut child = c.spawn()?;
    // Drain both pipes while waiting, so a chatty child never blocks on a full pipe.
    let mut so = child.stdout.take().unwrap();
    let mut se = child.stderr.take().unwrap();
    let ro = std::thread::spawn(move || {
        let mut s = String::new();
        let _ = so.read_to_string(&mut s);
        s
    });
    let re = std::thread::spawn(move || {
        let mut s = String::new();
        let _ = se.read_to_string(&mut s);
        s
    });
    let mut timed_out = false;
    let status = loop {
        if let Some(st) = child.try_wait()? {
            break Some(st);
        }
        if timeout.is_some_and(|t| t0.elapsed() >= t) {
            timed_out = true;
            kill_group(child.id());
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        std::thread::sleep(Duration::from_millis(50));
    };
    Ok(Ran {
        code: status.and_then(|s| s.code()),
        out: ro.join().unwrap_or_default(),
        err: re.join().unwrap_or_default(),
        secs: t0.elapsed().as_secs_f64(),
        timed_out,
    })
}

// `--` before the negative pid: procps `kill` otherwise reads `-<pgid>` as an option and kills
// nothing, so the solver runs to its end past the timeout.
fn kill_group(pid: u32) {
    #[cfg(unix)]
    {
        let _ = Command::new("kill")
            .args(["-KILL", "--", &format!("-{pid}")])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();
    }
    #[cfg(not(unix))]
    let _ = pid;
}

/// The last `n` bytes of `s`, cut on a character boundary.
pub fn tail(s: &str, n: usize) -> String {
    let mut i = s.len().saturating_sub(n);
    while !s.is_char_boundary(i) {
        i += 1;
    }
    s[i..].to_string()
}

pub fn sha256(path: &Path) -> std::io::Result<String> {
    let mut f = std::fs::File::open(path)?;
    let mut h = Sha256::new();
    let mut buf = vec![0u8; 1 << 20];
    loop {
        let n = f.read(&mut buf)?;
        if n == 0 {
            break;
        }
        h.update(&buf[..n]);
    }
    Ok(h.finalize().iter().map(|b| format!("{b:02x}")).collect())
}

/// A program on PATH, as a path.
pub fn which(name: &str) -> Option<String> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|d| d.join(name))
        .find(|p| p.is_file())
        .map(|p| p.to_string_lossy().into_owned())
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    #[test]
    fn a_timeout_kills_the_child_and_says_so() {
        let cmd: Vec<String> = ["sh", "-c", "sleep 30"].iter().map(|s| s.to_string()).collect();
        let r = super::run(&cmd, Some(Duration::from_millis(300)), None).unwrap();
        assert!(r.timed_out && r.code.is_none() && r.secs < 10.0);
    }

    #[test]
    fn output_and_exit_code_come_back() {
        let cmd: Vec<String> = ["sh", "-c", "echo hi; echo err >&2; exit 3"].iter().map(|s| s.to_string()).collect();
        let r = super::run(&cmd, None, None).unwrap();
        assert_eq!((r.code, r.out.as_str(), r.err.as_str(), r.timed_out), (Some(3), "hi\n", "err\n", false));
    }
}
