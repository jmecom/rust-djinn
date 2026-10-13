//! The workloads for `cargo djinn bench` and `cargo djinn optimize`, over a corpus of several
//! kinds of data from a few KB to a few MB: `workload_compress` (the compression side; the
//! decompression side is `bench_decompress::workload_decompress`; `[package.metadata.djinn] bench`
//! picks one).
//! Human-written and trusted only for timing; correctness comes from the verifier.
//!
//! `cargo run --release -- --sizes [FILE...]` prints compressed sizes next to the system gzip's,
//! which is how the compression ratio is tracked; `-- --workload [FILE...]` times one pass. Without
//! files both use the built-in corpus.

/// A deterministic xorshift generator.
pub struct Rng(u64);
impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed | 1)
    }
    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

const WORDS: &[&str] = &[
    "the", "of", "and", "to", "in", "a", "is", "that", "for", "it", "as", "was", "with", "be", "by", "on", "not", "he",
    "this", "are", "or", "his", "from", "at", "which", "but", "have", "an", "had", "they", "you", "were", "their", "one",
    "all", "we", "can", "her", "has", "there", "been", "if", "more", "when", "will", "would", "who", "so", "no", "she",
    "specification", "compress", "decompress", "verified", "theorem", "block", "symbol", "length", "distance", "stream",
    "encoder", "decoder", "proof", "obligation", "relation", "function", "implementation", "unambiguous", "grid", "code",
];

/// Text with a Zipf-like word distribution, sentences and paragraphs.
pub fn text(rng: &mut Rng, bytes: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(bytes + 32);
    let mut line = 0;
    while v.len() < bytes {
        let r = rng.below(1000) as usize;
        let i = if r < 500 { r % 20 } else if r < 850 { 20 + r % 30 } else { 50 + r % 20 };
        v.extend_from_slice(WORDS[i].as_bytes());
        line += WORDS[i].len() + 1;
        if rng.below(12) == 0 {
            v.extend_from_slice(b". ");
        } else if line > 72 {
            v.push(b'\n');
            line = 0;
            if rng.below(8) == 0 {
                v.push(b'\n');
            }
        } else {
            v.push(b' ');
        }
    }
    v.truncate(bytes);
    v
}

/// Rust source: this crate's own specification, as many times as needed.
pub fn source(bytes: usize) -> Vec<u8> {
    let spec = include_bytes!("spec.rs");
    let mut v = Vec::with_capacity(bytes);
    while v.len() < bytes {
        v.extend_from_slice(spec);
    }
    v.truncate(bytes);
    v
}

/// Incompressible bytes.
pub fn random(rng: &mut Rng, bytes: usize) -> Vec<u8> {
    (0..bytes).map(|_| rng.next() as u8).collect()
}

/// Numbers in columns, like a log or a CSV export.
pub fn table(rng: &mut Rng, bytes: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(bytes + 64);
    let mut t: u64 = 1_700_000_000;
    while v.len() < bytes {
        t += rng.below(90);
        let a = rng.below(1000);
        let b = (rng.below(100000) as f64) / 100.0;
        v.extend_from_slice(format!("{t},sensor{},{a},{b:.2},{}\n", rng.below(16), if rng.below(10) == 0 { "ALERT" } else { "ok" }).as_bytes());
    }
    v.truncate(bytes);
    v
}

/// Runs, periodic patterns and far copies: the match search's hard cases, with the lengths of
/// the runs and patterns growing with `DJINN_BENCH_SCALE` (an unoptimised exact search is cubic
/// on a run, so scale 1 keeps them short).
pub fn repetitive(rng: &mut Rng, bytes: usize, scale: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(bytes + 4096);
    let long = 48 * scale;
    while v.len() < bytes {
        match rng.below(4) {
            0 => {
                let b = rng.next() as u8;
                let n = 8 + rng.below(long as u64) as usize;
                v.extend(std::iter::repeat(b).take(n));
            }
            1 => {
                let period = 1 + rng.below(40) as usize;
                let pat: Vec<u8> = (0..period).map(|_| rng.next() as u8).collect();
                let n = 16 + rng.below(4 * long as u64) as usize;
                for k in 0..n {
                    v.push(pat[k % period]);
                }
            }
            2 => {
                let back = (1 + rng.below(40000) as usize).min(v.len().max(1));
                let n = 50 + rng.below(1000) as usize;
                let start = v.len() - back;
                for k in 0..n {
                    let b = v[start + k];
                    v.push(b);
                }
            }
            _ => {
                let n = 100 + rng.below(400) as usize;
                v.extend(text(rng, n));
            }
        }
    }
    v.truncate(bytes);
    v
}

/// Machine code or other binary data, the short-match-heavy kind of input (executables, object
/// files, raw images) that the synthetic entries lack. No sample ships with the crate: bring your
/// own file and name it in `DJINN_BENCH_BINARY` (any compiled executable will do). The entry is
/// `bytes` from 2 MiB into the file (from its start if it is smaller), so a release build of some
/// program gives code rather than headers. Without the variable the corpus has no binary entry.
pub fn binary(bytes: usize) -> Option<Vec<u8>> {
    let path = std::env::var("DJINN_BENCH_BINARY").ok()?;
    let all = std::fs::read(&path).unwrap_or_else(|e| panic!("DJINN_BENCH_BINARY={path}: {e}"));
    let from = if all.len() >= (2 << 20) + bytes { 2 << 20 } else { 0 };
    Some(all[from..(from + bytes).min(all.len())].to_vec())
}

/// The corpus: name, bytes. `DJINN_BENCH_SCALE` (default 1) multiplies every size but the first,
/// so that the same workload can follow the implementation as it gets faster: scale 1 is about
/// 250 KB in all, scale 8 about 2 MB with a 512 KB file.
pub fn corpus() -> Vec<(&'static str, Vec<u8>)> {
    let scale: usize = std::env::var("DJINN_BENCH_SCALE").ok().and_then(|s| s.parse().ok()).unwrap_or(1);
    let k = (16 << 10) * scale;
    let mut rng = Rng::new(0x9E37_79B9_7F4A_7C15);
    let mut c = vec![
        ("text-4k", text(&mut rng, 4 << 10)),
        ("text", text(&mut rng, 2 * k)),
        ("source", source(2 * k)),
        ("random", random(&mut rng, k)),
        ("table", table(&mut rng, 2 * k)),
        ("repetitive", repetitive(&mut rng, 2 * k, scale)),
    ];
    // mixed: a concatenation that rewards block splitting
    let mut mixed = Vec::new();
    mixed.extend_from_slice(&c[1].1[..k]);
    mixed.extend_from_slice(&c[3].1[..k / 2]);
    mixed.extend_from_slice(&c[4].1[..k / 2]);
    mixed.extend_from_slice(&c[2].1[..k]);
    c.push(("mixed", mixed));
    c.push(("text-large", text(&mut rng, 4 * k)));
    if let Some(b) = binary(2 * k) {
        c.push(("binary", b));
    }
    c
}

/// The corpus to report on: the given files, or the built-in corpus if there are none.
pub fn corpus_from(files: &[String]) -> Vec<(String, Vec<u8>)> {
    if files.is_empty() {
        return corpus().into_iter().map(|(n, d)| (n.to_string(), d)).collect();
    }
    files
        .iter()
        .map(|f| {
            let data = std::fs::read(f).unwrap_or_else(|e| panic!("{f}: {e}"));
            let name = std::path::Path::new(f).file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or(f.clone());
            (name, data)
        })
        .collect()
}

/// The compression level the workloads and tables use: `DJINN_BENCH_LEVEL`, default 6 (gzip's
/// default, and the level lean-zip's headline comparison is made at). What a level means is the
/// implementer's: the specification fixes only that 0 emits no copies.
pub fn level() -> u8 {
    std::env::var("DJINN_BENCH_LEVEL").ok().and_then(|v| v.parse().ok()).unwrap_or(6)
}

/// The compression side alone: compress the corpus at `level`, no round trip, and return the
/// total compressed size. The workload of the compression crate's `optimize`, which measures it
/// at every level named by `bench_points` in Cargo.toml and judges the (size, time) curve.
pub fn workload_compress(level: usize) -> usize {
    let mut total = 0usize;
    for (_, data) in bench_corpus() {
        total += crate::compress(&data, level as u8).len();
    }
    total
}

/// The corpus the workloads use: `DJINN_BENCH_CORPUS=dir` for a directory of files, else the
/// built-in one.
fn bench_corpus() -> Vec<(String, Vec<u8>)> {
    match std::env::var("DJINN_BENCH_CORPUS") {
        Ok(dir) => {
            let mut files: Vec<String> = std::fs::read_dir(&dir)
                .unwrap_or_else(|e| panic!("{dir}: {e}"))
                .filter_map(|e| e.ok())
                .filter(|e| e.file_type().map(|t| t.is_file()).unwrap_or(false))
                .map(|e| e.path().to_string_lossy().into_owned())
                .collect();
            files.sort();
            corpus_from(&files)
        }
        Err(_) => corpus_from(&[]),
    }
}

/// One pass over a corpus with the time of each file, at the bench level; each result is
/// decompressed by the system `gzip -d` as a check: `cargo run --release -- --workload`.
pub fn timed(corpus: &[(String, Vec<u8>)]) -> String {
    let mut out = String::from("file                 bytes   compress      MB/s     packed\n");
    for (name, data) in corpus {
        let t0 = std::time::Instant::now();
        let packed = crate::compress(data, level());
        let c = t0.elapsed().as_secs_f64();
        let back = gunzip(&packed);
        assert!(back.as_deref() == Some(data.as_slice()), "{name}: gzip -d does not give the input back");
        let mb = data.len() as f64 / 1e6;
        let line = format!("{name:18} {:9} {c:8.3} s {:8.1} {:10}\n", data.len(), mb / c, packed.len());
        eprint!("{line}");
        out.push_str(&line);
    }
    out
}

/// The system `gzip -d` on a stream, if it is installed (else `None`: no check).
fn gunzip(packed: &[u8]) -> Option<Vec<u8>> {
    let mut child = std::process::Command::new("gzip")
        .arg("-dc")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .ok()?;
    let mut stdin = child.stdin.take()?;
    let input = packed.to_vec();
    let writer = std::thread::spawn(move || {
        use std::io::Write;
        let _ = stdin.write_all(&input);
    });
    let out = child.wait_with_output().ok()?;
    let _ = writer.join();
    if out.status.success() { Some(out.stdout) } else { None }
}

/// A corpus with its compressed sizes, next to `gzip -9` if it is installed.
pub fn sizes(corpus: &[(String, Vec<u8>)]) -> String {
    let mut out = String::from("file                 bytes      ours   gzip -9   ratio\n");
    let (mut ours_total, mut gz_total) = (0usize, 0usize);
    for (name, data) in corpus {
        let packed = crate::compress(data, level());
        // feed gzip from a thread: writing everything before reading would deadlock once its
        // output outgrows the pipe
        let gz = std::process::Command::new("gzip")
            .arg("-9c")
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .and_then(|mut child| {
                let mut stdin = child.stdin.take().unwrap();
                let input = data.clone();
                let writer = std::thread::spawn(move || {
                    use std::io::Write;
                    let _ = stdin.write_all(&input);
                });
                let out = child.wait_with_output();
                let _ = writer.join();
                out
            })
            .map(|o| o.stdout.len())
            .unwrap_or(0);
        ours_total += packed.len();
        gz_total += gz;
        out.push_str(&format!("{name:18} {:9} {:9} {gz:9}   {:.3}\n", data.len(), packed.len(), packed.len() as f64 / gz.max(1) as f64));
    }
    out.push_str(&format!("{:18} {:9} {ours_total:9} {gz_total:9}   {:.3}\n", "total", "", ours_total as f64 / gz_total.max(1) as f64));
    out
}
