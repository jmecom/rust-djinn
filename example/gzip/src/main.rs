//! The command line. The driver is `run` at the end of `spec.rs`.
//!
//!   gzip [-N] [FILE] > out.gz    compress FILE (or stdin) at level N (0–10; default 6)
//!   gzip -d [FILE.gz] > out      decompress FILE (or stdin)
//!   gzip -d --workload [FILE...] the decompression time per file (corpora/packed if no files)
//!   gzip --size-only [FILE]      compress and print only the compressed length: the shape of
//!                                lean-zip's `compress-file` race (read, compress, report)
//!   gzip --sizes [FILE...]       compressed sizes next to gzip -9 (the built-in corpus if no files)
//!   gzip --workload [FILE...]    the time per file (the built-in corpus if no files)
//!
//! The input is read with `std::fs::read`, which pre-sizes the buffer from the file length; a
//! redirected stdin (`< file`) is read the same way through `/dev/stdin`.
use std::io::Write;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let is_flag = |a: &str| a.starts_with('-') && a.len() > 1 && !std::path::Path::new(a).exists();
    let flags: Vec<&str> = args.iter().filter(|a| is_flag(a)).map(|a| a.as_str()).collect();
    let files: Vec<String> = args.iter().filter(|a| !is_flag(a)).cloned().collect();
    // `-N` picks the level; `--sizes` and `--workload` use the same level
    if let Some(l) = flags.iter().find_map(|f| f.strip_prefix('-').and_then(|n| n.parse::<u8>().ok())) {
        std::env::set_var("DJINN_BENCH_LEVEL", l.to_string());
    }
    let level = gzip::bench::level();
    let decompress = flags.contains(&"-d");
    if decompress && flags.contains(&"--workload") {
        let corpus = if files.is_empty() { gzip::bench_decompress::packed() } else { gzip::bench_decompress::corpus_from(&files) };
        print!("{}", gzip::bench_decompress::timed(&corpus));
        return;
    }
    if flags.contains(&"--sizes") {
        print!("{}", gzip::bench::sizes(&gzip::bench::corpus_from(&files)));
        return;
    }
    if flags.contains(&"--workload") {
        print!("{}", gzip::bench::timed(&gzip::bench::corpus_from(&files)));
        return;
    }
    let path = files.first().map(String::as_str).unwrap_or("/dev/stdin");
    let input = match std::fs::read(path) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("gzip: cannot read {path}: {e}");
            std::process::exit(1);
        }
    };
    match gzip::run(if decompress { None } else { Some(level) }, &input) {
        Ok(bytes) if flags.contains(&"--size-only") => println!("{}", bytes.len()),
        Ok(bytes) => std::io::stdout().lock().write_all(&bytes).expect("stdout"),
        Err(e) => {
            eprintln!("gzip: {e}");
            std::process::exit(1);
        }
    }
}
