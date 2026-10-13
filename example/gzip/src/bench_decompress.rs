//! The decompression workload, for `cargo djinn bench` and `cargo djinn optimize` through
//! `./optimize-loop.sh decompress` (see the README): decompress a set of gzip streams and check each.
//! Human-written and trusted only for timing; correctness comes from the verifier (and `decompress`
//! checks the CRC-32 and length itself).
//!
//! The streams are made in process: the compression corpus (`bench::corpus`, at
//! `DJINN_BENCH_SCALE`) compressed by our own `compress` at levels 1, 6 and 10, so they cover
//! stored, fixed and dynamic blocks, short and long matches. `DJINN_BENCH_PACKED=dir` uses the
//! `.gz` files of a directory instead (e.g. streams from other encoders).
//! `cargo run --release -- -d --workload [FILE...]` prints the time per stream.

/// The packed corpus: name and compressed bytes, sorted by name.
pub fn packed() -> Vec<(String, Vec<u8>)> {
    if let Ok(dir) = std::env::var("DJINN_BENCH_PACKED") {
        let mut files: Vec<String> = std::fs::read_dir(&dir)
            .unwrap_or_else(|e| panic!("{dir}: {e}"))
            .filter_map(|e| e.ok())
            .filter(|e| e.file_type().map(|t| t.is_file()).unwrap_or(false))
            .map(|e| e.path().to_string_lossy().into_owned())
            .collect();
        files.sort();
        return corpus_from(&files);
    }
    let mut out = Vec::new();
    for (name, data) in crate::bench::corpus() {
        for level in [1u8, 6, 10] {
            out.push((format!("{name}.l{level}.gz"), crate::compress(&data, level)));
        }
    }
    out.sort();
    out
}

/// The given files, read whole.
pub fn corpus_from(files: &[String]) -> Vec<(String, Vec<u8>)> {
    files
        .iter()
        .map(|f| {
            let data = std::fs::read(f).unwrap_or_else(|e| panic!("{f}: {e}"));
            let name = std::path::Path::new(f).file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or(f.clone());
            (name, data)
        })
        .collect()
}

/// Decompresses every packed file once. The files are read once and kept: the first call pays
/// for the reading, during the runner's calibration, never in a timed batch.
pub fn workload_decompress() {
    static PACKED: std::sync::OnceLock<Vec<(String, Vec<u8>)>> = std::sync::OnceLock::new();
    for (name, bytes) in PACKED.get_or_init(packed) {
        let out = crate::decompress(bytes).unwrap_or_else(|| panic!("{name}: decompress failed"));
        std::hint::black_box(out.len());
    }
}

/// One pass with the time of each file.
pub fn timed(corpus: &[(String, Vec<u8>)]) -> String {
    let mut out = String::from("file                      packed      bytes   decompress      MB/s\n");
    for (name, bytes) in corpus {
        let t0 = std::time::Instant::now();
        let data = crate::decompress(bytes).unwrap_or_else(|| panic!("{name}: decompress failed"));
        let d = t0.elapsed().as_secs_f64();
        let line = format!("{name:24} {:8} {:10} {d:9.3} s {:9.1}\n", bytes.len(), data.len(), data.len() as f64 / 1e6 / d);
        eprint!("{line}");
        out.push_str(&line);
    }
    out
}
