#!/usr/bin/env bash
# Hill-climbs one side of the codec indefinitely: one `cargo djinn optimize --cycles 1` per round,
# Claude and Codex taking turns. Each invocation of `optimize` starts with an empty history, so the
# rounds so far are handed to the agent through `--prompt`, built from the log
# (.djinnscratch/optimize-log-<target>.tsv). Accepted rounds leave the new solution and proofs in
# the working tree; commit them yourself.
#
#   ./optimize-loop.sh compress   [optimize args...]   # the default target
#   ./optimize-loop.sh decompress [optimize args...]
#   touch .djinnscratch/optimize-loop.stop             # stop after the round that is running
#   pkill -INT -f 'cargo-djinn optimize'               # and end that round now (it reverts)
#
# compress: the workload is `bench::workload_compress` at every level in `bench_points`, judged as a
# (size, time) curve; implement-prompt.txt is prepended to every prompt. decompress: the script
# points `bench` at `bench_decompress::workload_decompress` (no points) for as long as it runs and
# restores Cargo.toml when it exits; the acceptance threshold defaults to 1.5%.
#
# Codex rounds run at CODEX_EFFORT (default ultra). The points are timed one at a time (BENCH_JOBS,
# default 1) for at least 30 s each: more than one at a time put points on SMT siblings and gave
# 2-7% spreads and false rejections. Claude rounds pick one of the OAuth tokens in ~/.claudetok*
# if there are any (else the logged-in credentials), switching at once when one is exhausted.
set -u

CRATE="$(cd "$(dirname "$0")" && pwd)"
TARGET=compress
case "${1:-}" in compress | decompress) TARGET="$1"; shift ;; esac
STATE="$CRATE/.djinnscratch"
mkdir -p "$STATE"
LOG="$STATE/optimize-log-$TARGET.tsv"
OUT="$STATE/optimize-loop"
STOP="$STATE/optimize-loop.stop"

mkdir -p "$OUT"
echo $$ > "$STATE/optimize-loop.pid"
rm -f "$STOP"
cd "$CRATE" || exit 2

# the binary corpus entry comes from a file of the user's (see README); without it a run would
# measure a different corpus from the rounds before it, so refuse to start
if [ -z "${DJINN_BENCH_BINARY:-}" ] || [ ! -f "$DJINN_BENCH_BINARY" ]; then
    echo "optimize-loop: set DJINN_BENCH_BINARY to a binary file (e.g. any compiled executable); see README" >&2
    exit 2
fi
DJINN_BENCH_BINARY="$(cd "$(dirname "$DJINN_BENCH_BINARY")" && pwd)/$(basename "$DJINN_BENCH_BINARY")"
export DJINN_BENCH_BINARY

THRESHOLD=()
if [ "$TARGET" = decompress ]; then
    # the decoder's workload instead of the compressor's, restored on exit
    cp Cargo.toml "$STATE/Cargo.toml.orig"
    trap 'cp "$STATE/Cargo.toml.orig" Cargo.toml' EXIT
    sed -i -e 's|^bench = .*|bench = "bench_decompress::workload_decompress"|' -e '/^bench_points = /d' Cargo.toml
    THRESHOLD=(--threshold "${DECOMPRESS_THRESHOLD:-1.5}")
fi

# the workload's corpus is generated in process; the scale must be the same for the harness and
# for `./bench` in the jail, so export it. Codex's sandbox has no network for cargo.
export DJINN_BENCH_SCALE="${DJINN_BENCH_SCALE:-4}" CARGO_NET_OFFLINE=true
CODEX_EFFORT="${CODEX_EFFORT-ultra}"
# started from inside a Claude Code session, the Claude agent must not take itself for its child
for v in $(compgen -e | grep -E '^CLAUDE'); do unset "$v"; done

# the Claude agent's credentials: one of the OAuth tokens in ~/.claudetok{,1..5}, a random one
# each Claude round and never the one used the round before; the file's name (not its content)
# is kept in $TOKSTATE. A round that ends on the usage-limit message is retried at once with
# another token, with no back-off.
TOKENS=("$HOME/.claudetok" "$HOME"/.claudetok[1-5])
TOKSTATE="$STATE/optimize-loop.token"
EXHAUSTED="$STATE/optimize-loop.exhausted"   # tokens that hit a limit since the last Claude round that ran
BLOCKED="$STATE/optimize-loop.blocked"       # tokens that answered "out of usage credits": not a window, never retried
FORCEFILE="$STATE/optimize-loop.force"       # a pending retry, kept across restarts of this script
pick_token() {
    local last="" t c=()
    [ -f "$TOKSTATE" ] && last="$(cat "$TOKSTATE")"
    touch "$EXHAUSTED" "$BLOCKED"
    for t in "${TOKENS[@]}"; do [ -f "$t" ] && [ "$t" != "$last" ] && ! grep -qxF "$t" "$EXHAUSTED" && ! grep -qxF "$t" "$BLOCKED" && c+=("$t"); done
    [ ${#c[@]} -eq 0 ] && for t in "${TOKENS[@]}"; do [ -f "$t" ] && [ "$t" != "$last" ] && ! grep -qxF "$t" "$BLOCKED" && c+=("$t"); done
    [ ${#c[@]} -eq 0 ] && for t in "${TOKENS[@]}"; do [ -f "$t" ] && [ "$t" != "$last" ] && c+=("$t"); done
    [ ${#c[@]} -eq 0 ] && for t in "${TOKENS[@]}"; do [ -f "$t" ] && c+=("$t"); done
    [ ${#c[@]} -eq 0 ] && return 1
    printf '%s\n' "${c[@]}" | shuf -n 1
}

[ -f "$LOG" ] || printf 'cycle\ttime_utc\tverdict\tbefore_ms\tmeasured_ms\tafter_ms\tspeedup_total\tcost_usd\ttokens_in\ttokens_out\tagent_wall\tjob\tpoints\tsummary\n' > "$LOG"

# the agent whose turn it is: the one that did not run the last round
next_agent() {
    case "$(awk -F'\t' 'NR > 1 && $12 != "-" { j = $12 } END { print j }' "$LOG")" in
    *-claude) echo codex ;;
    *) echo claude ;;
    esac
}

# the rounds so far, for the agent
history() { # agent
    python3 - "$LOG" "$1" "$TARGET" <<'EOF'
import csv, sys
# what every agent so far had to find out for itself
if sys.argv[2] == "codex":
    print("Your shell is sandboxed, so `./verify` fails there with a read-only file system: verify with "
          "the `verify` tool of the MCP server `djinn`.")
if sys.argv[3] == "compress":
    print(open("implement-prompt.txt").read().strip() + "\n")
else:
    print("This round optimises decompression only: the workload decompresses streams made by our own "
          "compressor (src/bench_decompress.rs). Leave the compressor's code and proofs alone.\n")
print("`./bench --min-time 30 --jobs 1` is how the harness measures (the default 5 s gives single-iteration batches at the slow levels, and more than one point at a time puts points on SMT siblings; both inflate the noise, which raises the acceptance bar): the workload's corpus is generated in process, and DJINN_BENCH_SCALE "
      "is already set in your environment to the scale the harness measures at.\n")
rows = list(csv.DictReader(open(sys.argv[1]), delimiter="\t", quoting=csv.QUOTE_NONE))
rows = [r for r in rows if not r["verdict"].startswith("error")]
if not rows:
    sys.exit(0)
print("This optimisation runs as a series of independent one-cycle invocations, so the history of "
      "attempts above is empty or incomplete. The rounds so far, oldest first (what was accepted is "
      "already in the solution: build on it; do not repeat what was rejected):\n")
for i, r in enumerate(rows):
    keep = 700 if len(rows) - i <= 12 or r["verdict"].startswith("accepted") else 250
    s = r["summary"]
    s = s[:keep] + ("…" if len(s) > keep else "")
    m = f", measured {r['measured_ms']} ms" if r["measured_ms"] != "-" else ""
    p = f"\n  points (level:bytes/ms): {r['points']}" if r["points"] not in ("", "-") else ""
    print(f"- round {r['cycle']}: {r['verdict']} (before {r['before_ms']} ms{m}){p}\n  tried: {s}")
print(f"\nTime before the first round: {rows[0]['before_ms']} ms per workload iteration; now about {rows[-1]['after_ms']} ms.")
EOF
}

# one log line from .djinnscratch/optimize.json (or from the tail of the output, if the run
# never got to an attempt); prints the commit subject, then the body
record() { # cycle started_unix exit_code output_file
    python3 - "$LOG" "$STATE/optimize.json" "$@" <<'EOF'
import csv, json, os, sys, time
log, state, cycle, started, code, out = sys.argv[1:7]
rows = list(csv.DictReader(open(log), delimiter="\t", quoting=csv.QUOTE_NONE))
first = next((float(r["before_ms"]) for r in rows if r["before_ms"] != "-"), None)
ms = lambda ns: "-" if ns is None else f"{ns / 1e6:.1f}"
clean = lambda s: " ".join(str(s).split())
pts = lambda ps: " ".join(f"{p[0]}:{p[1] if p[1] is not None else '?'}/{p[2] / 1e6:.0f}" for p in ps) if ps else "-"
now = time.strftime("%Y-%m-%d %H:%M:%S", time.gmtime())
try:
    j = json.load(open(state))
    if j["started"] < int(started) or not j["attempts"]:
        j = None
except Exception:
    j = None
if j is None:
    tail = [l for l in open(out, errors="replace").read().splitlines() if l.strip()][-1:]
    verdict = "error (exit %s): %s" % (code, clean(tail[0])[:200] if tail else "no output")
    row = [cycle, now, verdict] + ["-"] * 10 + [""]
    subject, body = f"optimize round {cycle}: {verdict[:60]}", ""
else:
    a = j["attempts"][-1]
    before, after = j["baseline_ns"], j["current_ns"]
    first = first or before / 1e6
    total = f"{first / (after / 1e6):.2f}x"
    cost = "-" if a["cost_usd"] is None else ("~" if a["cost_is_estimate"] else "") + f"{a['cost_usd']:.2f}"
    wall = f"{a['elapsed_secs'] // 60}m{a['elapsed_secs'] % 60:02d}s"
    row = [cycle, now, a["verdict"], ms(before), ms(a["ns"]), ms(after), total, cost, a["tokens_in"], a["tokens_out"], wall, a["job"], pts(a.get("points")), clean(a["summary"])]
    if a["verdict"].startswith("accepted"):
        subject = f"optimize round {cycle}: {ms(before)} ms -> {ms(after)} ms, {a['verdict']}"
    else:
        subject = f"optimize round {cycle}: {a['verdict']}, still {ms(after)} ms"
    body = (f"Workload: {ms(first * 1e6)} ms before the first round, {ms(after)} ms now ({total}), summed over the levels.\n"
            f"Agent: {a['job']}, {wall}, cost {cost} USD.\n"
            f"Points measured (level:bytes/ms): {pts(a.get('points'))}\n"
            f"Points now: {pts(j.get('current_points'))}\n\nThe agent's summary:\n{a['summary'].strip()}\n")
with open(log, "a") as f:
    f.write("\t".join(str(x) for x in row) + "\n")
print(subject)
print()
print(body)
EOF
}

errors=0
force="${FORCE_AGENT:-}"
[ -z "$force" ] && [ -f "$FORCEFILE" ] && force="$(cat "$FORCEFILE")"
while :; do
    if [ -e "$STOP" ]; then
        echo "== optimize-loop: stop requested, leaving"
        break
    fi
    cycle=$(($(wc -l < "$LOG")))
    started=$(date +%s)
    out="$OUT/round-$cycle.out"
    agent="${force:-$(next_agent)}"
    force=""
    rm -f "$FORCEFILE"
    if [ "$agent" = claude ]; then
        if tok="$(pick_token)"; then
            CLAUDE_CODE_OAUTH_TOKEN="$(cat "$tok")"
            export CLAUDE_CODE_OAUTH_TOKEN
            echo "$tok" > "$TOKSTATE"
            echo "== optimize-loop: Claude token from $(basename "$tok")"
        else
            unset CLAUDE_CODE_OAUTH_TOKEN
            echo "== optimize-loop: no token files found; Claude uses its logged-in credentials"
        fi
    else
        unset CLAUDE_CODE_OAUTH_TOKEN
    fi
    echo "== optimize-loop: $TARGET round $cycle starts $(date -u '+%Y-%m-%d %H:%M:%S') UTC with $agent (DJINN_BENCH_SCALE=$DJINN_BENCH_SCALE)"
    args=(optimize --cycles 1 --agent "$agent" --jobs "${BENCH_JOBS-1}" --min-time "${MIN_TIME:-30}" "${THRESHOLD[@]}" "$@")
    [ "$agent" = codex ] && [ -n "$CODEX_EFFORT" ] && args+=(--effort "$CODEX_EFFORT")
    hist="$(history "$agent")"
    [ -n "$hist" ] && args+=(--prompt "$hist")
    cargo djinn "${args[@]}" 2>&1 | tee "$out"
    code=${PIPESTATUS[0]}

    if [ "$agent" = claude ] && grep -q "agent exited; tokens in [1-9]" "$out"; then : > "$EXHAUSTED"; fi
    record "$cycle" "$started" "$code" "$out" | head -n 1 | sed 's/^/== optimize-loop: /'

    verdict="$(tail -n 1 "$LOG" | cut -f3)"
    case "$verdict" in
    error*)
        errors=$((errors + 1))
        if [ "$errors" -ge 3 ]; then
            echo "== optimize-loop: three rounds in a row failed before an attempt; leaving"
            exit 1
        fi
        sleep 600
        ;;
    accepted*) errors=0 ;;
    interrupted*)
        echo "== optimize-loop: the round was interrupted; leaving"
        break
        ;;
    *)
        errors=0
        if [ "$agent" = claude ] && grep -qiE "hit your .*limit|reached your .*limit|out of usage credits|usage limit" "$out"; then
            # the token is exhausted: the next round is Claude again, with another token, at once
            echo "== optimize-loop: the Claude token of round $cycle is exhausted; retrying with another token"
            [ -f "$TOKSTATE" ] && cat "$TOKSTATE" >> "$EXHAUSTED"
            if grep -qi "out of usage credits" "$out" && [ -f "$TOKSTATE" ]; then cat "$TOKSTATE" >> "$BLOCKED"; fi
            force=claude
            echo claude > "$FORCEFILE"
        else
            # an agent that gives up within two minutes has most likely hit a usage limit: wait before the next
            wall="$(tail -n 1 "$LOG" | cut -f11)"
            case "$wall" in
            0m* | 1m*)
                if [ ! -e "$STOP" ]; then
                    echo "== optimize-loop: the agent of round $cycle stopped after $wall without a gain; waiting 30 minutes"
                    sleep 1800
                fi
                ;;
            esac
        fi
        ;;
    esac
done
