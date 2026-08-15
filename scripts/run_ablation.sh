#!/usr/bin/env bash
#
# Runs the ShotTx ablation matrix against the TPTP TH0/TH1 corpus.
#
# One fresh BEAM node per configuration for timing isolation. Results are
# written as per-config CSVs under $OUTPUT_DIR. The runner is resumable and
# pausable: interrupted runs pick up where they left off on the next invocation,
# and a `STOP` sentinel file in $OUTPUT_DIR halts the sweep at the next
# problem boundary.
#
# Usage:
#   scripts/run_ablation.sh [OUTPUT_DIR]
#
# Environment variables:
#   TPTP_ROOT        Required. Path to the TPTP directory containing Problems/.
#   BASE_TIMEOUT     Optional. Per-problem timeout in ms (default: 2000). Applied
#                    uniformly to every configuration — the matrix does not sweep
#                    the timeout, so that solved-count differences between rows
#                    reflect the ablated component and not a differing budget.
#   LANGUAGE         Optional. th0 | th1 | both (default: both).
#   PROBLEM_LIMIT    Optional. Max problems per configuration (default: all).
#   PARSE_TIMEOUT    Optional. Wall-clock budget in ms for parsing one problem
#                    (default: 60000). Problems whose includes keep the parser
#                    busy past this are killed and recorded as `parse_timeout`.
#                    Timed-out and failed parses are both appended to
#                    $OUTPUT_DIR/parse_cache and replayed from there by the
#                    remaining configurations — the parser's verdict does not
#                    depend on the prover parameters, so each is paid once per
#                    sweep rather than once per configuration.
#   PROVE_GRACE      Optional. Slack in ms added to BASE_TIMEOUT to obtain the
#                    hard wall-clock budget for a proof attempt (default: 10000).
#                    A prover that overruns its own cooperative timeout is killed
#                    and recorded as `hard_timeout`.
#
# Validate the corpus cheaply before committing to the full multi-day sweep —
# a parser-version mismatch shows up as `parser_error` in every row:
#
#   PROBLEM_LIMIT=20 scripts/run_ablation.sh smoke_results
#   grep -c parser_error smoke_results/baseline.csv
#
# Note that PROBLEM_LIMIT interacts with resume: the limit counts problems
# processed in *this* invocation, so re-running with the same OUTPUT_DIR
# advances through the corpus another PROBLEM_LIMIT problems.
#
# Pause a live run:
#   touch <OUTPUT_DIR>/STOP     # graceful, waits for current problem
#   # or Ctrl-C twice to force-kill (current problem is lost, resume rescans)
#
# Resume:
#   rm <OUTPUT_DIR>/STOP && scripts/run_ablation.sh <OUTPUT_DIR>

set -euo pipefail

OUTPUT_DIR="${1:-bench_results/$(date +%Y-%m-%d_%H%M%S)}"
BASE_TIMEOUT="${BASE_TIMEOUT:-2000}"
LANGUAGE="${LANGUAGE:-both}"
PARSE_TIMEOUT="${PARSE_TIMEOUT:-60000}"
PROVE_GRACE="${PROVE_GRACE:-10000}"

# Prefixes a line with the local wall-clock time, so a multi-day sweep's log
# says when each configuration started and finished, not just how long it took.
stamp() { date '+[%m-%d %H:%M:%S]'; }

# Rendered straight into the `mix run -e` snippet, so it must be a valid Elixir
# literal: an integer when set, `nil` (TptpRunner's "no limit") when not.
PROBLEM_LIMIT_LITERAL="${PROBLEM_LIMIT:-nil}"

if [ -z "${TPTP_ROOT:-}" ]; then
    echo "ERROR: TPTP_ROOT environment variable is not set." >&2
    exit 1
fi

# TPTP_ROOT being set proves nothing: the devcontainer exports it unconditionally,
# so a container started without the corpus bind-mount still passes the check
# above and then silently produces empty result directories. Insist on the
# directory the runner actually globs.
if [ ! -d "$TPTP_ROOT/Problems" ]; then
    echo "ERROR: no TPTP corpus at $TPTP_ROOT (expected a Problems/ subdirectory)." >&2
    echo "       TPTP_ROOT is set but the corpus is not mounted there — most likely" >&2
    echo "       this container was not started from the elixir-isabelle profile." >&2
    exit 1
fi

if [ "$PROBLEM_LIMIT_LITERAL" != "nil" ] && ! [[ "$PROBLEM_LIMIT_LITERAL" =~ ^[1-9][0-9]*$ ]]; then
    echo "ERROR: PROBLEM_LIMIT must be a positive integer, got '$PROBLEM_LIMIT'." >&2
    exit 1
fi

mkdir -p "$OUTPUT_DIR"

echo "=================================================================="
echo "ShotTx ablation sweep"
echo "  started       = $(date '+%Y-%m-%d %H:%M:%S %Z')"
echo "  output_dir    = $OUTPUT_DIR"
echo "  base_timeout  = ${BASE_TIMEOUT}ms"
echo "  parse_timeout = ${PARSE_TIMEOUT}ms"
echo "  prove_grace   = ${PROVE_GRACE}ms"
echo "  language      = $LANGUAGE"
echo "  problem_limit = $PROBLEM_LIMIT_LITERAL"
echo "  tptp_root     = $TPTP_ROOT"
echo "=================================================================="

# Compile up front. `mix run` would otherwise emit "Compiling N files" on stdout
# during label enumeration below and those lines would be captured as labels.
echo ""
echo "Compiling..."
mix compile

# Enumerate config labels once by asking the Ablation module. Errors are left on
# stderr deliberately: swallowing them turns a compile failure or a renamed
# module into a bare "returned no configurations" with no clue as to why.
LABELS=$(mix run --no-start -e "
  ShotTx.Benchmark.Ablation.matrix(base_timeout: $BASE_TIMEOUT)
  |> Enum.each(fn {label, _} -> IO.puts(label) end)
")

if [ -z "$LABELS" ]; then
    echo "ERROR: Ablation.matrix/1 returned no configurations (see errors above)." >&2
    exit 1
fi

TOTAL=$(echo "$LABELS" | wc -l)
INDEX=0

for LABEL in $LABELS; do
    INDEX=$((INDEX + 1))

    if [ -f "$OUTPUT_DIR/STOP" ]; then
        echo ""
        echo "STOP sentinel present at $OUTPUT_DIR/STOP — halting sweep."
        echo "Delete the sentinel and re-run to resume."
        exit 0
    fi

    CSV_PATH="$OUTPUT_DIR/$LABEL.csv"

    echo ""
    echo "------------------------------------------------------------------"
    echo "$(stamp) [$INDEX/$TOTAL] Config: $LABEL"
    echo "  writing -> $CSV_PATH"
    echo "------------------------------------------------------------------"

    mix run -e "
      configs = ShotTx.Benchmark.Ablation.matrix(base_timeout: $BASE_TIMEOUT)
      {_, params} = Enum.find(configs, fn {l, _} -> l == \"$LABEL\" end)
      result = ShotTx.Benchmark.TptpRunner.run_tptp(params,
        label: \"$LABEL\",
        output_dir: \"$OUTPUT_DIR\",
        language: :$LANGUAGE,
        problem_limit: $PROBLEM_LIMIT_LITERAL,
        parse_timeout: $PARSE_TIMEOUT,
        prove_grace: $PROVE_GRACE
      )
      if result == :stopped, do: System.halt(2), else: System.halt(0)
    " || {
        # Exit code 2 signals STOP-sentinel-halt from the runner.
        if [ $? -eq 2 ]; then
            echo "Runner reported :stopped, exiting sweep."
            exit 0
        else
            echo "WARNING: config $LABEL exited abnormally. Continuing."
        fi
    }
done

echo ""
echo "=================================================================="
echo "$(stamp) Sweep complete. $TOTAL configurations in $OUTPUT_DIR/"
if [ -f "$OUTPUT_DIR/parse_cache" ]; then
    echo "  $(wc -l < "$OUTPUT_DIR/parse_cache") problem(s) unparsable; see $OUTPUT_DIR/parse_cache"
fi
echo "=================================================================="
