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
#   BASE_TIMEOUT     Optional. Base per-problem timeout in ms (default: 5000).
#   LANGUAGE         Optional. th0 | th1 | both (default: both).
#
# Pause a live run:
#   touch <OUTPUT_DIR>/STOP     # graceful, waits for current problem
#   # or Ctrl-C twice to force-kill (current problem is lost, resume rescans)
#
# Resume:
#   rm <OUTPUT_DIR>/STOP && scripts/run_ablation.sh <OUTPUT_DIR>

set -euo pipefail

OUTPUT_DIR="${1:-bench_results/$(date +%Y-%m-%d_%H%M%S)}"
BASE_TIMEOUT="${BASE_TIMEOUT:-5000}"
LANGUAGE="${LANGUAGE:-both}"

if [ -z "${TPTP_ROOT:-}" ]; then
    echo "ERROR: TPTP_ROOT environment variable is not set." >&2
    exit 1
fi

mkdir -p "$OUTPUT_DIR"

echo "=================================================================="
echo "ShotTx ablation sweep"
echo "  output_dir    = $OUTPUT_DIR"
echo "  base_timeout  = ${BASE_TIMEOUT}ms"
echo "  language      = $LANGUAGE"
echo "  tptp_root     = $TPTP_ROOT"
echo "=================================================================="

# Enumerate config labels once by asking the Ablation module.
LABELS=$(mix run --no-start -e "
  ShotTx.Benchmark.Ablation.matrix(base_timeout: $BASE_TIMEOUT)
  |> Enum.each(fn {label, _} -> IO.puts(label) end)
" 2>/dev/null)

if [ -z "$LABELS" ]; then
    echo "ERROR: Ablation.matrix/1 returned no configurations." >&2
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
    echo "[$INDEX/$TOTAL] Config: $LABEL"
    echo "  writing -> $CSV_PATH"
    echo "------------------------------------------------------------------"

    mix run -e "
      configs = ShotTx.Benchmark.Ablation.matrix(base_timeout: $BASE_TIMEOUT)
      {_, params} = Enum.find(configs, fn {l, _} -> l == \"$LABEL\" end)
      result = ShotTx.Benchmark.TptpRunner.run_tptp(params,
        label: \"$LABEL\",
        output_dir: \"$OUTPUT_DIR\",
        language: :$LANGUAGE
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
echo "Sweep complete. $TOTAL configurations in $OUTPUT_DIR/"
echo "=================================================================="
