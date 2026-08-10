#!/usr/bin/env bash
#
# Evaluates ShotTx on the structured set of higher-order problems
# (ShotTx.Benchmark.HolSuite, extracted from
# examples/structured_hol_problems.livemd) and writes one CSV row per problem.
#
# One fresh BEAM per problem. This is not merely for timing hygiene: ShotTx
# carries shared state across proof sessions, and a crashed or killed session
# changes the answer for later problems in the same node. See the moduledoc of
# ShotTx.Benchmark.HolRunner.
#
# Usage:
#   scripts/run_hol_benchmark.sh [OUTPUT_CSV]
#
# Environment variables:
#   TIMEOUT_MS   Per-problem prover timeout in ms (default: prover default).
#
# Resumable: problems already present in OUTPUT_CSV are skipped, so an
# interrupted sweep continues where it stopped. Delete the CSV to start over.
#
# Pause a live run:
#   touch <dirname OUTPUT_CSV>/STOP     # graceful, waits for current problem

set -euo pipefail

OUTPUT="${1:-bench_results/hol_suite.csv}"
OUTPUT_DIR="$(dirname "$OUTPUT")"
STOP_FILE="$OUTPUT_DIR/STOP"

mkdir -p "$OUTPUT_DIR"

# Compile once up front so no per-problem invocation pays for it (and so a
# compile error fails fast rather than 130 times).
mix compile

if [ ! -s "$OUTPUT" ]; then
    mix run scripts/hol_problem.exs --header > "$OUTPUT"
fi

IDS=$(mix run scripts/hol_problem.exs --list)
TOTAL=$(echo "$IDS" | wc -l)
INDEX=0

echo "=================================================================="
echo "ShotTx structured HOL suite"
echo "  output   = $OUTPUT"
echo "  problems = $TOTAL"
echo "  timeout  = ${TIMEOUT_MS:-prover default} ms"
echo "=================================================================="

for ID in $IDS; do
    INDEX=$((INDEX + 1))

    if [ -f "$STOP_FILE" ]; then
        echo "STOP sentinel at $STOP_FILE — halting. Delete it and re-run to resume."
        exit 0
    fi

    # Resume: the id is the first CSV field.
    if cut -d, -f1 "$OUTPUT" | grep -qx "$ID"; then
        echo "[$INDEX/$TOTAL] $ID (already recorded)"
        continue
    fi

    # `grep` guards against anything the BEAM prints on stdout besides the row.
    ROW=$(mix run scripts/hol_problem.exs "$ID" ${TIMEOUT_MS:+"$TIMEOUT_MS"} 2>/dev/null \
          | grep -m1 "^$ID,") || {
        echo "[$INDEX/$TOTAL] $ID — no row produced, recording as harness_error"
        ROW="$ID,,,,harness_error,0,,,,,,,,runner produced no row"
    }

    printf '%s\n' "$ROW" >> "$OUTPUT"
    echo "[$INDEX/$TOTAL] $(echo "$ROW" | cut -d, -f1,5,6 | tr ',' ' ')"
done

echo "=================================================================="
echo "Done. $TOTAL problems in $OUTPUT"
echo "=================================================================="
