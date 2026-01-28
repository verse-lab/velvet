#!/usr/bin/env bash
# Run hyperfine benchmarks for all Dafny/Lean/Lean-async file triplets.
#
# Usage: ./run_benchmarks.sh [--runs N] [--warmup W] [--prefix P]
#   --runs    Number of timed runs (default: 10)
#   --warmup  Number of warmup runs (default: 1)
#   --prefix  Only run benchmarks whose name starts with P (default: all)
#
# Must be run from anywhere; it resolves paths relative to the script location.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$SCRIPT_DIR/../../.."
RESULTS_DIR="$SCRIPT_DIR/results"
FOLDERS=("both_easy" "needs_proofs" "needs_refactoring")

RUNS=10
WARMUP=1
PREFIX=""

# Parse arguments
while [[ $# -gt 0 ]]; do
    case "$1" in
        --runs)   RUNS="$2"; shift 2 ;;
        --warmup) WARMUP="$2"; shift 2 ;;
        --prefix) PREFIX="$2"; shift 2 ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

# Check prerequisites
command -v hyperfine >/dev/null 2>&1 || { echo "Error: hyperfine not found"; exit 1; }
command -v dafny >/dev/null 2>&1    || { echo "Error: dafny not found"; exit 1; }
command -v lake >/dev/null 2>&1     || { echo "Error: lake not found"; exit 1; }

echo "Benchmark configuration:"
echo "  Project root: $PROJECT_ROOT"
echo "  Runs: $RUNS"
echo "  Warmup: $WARMUP"
echo "  Prefix: ${PREFIX:-<all>}"
echo ""

for folder in "${FOLDERS[@]}"; do
    dir="$SCRIPT_DIR/$folder"
    [ -d "$dir" ] || { echo "Skipping missing folder: $folder"; continue; }

    out_dir="$RESULTS_DIR/$folder"
    mkdir -p "$out_dir"

    echo "=== Folder: $folder ==="

    for dfy_file in "$dir"/*.dfy; do
        [ -f "$dfy_file" ] || continue

        base="$(basename "$dfy_file" .dfy)"

        # Skip if prefix is set and doesn't match
        if [[ -n "$PREFIX" && "$base" != "$PREFIX"* ]]; then
            continue
        fi

        lean_file="$dir/${base}.lean"
        async_file="$dir/${base}_async.lean"

        # Check that all three files exist
        if [ ! -f "$lean_file" ]; then
            echo "  SKIP $base: missing $lean_file"
            continue
        fi
        if [ ! -f "$async_file" ]; then
            echo "  SKIP $base: missing $async_file (run generate_async.sh first)"
            continue
        fi

        json_out="$out_dir/${base}.json"

        echo "  Benchmarking: $base"

        hyperfine \
            --runs "$RUNS" \
            --warmup "$WARMUP" \
            --export-json "$json_out" \
            --command-name "dafny"      "dafny verify ${dfy_file}" \
            --command-name "lean"       "cd ${PROJECT_ROOT} && lake env lean ${lean_file}" \
            --command-name "lean_async" "cd ${PROJECT_ROOT} && lake env lean ${async_file}" \
            2>&1 | sed 's/^/    /'

        echo ""
    done
done

echo "Results written to: $RESULTS_DIR"
