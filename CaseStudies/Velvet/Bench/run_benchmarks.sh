#!/usr/bin/env bash
# Run hyperfine benchmarks for all Dafny/Lean/Lean-async file triplets.
#
# Usage: ./run_benchmarks.sh [--runs N] [--warmup W]
#   --runs    Number of timed runs (default: 10)
#   --warmup  Number of warmup runs (default: 1)
#
# Must be run from anywhere; it resolves paths relative to the script location.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
RESULTS_DIR="$SCRIPT_DIR/results"
FOLDERS=("both_easy" "needs_proofs" "needs_refactoring")

RUNS=10
WARMUP=1

# Parse arguments
while [[ $# -gt 0 ]]; do
    case "$1" in
        --runs)  RUNS="$2"; shift 2 ;;
        --warmup) WARMUP="$2"; shift 2 ;;
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
echo ""

# Helper: convert file path to Lean module name (relative to project root)
# e.g., CaseStudies/Velvet/Bench/both_easy/foo.lean -> CaseStudies.Velvet.Bench.both_easy.foo
file_to_module() {
    local file="$1"
    local rel
    rel="$(realpath --relative-to="$PROJECT_ROOT" "$file")"
    echo "${rel%.lean}" | tr '/' '.'
}

for folder in "${FOLDERS[@]}"; do
    dir="$SCRIPT_DIR/$folder"
    [ -d "$dir" ] || { echo "Skipping missing folder: $folder"; continue; }

    out_dir="$RESULTS_DIR/$folder"
    mkdir -p "$out_dir"

    echo "=== Folder: $folder ==="

    for dfy_file in "$dir"/*.dfy; do
        [ -f "$dfy_file" ] || continue

        base="$(basename "$dfy_file" .dfy)"
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

        lean_module="$(file_to_module "$lean_file")"
        async_module="$(file_to_module "$async_file")"
        json_out="$out_dir/${base}.json"

        echo "  Benchmarking: $base"

        hyperfine \
            --runs "$RUNS" \
            --warmup "$WARMUP" \
            --export-json "$json_out" \
            --prepare "touch '$lean_file'" \
            --prepare "touch '$async_file'" \
            --command-name "dafny"      "dafny verify '$dfy_file'" \
            --command-name "lean"       "lake build '$lean_module'" \
            --command-name "lean_async" "lake build '$async_module'" \
            2>&1 | sed 's/^/    /'

        echo ""
    done
done

echo "Results written to: $RESULTS_DIR"
