#!/usr/bin/env bash
# Generate _async.lean copies of all .lean benchmark files.
# Replaces `loom_solve` with `loom_solve_async` in each copy.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FOLDERS=("both_easy" "needs_proofs" "needs_refactoring")

count=0

for folder in "${FOLDERS[@]}"; do
    dir="$SCRIPT_DIR/$folder"
    [ -d "$dir" ] || continue

    for lean_file in "$dir"/*.lean; do
        [ -f "$lean_file" ] || continue

        base="$(basename "$lean_file" .lean)"
        # Skip files that are already _async variants
        [[ "$base" == *_async ]] && continue

        async_file="$dir/${base}_async.lean"
        sed 's/loom_solve/loom_solve_async/g' "$lean_file" > "$async_file"
        count=$((count + 1))
    done
done

echo "Generated $count _async.lean files."
