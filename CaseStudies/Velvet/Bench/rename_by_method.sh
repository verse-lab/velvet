#!/usr/bin/env bash
# Rename benchmark files based on the method name inside each .lean file.
#
# For each .lean file (excluding _async), extracts the method name from
# `method <name>` in the Impl section, then renames:
#   foo.lean       -> <name>.lean
#   foo.dfy        -> <name>.dfy
#   foo_async.lean -> <name>_async.lean
#
# Usage: ./rename_by_method.sh [--dry-run]

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FOLDERS=("both_easy" "needs_proofs" "needs_refactoring")
DRY_RUN=false

[[ "${1:-}" == "--dry-run" ]] && DRY_RUN=true

for folder in "${FOLDERS[@]}"; do
    dir="$SCRIPT_DIR/$folder"
    [ -d "$dir" ] || continue

    echo "=== $folder ==="

    for lean_file in "$dir"/*.lean; do
        [ -f "$lean_file" ] || continue
        base="$(basename "$lean_file" .lean)"

        # Skip _async files
        [[ "$base" == *_async ]] && continue

        # Extract method name: first occurrence of `method <name>`
        method_name=$(grep -m1 -oP '(?<=^method )\w+' "$lean_file" || true)

        if [ -z "$method_name" ]; then
            echo "  SKIP $base: no 'method <name>' found"
            continue
        fi

        # Skip if already named correctly
        if [ "$base" = "$method_name" ]; then
            echo "  OK   $base (already named)"
            continue
        fi

        dfy_file="$dir/${base}.dfy"
        async_file="$dir/${base}_async.lean"

        echo "  $base -> $method_name"

        if [ "$DRY_RUN" = true ]; then
            echo "    [dry-run] mv $lean_file -> $dir/${method_name}.lean"
            [ -f "$dfy_file" ]   && echo "    [dry-run] mv $dfy_file -> $dir/${method_name}.dfy"
            [ -f "$async_file" ] && echo "    [dry-run] mv $async_file -> $dir/${method_name}_async.lean"
        else
            mv "$lean_file" "$dir/${method_name}.lean"
            [ -f "$dfy_file" ]   && mv "$dfy_file" "$dir/${method_name}.dfy"
            [ -f "$async_file" ] && mv "$async_file" "$dir/${method_name}_async.lean"
        fi
    done

    echo ""
done
