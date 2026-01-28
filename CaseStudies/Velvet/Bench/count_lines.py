#!/usr/bin/env python3
"""
Script to count code lines and proof lines in Lean files.

Code lines: Lines from 'method' to the first same-indented line, excluding blank lines and invariants.
Proof lines: Non-code lines excluding blank lines, imports, sections, ends, set_options, comments, plus invariant count.
"""

import os
import re
from pathlib import Path
from collections import defaultdict

def get_indentation(line):
    """Get the indentation level (number of leading spaces) of a line."""
    return len(line) - len(line.lstrip())

def is_blank_line(line):
    """Check if a line is blank or only whitespace."""
    return line.strip() == ""

def is_comment_line(line, multiline_comment_lines=None, line_idx=None):
    """Check if a line is a comment (starts with -- or is part of /- -/)."""
    stripped = line.strip()
    is_single_comment = stripped.startswith("--")
    is_multiline_comment = (multiline_comment_lines is not None and
                           line_idx is not None and
                           line_idx in multiline_comment_lines)
    return is_single_comment or is_multiline_comment

def should_exclude_from_proof(line, multiline_comment_lines=None, line_idx=None):
    """Check if a line should be excluded from proof count."""
    stripped = line.strip()
    return (is_blank_line(line) or
            stripped.startswith("import ") or
            stripped.startswith("section ") or
            stripped.startswith("end ") or
            stripped.startswith("set_option ") or
            is_comment_line(line, multiline_comment_lines, line_idx))

def is_spec_line(line):
    """Check if a line is a specification line (require, ensures, done_with)."""
    stripped = line.strip()
    return (stripped.startswith("require ") or
            stripped.startswith("ensures ") or
            stripped.startswith("done_with "))

def count_lines_in_file(filepath):
    """Count code lines and proof lines in a single file."""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            lines = f.readlines()
    except Exception as e:
        print(f"Error reading {filepath}: {e}")
        return None, None, None

    total_lines = len(lines)
    code_segments = []
    invariant_count = 0

    # Mark lines that are inside multi-line comments
    in_multiline_comment = False
    multiline_comment_lines = set()

    for i, line in enumerate(lines):
        stripped = line.strip()

        if "/-" in stripped:
            in_multiline_comment = True
            multiline_comment_lines.add(i)
        elif "-/" in stripped:
            multiline_comment_lines.add(i)
            in_multiline_comment = False
        elif in_multiline_comment:
            multiline_comment_lines.add(i)

    # Mark lines that are inside spec blocks (requires, ensures, done_with)
    spec_lines = set()

    for i, line in enumerate(lines):
        stripped = line.strip()

        # Check if this line starts a spec block
        if (stripped.startswith("require ") or
            stripped.startswith("ensures ") or
            stripped.startswith("done_with ")):

            # Find the indentation level
            spec_indent = get_indentation(line)
            spec_lines.add(i)

            # Look ahead to find continuation lines
            j = i + 1
            while j < len(lines):
                next_line = lines[j]
                if is_blank_line(next_line):
                    j += 1
                    continue

                next_indent = get_indentation(next_line)
                next_stripped = next_line.strip()

                # If we hit a 'do' at the same or less indentation, we've reached the end of spec
                if (next_stripped.startswith("do") and next_indent <= spec_indent):
                    break

                # If indentation is same as spec (pattern match continuation) or greater (nested content), it's part of spec
                if (next_indent >= spec_indent and
                    not next_stripped.startswith("method ") and
                    not next_stripped.startswith("if ") and
                    not next_stripped.startswith("let ") and
                    not next_stripped.startswith("while ") and
                    not next_stripped.startswith("return ")):
                    spec_lines.add(j)
                    j += 1
                # If we hit same or less indentation and it's not part of the spec structure, we're done
                elif next_indent < spec_indent:
                    break
                else:
                    j += 1

    # Find all method blocks
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        if stripped.startswith("method "):
            method_indent = get_indentation(line)
            method_start = i
            j = i + 1

            # Find the end of the method block (first line with same indentation as method)
            while j < len(lines):
                if not is_blank_line(lines[j]) and get_indentation(lines[j]) <= method_indent:
                    break
                j += 1

            code_segments.append((method_start, j))
            i = j
        else:
            i += 1

    # Count code lines, invariants, and spec lines
    code_lines = 0
    code_segment_lines = set()
    spec_lines_in_code = 0

    for start, end in code_segments:
        for line_idx in range(start, end):
            code_segment_lines.add(line_idx)
            line = lines[line_idx]
            if not is_blank_line(line) and not is_comment_line(line, multiline_comment_lines, line_idx):
                if line_idx in spec_lines:
                    spec_lines_in_code += 1
                else:
                    code_lines += 1
            if line.strip().startswith("invariant "):
                invariant_count += 1

    # Subtract invariants from code lines
    code_lines -= invariant_count

    # Count proof lines
    proof_lines = 0
    for i, line in enumerate(lines):
        if i not in code_segment_lines and not should_exclude_from_proof(line, multiline_comment_lines, i):
            proof_lines += 1

    # Add invariants and spec lines from code segments to proof lines
    proof_lines += invariant_count + spec_lines_in_code

    return code_lines, proof_lines, {
        'total_lines': total_lines,
        'code_segments': len(code_segments),
        'invariant_count': invariant_count,
        'spec_lines_in_code': spec_lines_in_code,
        'code_segment_lines': len(code_segment_lines)
    }

def scan_directory(directory):
    """Scan directory for .lean files and count lines."""
    results = []

    for root, dirs, files in os.walk(directory):
        for file in files:
            if file.endswith('.lean'):
                filepath = os.path.join(root, file)
                code_lines, proof_lines, details = count_lines_in_file(filepath)

                if code_lines is not None:
                    rel_path = os.path.relpath(filepath, directory)
                    results.append({
                        'file': rel_path,
                        'code_lines': code_lines,
                        'proof_lines': proof_lines,
                        'details': details
                    })

    return results

def print_results(results):
    """Print the results in a formatted way."""
    total_code = 0
    total_proof = 0

    print(f"{'File':<50} {'Code Lines':<12} {'Proof Lines':<12} {'Total':<8}")
    print("=" * 90)

    for result in sorted(results, key=lambda x: x['file']):
        file = result['file']
        code = result['code_lines']
        proof = result['proof_lines']
        total = code + proof

        total_code += code
        total_proof += proof

        print(f"{file:<50} {code:<12} {proof:<12} {total:<8}")

        # Print details if verbose
        details = result['details']
        print(f"  └─ Methods: {details['code_segments']}, Invariants: {details['invariant_count']}, Specs: {details['spec_lines_in_code']}, Total lines: {details['total_lines']}")

    print("=" * 90)
    print(f"{'TOTAL':<50} {total_code:<12} {total_proof:<12} {total_code + total_proof:<8}")
    print()
    print("Code lines: Lines in method blocks (excluding blank lines, comments, invariants, require/ensures/done_with)")
    print("Proof lines: Non-method lines (excluding blank, import, section, end, set_option, comments) + invariants + require/ensures/done_with")

def main():
    import argparse

    parser = argparse.ArgumentParser(description='Count code and proof lines in Lean files')
    parser.add_argument('directory', nargs='?', default='.',
                       help='Directory to scan (default: current directory)')

    args = parser.parse_args()

    if not os.path.exists(args.directory):
        print(f"Error: Directory '{args.directory}' does not exist")
        return 1

    results = scan_directory(args.directory)

    if not results:
        print(f"No .lean files found in '{args.directory}'")
        return 0

    print_results(results)
    return 0

if __name__ == "__main__":
    exit(main())