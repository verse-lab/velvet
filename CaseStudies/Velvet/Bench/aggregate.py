#!/usr/bin/env python3
"""
Aggregate hyperfine benchmark results and produce CSV, console table, and bar chart PNGs.

Usage:
    python aggregate.py [--results-dir DIR] [--output-dir DIR]
"""

import argparse
import csv
import json
import re
import sys
from pathlib import Path
from typing import Dict, List, Tuple

try:
    import matplotlib.pyplot as plt
    import numpy as np
    HAS_MATPLOTLIB = True
except ImportError:
    HAS_MATPLOTLIB = False
    print("Warning: matplotlib/numpy not available; skipping chart generation.")

SCRIPT_DIR = Path(__file__).parent.resolve()
DEFAULT_RESULTS_DIR = SCRIPT_DIR / "results"


# ── Data loading ─────────────────────────────────────────────────────────────

def load_hyperfine_json(path: Path) -> Dict[str, dict]:
    """Load a hyperfine JSON file and return {command_name: stats_dict}."""
    with open(path) as f:
        data = json.load(f)
    return {r["command"]: r for r in data["results"]}


def natural_sort_key(name: str) -> Tuple:
    """Sort key that handles embedded numbers naturally."""
    parts = re.split(r'(\d+)', name)
    return tuple(int(p) if p.isdigit() else p.lower() for p in parts)


def shorten_name(name: str) -> str:
    name = name.replace("_impl", "")
    name = name.replace("verina_basic_", "b")
    name = name.replace("verina_advanced_", "a")
    return name


# ── Console table ────────────────────────────────────────────────────────────

def print_table(rows: List[dict], folder: str) -> None:
    """Print a formatted console table for one folder."""
    if not rows:
        return

    header = f"{'Program':<30} {'Dafny (s)':>12} {'Lean (s)':>12} {'Async (s)':>12} {'Lean/Dafny':>12} {'Async/Dafny':>12}"
    sep = "-" * len(header)

    print(f"\n{folder}")
    print(sep)
    print(header)
    print(sep)

    for r in rows:
        ratio_lean = r["lean_mean"] / r["dafny_mean"] if r["dafny_mean"] > 0 else float("inf")
        ratio_async = r["async_mean"] / r["dafny_mean"] if r["dafny_mean"] > 0 else float("inf")
        print(
            f"{r['program']:<30} "
            f"{r['dafny_mean']:>10.3f}s "
            f"{r['lean_mean']:>10.3f}s "
            f"{r['async_mean']:>10.3f}s "
            f"{ratio_lean:>11.2f}x "
            f"{ratio_async:>11.2f}x"
        )

    print(sep)

    # Totals
    total_d = sum(r["dafny_mean"] for r in rows)
    total_l = sum(r["lean_mean"] for r in rows)
    total_a = sum(r["async_mean"] for r in rows)
    ratio_l = total_l / total_d if total_d > 0 else float("inf")
    ratio_a = total_a / total_d if total_d > 0 else float("inf")
    print(
        f"{'TOTAL':<30} "
        f"{total_d:>10.3f}s "
        f"{total_l:>10.3f}s "
        f"{total_a:>10.3f}s "
        f"{ratio_l:>11.2f}x "
        f"{ratio_a:>11.2f}x"
    )
    print()


# ── CSV output ───────────────────────────────────────────────────────────────

CSV_FIELDS = [
    "folder", "program",
    "dafny_mean", "dafny_stddev", "dafny_min", "dafny_max",
    "lean_mean", "lean_stddev", "lean_min", "lean_max",
    "async_mean", "async_stddev", "async_min", "async_max",
]


def write_csv(all_rows: List[dict], output_path: Path) -> None:
    with open(output_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=CSV_FIELDS, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(all_rows)
    print(f"CSV written to: {output_path}")


# ── Bar chart ────────────────────────────────────────────────────────────────

def create_bar_chart(rows: List[dict], folder: str, output_path: Path) -> None:
    if not HAS_MATPLOTLIB or not rows:
        return

    names = [shorten_name(r["program"]) for r in rows]
    dafny = [r["dafny_mean"] for r in rows]
    lean = [r["lean_mean"] for r in rows]
    async_ = [r["async_mean"] for r in rows]

    x = np.arange(len(names))
    width = 0.25

    fig, ax = plt.subplots(figsize=(max(10, len(names) * 0.8), 6))

    ax.bar(x - width, dafny, width, label="Dafny", color="#3498db", edgecolor="black", linewidth=0.5)
    ax.bar(x, lean, width, label="Lean (sync)", color="#e67e22", edgecolor="black", linewidth=0.5)
    ax.bar(x + width, async_, width, label="Lean (async)", color="#2ecc71", edgecolor="black", linewidth=0.5)

    ax.set_xlabel("Program", fontsize=12)
    ax.set_ylabel("Verification Time (s)", fontsize=12)
    ax.set_title(f"Verification Time: {folder.replace('_', ' ').title()}", fontsize=14, fontweight="bold")
    ax.set_xticks(x)
    ax.set_xticklabels(names, rotation=45, ha="right", fontsize=9)
    ax.legend(loc="upper right", fontsize=10)
    ax.yaxis.grid(True, linestyle="--", alpha=0.7)
    ax.set_axisbelow(True)

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches="tight")
    plt.close(fig)
    print(f"Chart saved: {output_path}")


# ── Main ─────────────────────────────────────────────────────────────────────

def extract_stats(entry: dict) -> dict:
    """Pull out the stats we care about from a hyperfine result entry."""
    return {
        "mean": entry.get("mean", 0),
        "stddev": entry.get("stddev", 0),
        "min": entry.get("min", 0),
        "max": entry.get("max", 0),
    }


def main():
    parser = argparse.ArgumentParser(description="Aggregate hyperfine benchmark results")
    parser.add_argument("--results-dir", type=Path, default=DEFAULT_RESULTS_DIR)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_RESULTS_DIR)
    args = parser.parse_args()

    results_dir: Path = args.results_dir
    output_dir: Path = args.output_dir
    output_dir.mkdir(parents=True, exist_ok=True)

    if not results_dir.exists():
        print(f"Error: results directory not found: {results_dir}")
        sys.exit(1)

    all_rows: List[dict] = []

    for folder_dir in sorted(results_dir.iterdir()):
        if not folder_dir.is_dir():
            continue

        folder = folder_dir.name
        json_files = sorted(folder_dir.glob("*.json"), key=lambda p: natural_sort_key(p.stem))

        if not json_files:
            continue

        folder_rows = []

        for jf in json_files:
            try:
                commands = load_hyperfine_json(jf)
            except (json.JSONDecodeError, KeyError) as e:
                print(f"  Warning: failed to parse {jf}: {e}")
                continue

            program = jf.stem

            d = extract_stats(commands.get("dafny", {}))
            l = extract_stats(commands.get("lean", {}))
            a = extract_stats(commands.get("lean_async", {}))

            row = {
                "folder": folder,
                "program": program,
                "dafny_mean": d["mean"], "dafny_stddev": d["stddev"],
                "dafny_min": d["min"], "dafny_max": d["max"],
                "lean_mean": l["mean"], "lean_stddev": l["stddev"],
                "lean_min": l["min"], "lean_max": l["max"],
                "async_mean": a["mean"], "async_stddev": a["stddev"],
                "async_min": a["min"], "async_max": a["max"],
            }
            folder_rows.append(row)

        # Sort naturally
        folder_rows.sort(key=lambda r: natural_sort_key(r["program"]))

        print_table(folder_rows, folder)
        create_bar_chart(folder_rows, folder, output_dir / f"chart_{folder}.png")
        all_rows.extend(folder_rows)

    write_csv(all_rows, output_dir / "benchmark_results.csv")


if __name__ == "__main__":
    main()
