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

    import matplotlib.ticker as mticker

    plt.rcParams.update({
        "font.family": "sans-serif",
        "font.sans-serif": ["Inter", "Helvetica Neue", "Arial", "DejaVu Sans"],
    })

    names = [shorten_name(r["program"]) for r in rows]
    dafny = np.array([r["dafny_mean"] for r in rows])
    lean = np.array([r["lean_mean"] for r in rows])
    async_ = np.array([r["async_mean"] for r in rows])
    dafny_err = np.array([r["dafny_stddev"] for r in rows])
    lean_err = np.array([r["lean_stddev"] for r in rows])
    async_err = np.array([r["async_stddev"] for r in rows])

    x = np.arange(len(names))
    width = 0.24

    fig, ax = plt.subplots(figsize=(max(10, len(names) * 1.4), 5.5))
    fig.patch.set_facecolor("white")
    ax.set_facecolor("white")

    bar_kw = dict(width=width, edgecolor="white", linewidth=0.8, zorder=3)

    y_max = float(max(dafny.max(), lean.max(), async_.max()))
    Y_CAP = 10 if y_max >= 20 else None  # None means no clipping

    dafny_plot = np.minimum(dafny, Y_CAP) if Y_CAP else dafny
    lean_plot = np.minimum(lean, Y_CAP) if Y_CAP else lean
    async_plot = np.minimum(async_, Y_CAP) if Y_CAP else async_

    bars_d = ax.bar(x - width, dafny_plot, label="Dafny", color="#4A90D9", **bar_kw)
    bars_l = ax.bar(x, lean_plot, label="Lean (sync)", color="#E8833A", **bar_kw)
    bars_a = ax.bar(x + width, async_plot, label="Lean (async)", color="#50B86C", **bar_kw)

    # Draw break marks on clipped bars + labels (staggered for clipped)
    all_bars = [(bars_d, dafny), (bars_l, lean), (bars_a, async_)]
    for i in range(len(names)):
        clipped_idx = 0
        for bars, vals in all_bars:
            bar = bars[i]
            val = vals[i]
            if val <= 0:
                continue
            clipped = Y_CAP is not None and val > Y_CAP
            bx = bar.get_x()
            bw = bar.get_width()
            if clipped:
                # White gap + two thin slanted lines to indicate break
                gap_h = Y_CAP * 0.025
                ax.fill_between([bx, bx + bw], Y_CAP - gap_h, Y_CAP + gap_h,
                                color="white", zorder=5)
                slant = Y_CAP * 0.015
                for dy in [-gap_h * 0.5, gap_h * 0.5]:
                    ax.plot([bx, bx + bw], [Y_CAP + dy - slant, Y_CAP + dy + slant],
                            color="#888888", linewidth=0.7, zorder=6)
                # Stagger label height for each clipped bar in same group
                label_y = Y_CAP + Y_CAP * 0.05 + clipped_idx * Y_CAP * 0.07
                ax.text(bx + bw / 2, label_y,
                        f"{val:.1f}s", ha="center", va="bottom", fontsize=6.5,
                        color="#222222", fontweight="bold")
                clipped_idx += 1
            else:
                # Normal label above bar
                pad = (Y_CAP if Y_CAP else y_max) * 0.02
                ax.text(bx + bw / 2, val + pad,
                        f"{val:.1f}s", ha="center", va="bottom", fontsize=6,
                        color="#222222")

    ax.set_xlabel("Program", fontsize=11, color="#333333", labelpad=8)
    ax.set_ylabel("Verification Time (s)", fontsize=11, color="#333333", labelpad=8)
    title = folder.replace("_", " ").title()
    ax.set_title(f"Verification Time: {title}", fontsize=14, fontweight="bold",
                 color="#222222", pad=14)
    ax.set_xticks(x)
    ax.set_xticklabels(names, rotation=40, ha="right", fontsize=9, color="#444444")
    ax.tick_params(axis="y", labelsize=9, colors="#444444")

    ax.yaxis.grid(True, linestyle="-", alpha=0.15, color="#000000", zorder=0)
    ax.xaxis.grid(False)
    ax.set_axisbelow(True)

    for spine in ax.spines.values():
        spine.set_visible(False)
    ax.tick_params(axis="both", length=0)

    if Y_CAP is not None:
        ax.set_ylim(0, Y_CAP * 1.18)
    else:
        ax.set_ylim(0, y_max * 1.15)

    legend = ax.legend(loc="upper center", bbox_to_anchor=(0.5, -0.15),
                       ncol=3, fontsize=9, frameon=False)

    plt.tight_layout()
    plt.savefig(output_path, dpi=200, bbox_inches="tight", facecolor="white")
    # Also save as PDF
    pdf_path = output_path.with_suffix(".pdf")
    plt.savefig(pdf_path, bbox_inches="tight", facecolor="white")
    plt.close(fig)
    print(f"Chart saved: {output_path}")
    print(f"Chart saved: {pdf_path}")


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

    # Combined chart with all folders
    if all_rows:
        create_combined_chart(all_rows, output_dir / "chart_all.png")


def create_combined_chart(rows: List[dict], output_path: Path) -> None:
    if not HAS_MATPLOTLIB or not rows:
        return

    plt.rcParams.update({
        "font.family": "sans-serif",
        "font.sans-serif": ["Inter", "Helvetica Neue", "Arial", "DejaVu Sans"],
    })

    names = [shorten_name(r["program"]) for r in rows]
    folders = [r["folder"] for r in rows]
    dafny = np.array([r["dafny_mean"] for r in rows])
    lean = np.array([r["lean_mean"] for r in rows])
    async_ = np.array([r["async_mean"] for r in rows])

    x = np.arange(len(names))
    width = 0.24
    y_max = float(max(dafny.max(), lean.max(), async_.max()))
    Y_CAP = 10 if y_max >= 20 else None  # None means no clipping

    dafny_plot = np.minimum(dafny, Y_CAP) if Y_CAP else dafny
    lean_plot = np.minimum(lean, Y_CAP) if Y_CAP else lean
    async_plot = np.minimum(async_, Y_CAP) if Y_CAP else async_

    fig, ax = plt.subplots(figsize=(max(14, len(names) * 0.7), 6))
    fig.patch.set_facecolor("white")
    ax.set_facecolor("white")

    bar_kw = dict(width=width, edgecolor="white", linewidth=0.8, zorder=3)

    bars_d = ax.bar(x - width, dafny_plot, label="Dafny", color="#4A90D9", **bar_kw)
    bars_l = ax.bar(x, lean_plot, label="Lean (sync)", color="#E8833A", **bar_kw)
    bars_a = ax.bar(x + width, async_plot, label="Lean (async)", color="#50B86C", **bar_kw)

    # Break marks + labels (staggered for clipped)
    all_bars_c = [(bars_d, dafny), (bars_l, lean), (bars_a, async_)]
    for i in range(len(names)):
        clipped_idx = 0
        for bars, vals in all_bars_c:
            bar = bars[i]
            val = vals[i]
            if val <= 0:
                continue
            clipped = Y_CAP is not None and val > Y_CAP
            bx = bar.get_x()
            bw = bar.get_width()
            if clipped:
                gap_h = Y_CAP * 0.025
                ax.fill_between([bx, bx + bw], Y_CAP - gap_h, Y_CAP + gap_h,
                                color="white", zorder=5)
                slant = Y_CAP * 0.015
                for dy in [-gap_h * 0.5, gap_h * 0.5]:
                    ax.plot([bx, bx + bw], [Y_CAP + dy - slant, Y_CAP + dy + slant],
                            color="#888888", linewidth=0.7, zorder=6)
                label_y = Y_CAP + Y_CAP * 0.05 + clipped_idx * Y_CAP * 0.07
                ax.text(bx + bw / 2, label_y,
                        f"{val:.1f}s", ha="center", va="bottom", fontsize=5.5,
                        color="#222222", fontweight="bold")
                clipped_idx += 1
            else:
                pad = (Y_CAP if Y_CAP else y_max) * 0.02
                ax.text(bx + bw / 2, val + pad,
                        f"{val:.1f}s", ha="center", va="bottom", fontsize=5,
                        color="#222222")

    # Separator lines + category labels between folder groups
    prev_folder = None
    group_starts = []
    for i, f in enumerate(folders):
        if f != prev_folder:
            group_starts.append((i, f))
            if prev_folder is not None:
                sep_x = i - 0.5
                ax.axvline(sep_x, color="#CCCCCC", linewidth=0.8, linestyle="--", zorder=1)
            prev_folder = f

    ax.set_xlabel("Program", fontsize=11, color="#333333", labelpad=8)
    ax.set_ylabel("Verification Time (s)", fontsize=11, color="#333333", labelpad=8)
    ax.set_title("Verification Time: All Programs", fontsize=14, fontweight="bold",
                 color="#222222", pad=14)
    ax.set_xticks(x)
    ax.set_xticklabels(names, rotation=45, ha="right", fontsize=7, color="#444444")
    ax.tick_params(axis="y", labelsize=9, colors="#444444")

    ax.yaxis.grid(True, linestyle="-", alpha=0.15, color="#000000", zorder=0)
    ax.xaxis.grid(False)
    ax.set_axisbelow(True)

    for spine in ax.spines.values():
        spine.set_visible(False)
    ax.tick_params(axis="both", length=0)

    if Y_CAP is not None:
        ax.set_ylim(0, Y_CAP * 1.18)
    else:
        ax.set_ylim(0, y_max * 1.15)

    # Category labels at bottom
    effective_cap = Y_CAP if Y_CAP else y_max
    for idx, (start, folder) in enumerate(group_starts):
        end = group_starts[idx + 1][0] if idx + 1 < len(group_starts) else len(folders)
        mid = (start + end - 1) / 2
        label = folder.replace("_", " ").title()
        ax.text(mid, -effective_cap * 0.22, label, ha="center", va="top", fontsize=8,
                color="#666666", fontstyle="italic",
                transform=ax.get_xaxis_transform())

    legend = ax.legend(loc="upper center", bbox_to_anchor=(0.5, -0.18),
                       ncol=3, fontsize=9, frameon=False)

    plt.tight_layout()
    plt.savefig(output_path, dpi=200, bbox_inches="tight", facecolor="white")
    pdf_path = output_path.with_suffix(".pdf")
    plt.savefig(pdf_path, bbox_inches="tight", facecolor="white")
    plt.close(fig)
    print(f"Chart saved: {output_path}")
    print(f"Chart saved: {pdf_path}")


if __name__ == "__main__":
    main()
