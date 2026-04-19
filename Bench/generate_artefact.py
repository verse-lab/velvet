#!/usr/bin/env python3
"""
CAV 26 artefact driver: benchmarks Dafny vs Velvet/Lean on the programs in
Bench/{both_easy,needs_proofs} and produces results/chart_all.pdf.

Usage (from any directory):
    python3 Bench/generate_artefact.py
    python3 Bench/generate_artefact.py --runs 3 --warmup 1
    python3 Bench/generate_artefact.py --skip-bench     # only re-plot
"""

import argparse
import csv
import json
import math
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Tuple

SCRIPT_DIR = Path(__file__).parent.resolve()
REPO_ROOT = SCRIPT_DIR.parent
RESULTS_DIR = SCRIPT_DIR / "results"
FOLDERS = ["both_easy", "needs_proofs"]


# ── Pre-flight ───────────────────────────────────────────────────────────────

def check_prereqs() -> None:
    missing = [tool for tool in ("hyperfine", "dafny", "lake") if shutil.which(tool) is None]
    if missing:
        sys.exit(f"error: missing required tool(s): {', '.join(missing)}")
    try:
        import matplotlib  # noqa: F401
        import numpy       # noqa: F401
    except ImportError as e:
        sys.exit(f"error: missing Python dependency: {e.name}\n"
                 f"       install with: python3 -m pip install matplotlib numpy")


# ── Benchmark phase ──────────────────────────────────────────────────────────

def discover_pairs(folder: Path) -> List[Tuple[str, Path, Path]]:
    pairs = []
    for dfy in sorted(folder.glob("*.dfy")):
        lean = folder / f"{dfy.stem}.lean"
        if lean.exists():
            pairs.append((dfy.stem, dfy, lean))
        else:
            print(f"  skip {dfy.name}: no matching .lean")
    return pairs


def run_hyperfine(name: str, dfy: Path, lean: Path, out_json: Path, runs: int, warmup: int) -> None:
    out_json.parent.mkdir(parents=True, exist_ok=True)
    cmd = [
        "hyperfine",
        "--runs", str(runs),
        "--warmup", str(warmup),
        "--export-json", str(out_json),
        "--command-name", "dafny", f"dafny verify {dfy}",
        "--command-name", "lean",  f"cd {REPO_ROOT} && lake env lean {lean}",
    ]
    print(f"  benchmarking: {name}")
    subprocess.run(cmd, check=True)


def run_benchmarks(runs: int, warmup: int) -> None:
    for folder_name in FOLDERS:
        folder = SCRIPT_DIR / folder_name
        if not folder.is_dir():
            print(f"skipping missing folder: {folder_name}")
            continue
        print(f"=== folder: {folder_name} ===")
        out_dir = RESULTS_DIR / folder_name
        out_dir.mkdir(parents=True, exist_ok=True)
        for name, dfy, lean in discover_pairs(folder):
            run_hyperfine(name, dfy, lean, out_dir / f"{name}.json", runs, warmup)


# ── Aggregation (adapted from aggregate.py, async removed) ───────────────────

def natural_sort_key(name: str) -> Tuple:
    parts = re.split(r'(\d+)', name)
    return tuple(int(p) if p.isdigit() else p.lower() for p in parts)


def shorten_name(name: str) -> str:
    name = name.replace("_impl", "")
    name = name.replace("verina_basic_", "b")
    name = name.replace("verina_advanced_", "a")
    return name


def geo_mean(values: List[float]) -> float:
    pos = [v for v in values if v > 0 and v != float("inf")]
    if not pos:
        return 0.0
    return math.exp(sum(math.log(v) for v in pos) / len(pos))


def compute_ratios(rows: List[dict]) -> List[dict]:
    enriched = []
    for r in rows:
        r = dict(r)
        r["ratio_lean"] = r["lean_mean"] / r["dafny_mean"] if r["dafny_mean"] > 0 else float("inf")
        r["speedup_lean"] = r["dafny_mean"] / r["lean_mean"] if r["lean_mean"] > 0 else float("inf")
        enriched.append(r)
    return enriched


def extract_stats(entry: dict) -> dict:
    return {
        "mean":   entry.get("mean", 0),
        "stddev": entry.get("stddev", 0),
        "min":    entry.get("min", 0),
        "max":    entry.get("max", 0),
    }


def load_rows() -> List[dict]:
    rows: List[dict] = []
    for folder_name in FOLDERS:
        folder_dir = RESULTS_DIR / folder_name
        if not folder_dir.is_dir():
            continue
        folder_rows = []
        for jf in sorted(folder_dir.glob("*.json"), key=lambda p: natural_sort_key(p.stem)):
            try:
                with open(jf) as f:
                    data = json.load(f)
            except (json.JSONDecodeError, OSError) as e:
                print(f"  warning: failed to read {jf}: {e}")
                continue
            commands = {r["command"]: r for r in data.get("results", [])}
            d = extract_stats(commands.get("dafny", {}))
            l = extract_stats(commands.get("lean", {}))
            folder_rows.append({
                "folder":      folder_name,
                "program":     jf.stem,
                "dafny_mean":  d["mean"], "dafny_stddev": d["stddev"],
                "dafny_min":   d["min"],  "dafny_max":    d["max"],
                "lean_mean":   l["mean"], "lean_stddev":  l["stddev"],
                "lean_min":    l["min"],  "lean_max":     l["max"],
            })
        folder_rows.sort(key=lambda r: natural_sort_key(r["program"]))
        rows.extend(folder_rows)
    return rows


CSV_FIELDS = [
    "folder", "program",
    "dafny_mean", "dafny_stddev", "dafny_min", "dafny_max",
    "lean_mean",  "lean_stddev",  "lean_min",  "lean_max",
    "ratio_lean", "speedup_lean",
]


def write_csv(rows: List[dict], path: Path) -> None:
    with open(path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=CSV_FIELDS, extrasaction="ignore")
        w.writeheader()
        w.writerows(rows)
    print(f"csv written: {path}")


# ── Chart (adapted from aggregate.py) ────────────────────────────────────────

def _bar_chart(ax, names, dafny, lean, label_fontsize=6):
    import numpy as np
    x = np.arange(len(names))
    width = 0.25
    gap = 0.03
    half_offset = (width + gap) / 2

    y_max = float(max(dafny.max(), lean.max()))
    Y_CAP = 6.5 if y_max >= 20 else None

    def clip(arr):
        return np.minimum(arr, Y_CAP) if Y_CAP else arr

    common = dict(edgecolor="white", linewidth=0.5, zorder=3)
    bars_d = ax.bar(x - half_offset, clip(dafny), width=width, label="Dafny",  color="#4477AA", **common)
    bars_l = ax.bar(x + half_offset, clip(lean),  width=width, label="Velvet", color="#EE6677", **common)

    all_bars = [(bars_d, dafny), (bars_l, lean)]
    effective_cap = Y_CAP if Y_CAP else y_max
    for i in range(len(names)):
        clipped_entries = []
        for bars, vals in all_bars:
            val = vals[i]
            if val <= 0:
                continue
            bar = bars[i]
            bx, bw = bar.get_x(), bar.get_width()
            clipped = Y_CAP is not None and val > Y_CAP
            if clipped:
                gap_h = Y_CAP * 0.025
                ax.fill_between([bx, bx + bw], Y_CAP - gap_h, Y_CAP + gap_h,
                                color="white", zorder=5)
                slant = Y_CAP * 0.015
                for dy in (-gap_h * 0.5, gap_h * 0.5):
                    ax.plot([bx, bx + bw], [Y_CAP + dy - slant, Y_CAP + dy + slant],
                            color="#888888", linewidth=0.7, zorder=6)
                clipped_entries.append((val, bx + bw / 2))
            else:
                pad = effective_cap * 0.015
                ax.text(bx + bw / 2, val + pad, f"{val:.2f}",
                        ha="center", va="bottom", fontsize=label_fontsize,
                        color="#222222", rotation=90)

        if clipped_entries and Y_CAP is not None:
            label_y = Y_CAP + effective_cap * 0.04
            for val, cx in clipped_entries:
                ax.text(cx, label_y, f"{val:.2f}", ha="center", va="bottom",
                        fontsize=label_fontsize, color="#222222",
                        fontweight="bold", rotation=90)

    ax.set_ylabel("Verification Time (s)", fontsize=11, labelpad=8)
    ax.set_xticks(x)
    ax.set_xticklabels(names, rotation=30, ha="right", fontsize=8)
    ax.tick_params(axis="y", labelsize=9)
    ax.yaxis.grid(True, linestyle="-", alpha=0.15, color="#000000", zorder=0)
    ax.xaxis.grid(False)
    ax.set_axisbelow(True)
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.spines["left"].set_linewidth(0.6)
    ax.spines["bottom"].set_linewidth(0.6)
    if Y_CAP is not None:
        ax.set_ylim(0, Y_CAP * 1.1)
    else:
        ax.set_ylim(0, y_max * 1.10)
    ax.legend(loc="upper left", bbox_to_anchor=(0.01, 0.92), fontsize=9,
              frameon=True, facecolor="white", edgecolor="lightgray")


def create_combined_chart(rows: List[dict], png_path: Path) -> None:
    import matplotlib.pyplot as plt
    import numpy as np
    plt.rcParams.update({
        "font.family": "sans-serif",
        "font.sans-serif": ["Inter", "Helvetica Neue", "Arial", "DejaVu Sans"],
    })

    names = [shorten_name(r["program"]) for r in rows]
    folders = [r["folder"] for r in rows]
    dafny = np.array([r["dafny_mean"] for r in rows])
    lean = np.array([r["lean_mean"]  for r in rows])

    fig, ax = plt.subplots(figsize=(max(7, len(names) * 0.35), 4))
    fig.patch.set_facecolor("white")
    ax.set_facecolor("white")
    _bar_chart(ax, names, dafny, lean, label_fontsize=5.5)

    prev_folder = None
    for i, f in enumerate(folders):
        if f != prev_folder:
            if prev_folder is not None:
                ax.axvline(i - 0.5, color="#CCCCCC", linewidth=0.8,
                           linestyle="--", zorder=1)
            prev_folder = f

    ax.set_xticklabels(names, rotation=30, ha="right", fontsize=8.5)
    import matplotlib.pyplot as plt
    plt.tight_layout()
    plt.savefig(png_path, dpi=200, bbox_inches="tight", facecolor="white")
    pdf_path = png_path.with_suffix(".pdf")
    plt.savefig(pdf_path, bbox_inches="tight", facecolor="white")
    plt.close(fig)
    print(f"chart saved: {png_path}")
    print(f"chart saved: {pdf_path}")


# ── Summary ──────────────────────────────────────────────────────────────────

def print_summary(rows: List[dict]) -> None:
    n = len(rows)
    if n == 0:
        print("no benchmark rows to summarise")
        return
    total_d = sum(r["dafny_mean"] for r in rows)
    total_l = sum(r["lean_mean"] for r in rows)
    ratios_l = [r["ratio_lean"] for r in rows]
    speedups_l = [r["speedup_lean"] for r in rows]
    lean_wins = sum(1 for r in rows if r["lean_mean"] < r["dafny_mean"])
    print()
    print("  GRAND SUMMARY")
    print("  " + "=" * 60)
    print(f"  programs benchmarked:           {n}")
    print(f"  total Dafny  time:              {total_d:.3f}s")
    print(f"  total Velvet time:              {total_l:.3f}s")
    if total_d > 0:
        print(f"  aggregate ratio Velvet/Dafny:   {total_l / total_d:.2f}x")
    if total_l > 0:
        print(f"  aggregate speedup Velvet:       {total_d / total_l:.2f}x")
    print(f"  geo-mean ratio   Velvet/Dafny:  {geo_mean(ratios_l):.2f}x")
    print(f"  geo-mean speedup Velvet:        {geo_mean(speedups_l):.2f}x")
    print(f"  Velvet faster than Dafny:       {lean_wins}/{n} ({100 * lean_wins / n:.0f}%)")
    print("  " + "=" * 60)


# ── Main ─────────────────────────────────────────────────────────────────────

def main() -> None:
    ap = argparse.ArgumentParser(description="Build the CAV 26 artefact (benchmark + chart).")
    ap.add_argument("--runs",   type=int, default=10, help="hyperfine --runs (default 10)")
    ap.add_argument("--warmup", type=int, default=1,  help="hyperfine --warmup (default 1)")
    ap.add_argument("--skip-bench", action="store_true",
                    help="skip hyperfine; re-plot from existing results/*/*.json")
    args = ap.parse_args()

    check_prereqs()
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    if not args.skip_bench:
        run_benchmarks(args.runs, args.warmup)

    rows = load_rows()
    if not rows:
        sys.exit("error: no benchmark rows found (did hyperfine run?)")

    rows_with_ratios = compute_ratios(rows)
    write_csv(rows_with_ratios, RESULTS_DIR / "benchmark_results.csv")
    create_combined_chart(rows, RESULTS_DIR / "chart_all.png")
    print_summary(rows_with_ratios)


if __name__ == "__main__":
    main()
