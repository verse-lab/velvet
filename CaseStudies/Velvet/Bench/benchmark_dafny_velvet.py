#!/usr/bin/env python3
"""
Benchmark script for comparing Dafny vs Velvet/Lean verification performance.

Usage:
    python benchmark_dafny_velvet.py [--runs N] [--output DIR]

Must be run from the project root directory.
"""

import argparse
import json
import re
import statistics
import subprocess
import sys
import time
from dataclasses import dataclass, field, asdict
from datetime import datetime
from pathlib import Path
from typing import List, Tuple, Dict, Optional

import matplotlib.pyplot as plt
import numpy as np

# ============================================================================
# Configuration
# ============================================================================

SCRIPT_DIR = Path(__file__).parent.resolve()
PROJECT_ROOT = SCRIPT_DIR.parent.parent.parent  # Go up to Loom/Code
BENCHMARK_DIR = SCRIPT_DIR
FOLDERS = ["both_easy", "lean_is_harder", "trans_proof_in_dafny"]
DEFAULT_NUM_RUNS = 5
DEFAULT_TIMEOUT = 300  # 5 minutes


# ============================================================================
# Data Classes
# ============================================================================

@dataclass
class BenchmarkResult:
    """Aggregated benchmark results for a single program pair."""
    program_name: str
    dfy_path: str
    lean_path: str

    # Dafny results
    dafny_times: List[float] = field(default_factory=list)
    dafny_avg: float = 0.0
    dafny_min: float = 0.0
    dafny_max: float = 0.0
    dafny_std: float = 0.0
    dafny_success_rate: float = 0.0
    dafny_errors: List[str] = field(default_factory=list)

    # Lean results
    lean_times: List[float] = field(default_factory=list)
    lean_avg: float = 0.0
    lean_min: float = 0.0
    lean_max: float = 0.0
    lean_std: float = 0.0
    lean_success_rate: float = 0.0
    lean_errors: List[str] = field(default_factory=list)


@dataclass
class FolderResults:
    """Results for all programs in a folder category."""
    folder_name: str
    folder_path: str
    results: List[BenchmarkResult] = field(default_factory=list)
    total_dafny_time: float = 0.0
    total_lean_time: float = 0.0


# ============================================================================
# Discovery Functions
# ============================================================================

def discover_file_pairs(folder_path: Path) -> List[Tuple[str, Path, Path]]:
    """Find matching .dfy and .lean file pairs."""
    pairs = []
    dfy_files = sorted(folder_path.glob("*.dfy"))

    for dfy_file in dfy_files:
        base_name = dfy_file.stem
        lean_file = folder_path / f"{base_name}.lean"

        if lean_file.exists():
            pairs.append((base_name, dfy_file, lean_file))
        else:
            print(f"  Warning: Missing Lean file for {dfy_file.name}")

    return pairs


# ============================================================================
# Verification Functions
# ============================================================================

def run_verification_timed(
    command: List[str],
    cwd: Optional[Path] = None,
    timeout: int = DEFAULT_TIMEOUT
) -> Tuple[float, bool, str]:
    """Execute command and return (time, success, error_msg)."""
    start = time.perf_counter()
    try:
        result = subprocess.run(
            command,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=cwd
        )
        elapsed = time.perf_counter() - start
        success = result.returncode == 0
        error = "" if success else result.stderr[:500]  # Truncate long errors
        return (elapsed, success, error)
    except subprocess.TimeoutExpired:
        return (timeout, False, f"Timeout after {timeout}s")
    except FileNotFoundError as e:
        return (0.0, False, f"Command not found: {e}")
    except Exception as e:
        return (0.0, False, str(e))


def run_dafny_verification(dfy_file: Path) -> Tuple[float, bool, str]:
    """Run Dafny verification and measure time."""
    cmd = ["dafny", "verify", str(dfy_file)]
    return run_verification_timed(cmd)


def run_lean_verification(lean_file: Path, project_root: Path) -> Tuple[float, bool, str]:
    """Run Lean verification via lake env and measure time."""
    cmd = ["lake", "env", "lean", str(lean_file)]
    return run_verification_timed(cmd, cwd=project_root)


# ============================================================================
# Benchmarking Functions
# ============================================================================

def benchmark_single_file(
    name: str,
    dfy_path: Path,
    lean_path: Path,
    num_runs: int,
    project_root: Path
) -> BenchmarkResult:
    """Benchmark a single Dafny/Lean file pair."""
    result = BenchmarkResult(
        program_name=name,
        dfy_path=str(dfy_path),
        lean_path=str(lean_path)
    )

    # Benchmark Dafny
    for i in range(num_runs):
        elapsed, success, error = run_dafny_verification(dfy_path)
        if success:
            result.dafny_times.append(elapsed)
        else:
            result.dafny_errors.append(error)

    # Benchmark Lean
    for i in range(num_runs):
        elapsed, success, error = run_lean_verification(lean_path, project_root)
        if success:
            result.lean_times.append(elapsed)
        else:
            result.lean_errors.append(error)

    # Compute statistics for Dafny
    if result.dafny_times:
        result.dafny_avg = statistics.mean(result.dafny_times)
        result.dafny_min = min(result.dafny_times)
        result.dafny_max = max(result.dafny_times)
        result.dafny_std = statistics.stdev(result.dafny_times) if len(result.dafny_times) > 1 else 0.0
        result.dafny_success_rate = len(result.dafny_times) / num_runs

    # Compute statistics for Lean
    if result.lean_times:
        result.lean_avg = statistics.mean(result.lean_times)
        result.lean_min = min(result.lean_times)
        result.lean_max = max(result.lean_times)
        result.lean_std = statistics.stdev(result.lean_times) if len(result.lean_times) > 1 else 0.0
        result.lean_success_rate = len(result.lean_times) / num_runs

    return result


def benchmark_folder(folder_name: str, num_runs: int, project_root: Path) -> FolderResults:
    """Benchmark all programs in a folder."""
    folder_path = BENCHMARK_DIR / folder_name
    results = FolderResults(folder_name=folder_name, folder_path=str(folder_path))

    try:
        file_pairs = discover_file_pairs(folder_path)
    except Exception as e:
        print(f"  Error discovering files in {folder_path}: {e}")
        return results

    if not file_pairs:
        print(f"  No file pairs found in {folder_path}")
        return results

    print(f"  Found {len(file_pairs)} file pairs")

    for i, (name, dfy_path, lean_path) in enumerate(file_pairs, 1):
        print(f"  [{i}/{len(file_pairs)}] Benchmarking {name}...", end=" ", flush=True)

        try:
            result = benchmark_single_file(name, dfy_path, lean_path, num_runs, project_root)
            results.results.append(result)

            # Log progress
            if result.dafny_success_rate > 0 and result.lean_success_rate > 0:
                print(f"Dafny={result.dafny_avg:.2f}s, Lean={result.lean_avg:.2f}s")
            else:
                print(f"WARN (Dafny: {result.dafny_success_rate*100:.0f}%, Lean: {result.lean_success_rate*100:.0f}%)")

        except Exception as e:
            print(f"ERROR: {e}")
            error_result = BenchmarkResult(
                program_name=name,
                dfy_path=str(dfy_path),
                lean_path=str(lean_path),
                dafny_errors=[str(e)],
                lean_errors=[str(e)]
            )
            results.results.append(error_result)

    # Compute totals
    results.total_dafny_time = sum(r.dafny_avg for r in results.results if r.dafny_avg > 0)
    results.total_lean_time = sum(r.lean_avg for r in results.results if r.lean_avg > 0)

    return results


# ============================================================================
# Plotting Functions
# ============================================================================

def natural_sort_key(name: str) -> int:
    """Extract numeric suffix for natural sorting."""
    match = re.search(r'(\d+)', name)
    return int(match.group(1)) if match else 0


def shorten_name(name: str) -> str:
    """Shorten program name for display."""
    name = name.replace('_impl', '')
    name = name.replace('verina_basic_', 'basic_')
    name = name.replace('verina_advanced_', 'adv_')
    return name


def format_folder_name(folder: str) -> str:
    """Format folder name for display in title."""
    return folder.replace('_', ' ').title()


def create_comparison_bar_chart(folder_results: FolderResults, output_path: Path) -> None:
    """Create and save bar chart for folder results."""
    # Sort results by program name (natural sort for numeric suffixes)
    sorted_results = sorted(
        folder_results.results,
        key=lambda r: natural_sort_key(r.program_name)
    )

    # Filter out results with no successful runs
    sorted_results = [r for r in sorted_results if r.dafny_avg > 0 or r.lean_avg > 0]

    if not sorted_results:
        print(f"  Warning: No valid results to plot for {folder_results.folder_name}")
        return

    # Extract data
    program_names = [r.program_name for r in sorted_results]
    dafny_times = [r.dafny_avg for r in sorted_results]
    lean_times = [r.lean_avg for r in sorted_results]

    # Shorten names for display
    display_names = [shorten_name(name) for name in program_names]

    # Set up the plot
    fig, ax = plt.subplots(figsize=(14, 6))

    x = np.arange(len(display_names))
    width = 0.35

    # Create bars
    bars_dafny = ax.bar(
        x - width/2, dafny_times, width,
        label='Dafny', color='#3498db', edgecolor='black', linewidth=0.5
    )
    bars_lean = ax.bar(
        x + width/2, lean_times, width,
        label='Lean/Velvet', color='#e67e22', edgecolor='black', linewidth=0.5
    )

    # Customize appearance
    ax.set_xlabel('Program', fontsize=12)
    ax.set_ylabel('Verification Time (seconds)', fontsize=12)
    ax.set_title(
        f'Verification Time Comparison: {format_folder_name(folder_results.folder_name)}',
        fontsize=14, fontweight='bold'
    )
    ax.set_xticks(x)
    ax.set_xticklabels(display_names, rotation=45, ha='right', fontsize=9)
    ax.legend(loc='upper right', fontsize=10)

    # Add grid for readability
    ax.yaxis.grid(True, linestyle='--', alpha=0.7)
    ax.set_axisbelow(True)

    # Tight layout to prevent label cutoff
    plt.tight_layout()

    # Save figure
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close(fig)

    print(f"  Saved plot: {output_path}")


def generate_all_plots(all_results: Dict[str, FolderResults], output_dir: Path) -> None:
    """Generate plots for all folders."""
    output_dir.mkdir(parents=True, exist_ok=True)
    for folder_name, results in all_results.items():
        output_path = output_dir / f"benchmark_{folder_name}.png"
        create_comparison_bar_chart(results, output_path)


# ============================================================================
# Statistics & Output
# ============================================================================

def save_results_json(all_results: Dict[str, FolderResults], output_path: Path) -> None:
    """Save results to JSON file."""
    def convert(obj):
        if hasattr(obj, '__dict__'):
            return {k: convert(v) for k, v in obj.__dict__.items()}
        elif isinstance(obj, list):
            return [convert(i) for i in obj]
        elif isinstance(obj, Path):
            return str(obj)
        return obj

    data = {
        "metadata": {
            "timestamp": datetime.now().isoformat(),
            "num_runs": DEFAULT_NUM_RUNS,
            "project_root": str(PROJECT_ROOT)
        },
        "folders": {name: convert(results) for name, results in all_results.items()}
    }

    with open(output_path, 'w') as f:
        json.dump(data, f, indent=2)

    print(f"Saved results to: {output_path}")


def print_summary(all_results: Dict[str, FolderResults]) -> None:
    """Print formatted summary to console."""
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60 + "\n")

    total_programs = 0
    dafny_faster_count = 0

    for folder_name, results in all_results.items():
        print(f"{folder_name} ({len(results.results)} programs):")
        print(f"  Dafny total avg: {results.total_dafny_time:.2f}s")
        print(f"  Lean total avg:  {results.total_lean_time:.2f}s")

        if results.total_dafny_time > 0:
            speedup = results.total_lean_time / results.total_dafny_time
            print(f"  Speedup:         {speedup:.2f}x")

        # Count comparisons
        for r in results.results:
            if r.dafny_avg > 0 and r.lean_avg > 0:
                total_programs += 1
                if r.dafny_avg < r.lean_avg:
                    dafny_faster_count += 1

        print()

    if total_programs > 0:
        print(f"Overall: Dafny faster in {dafny_faster_count}/{total_programs} cases")


# ============================================================================
# Main Entry Point
# ============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Benchmark Dafny vs Velvet/Lean verification performance"
    )
    parser.add_argument(
        "--runs", "-n", type=int, default=DEFAULT_NUM_RUNS,
        help=f"Number of runs per file (default: {DEFAULT_NUM_RUNS})"
    )
    parser.add_argument(
        "--output", "-o", type=Path, default=BENCHMARK_DIR / "results",
        help="Output directory for plots and JSON"
    )
    parser.add_argument(
        "--folders", nargs="+", default=FOLDERS,
        help="Folders to benchmark"
    )
    args = parser.parse_args()

    # Verify project root
    if not PROJECT_ROOT.exists():
        print(f"Error: Project root not found: {PROJECT_ROOT}")
        sys.exit(1)

    print(f"Benchmarking Dafny vs Velvet/Lean")
    print(f"  Project root: {PROJECT_ROOT}")
    print(f"  Runs per file: {args.runs}")
    print(f"  Output directory: {args.output}")
    print()

    all_results = {}

    for folder_name in args.folders:
        print(f"Processing folder: {folder_name}")
        results = benchmark_folder(folder_name, args.runs, PROJECT_ROOT)
        all_results[folder_name] = results
        print()

    # Generate outputs
    generate_all_plots(all_results, args.output)
    save_results_json(all_results, args.output / "benchmark_results.json")
    print_summary(all_results)


if __name__ == "__main__":
    main()
