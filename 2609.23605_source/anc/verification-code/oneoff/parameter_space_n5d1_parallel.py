# Changelog (reverse chronological):
# 2026-08-01 - Claude: created this file. Plain-Python orchestrator (no Sage/Julia import at
#   module level -- process management only, same spirit as pipeline_orchestrator.py) exploiting
#   this machine's 12 logical cores to parallelize the now-Sage-only n=5,d=1 bulk sampling, per
#   Jan's instruction to use Sage for all computation (Oscar only for spot-checking) and "exploit
#   parallelism when appropriate". Coarse-grained chunking (a handful of `sage -c` subprocesses,
#   each processing a large contiguous slice), NOT one process per point -- these computations are
#   cheap (~6.4ms/point measured) and uniform, so per-point process-spawn overhead would dominate;
#   this is a different risk profile from pipeline_orchestrator.py's heavy face-lattice jobs (which
#   genuinely needed one-process-per-job isolation against unpredictable blowups), so that heavier
#   systemd-run/MemoryMax apparatus is intentionally not used here.

"""
Parallel Sage-only driver for parameter_space_n5d1.py's bulk sampling. Splits a points file into
N_WORKERS contiguous chunks, runs each as its own `sage -c` subprocess calling
run_on_points_chunk, waits for all of them, then merges via merge_chunks_with_spotcheck.

Usage (from the code/ directory):
    python3 parameter_space_n5d1_parallel.py <points_filename> [n_workers] [spotcheck_filename]

e.g.:
    python3 parameter_space_n5d1_parallel.py paramspace_n5_d1_points_seed3_N50000.json 10 \\
        paramspace_n5_d1_results_julia_spotcheck_N300.json
"""

import json
import os
import subprocess
import sys
import time

OUTDIR = '../runs'
SAGE = '/home/jan/miniforge3/envs/sage/bin/sage'


def run_parallel(points_filename, n_workers=10, spotcheck_filename=None):
    n_workers = int(n_workers)
    with open(os.path.join(OUTDIR, points_filename)) as f:
        n_points = len(json.load(f)['points'])

    chunk_size = (n_points + n_workers - 1) // n_workers
    bounds = [(i * chunk_size, min((i + 1) * chunk_size, n_points)) for i in range(n_workers)]
    bounds = [(s, e) for s, e in bounds if s < e]

    print(f'{n_points} points, {len(bounds)} workers, ~{chunk_size} points/chunk')
    t0 = time.time()
    procs = []
    for start, end in bounds:
        cmd = [SAGE, '-c',
               f"load('parameter_space_n5d1.py'); "
               f"run_on_points_chunk('{points_filename}', {start}, {end})"]
        procs.append((start, end, subprocess.Popen(cmd, stdout=subprocess.PIPE,
                                                     stderr=subprocess.STDOUT, text=True)))

    chunk_paths = []
    for start, end, p in procs:
        out, _ = p.communicate()
        if p.returncode != 0:
            print(f'CHUNK [{start}:{end}) FAILED (exit {p.returncode}):\n{out}')
            raise RuntimeError(f'chunk [{start}:{end}) failed')
        print(out.strip())
        chunk_paths.append(os.path.join(
            OUTDIR, points_filename.replace('.json', f'_chunk{start}-{end}.json')))
    print(f'all {len(bounds)} chunks done: {time.time()-t0:.1f}s wall-clock '
          f'(vs. serial estimate ~{n_points*0.0064:.0f}s)')

    merge_cmd = [SAGE, '-c',
                 f"load('parameter_space_n5d1.py'); "
                 f"merge_chunks_with_spotcheck('{points_filename}', {chunk_paths!r}, "
                 f"{spotcheck_filename!r})"]
    result = subprocess.run(merge_cmd, capture_output=True, text=True)
    print(result.stdout.strip())
    if result.returncode != 0:
        print(result.stderr)
        raise RuntimeError('merge failed')

    for cp in chunk_paths:
        os.remove(cp)
    print(f'cleaned up {len(chunk_paths)} chunk files')


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    points_filename = sys.argv[1]
    n_workers = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    spotcheck_filename = sys.argv[3] if len(sys.argv) > 3 else None
    run_parallel(points_filename, n_workers, spotcheck_filename)
