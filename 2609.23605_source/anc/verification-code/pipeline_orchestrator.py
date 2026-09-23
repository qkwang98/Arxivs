#!/usr/bin/env python3
# Changelog (reverse chronological):
# 2026-07-31 17:08 - Claude-Code (agent-shell, no web session): created this
#   file, replacing code/face_lattice_pipeline.py's old stage2_watcher/
#   stage3_watcher. Deliberately plain Python (no Sage import) -- it never
#   does any Sage computation itself, only process management, so it stays
#   a lightweight, hard-to-crash scheduler. See LOGBOOK.md 2026-07-31 for the
#   full incident writeup this design responds to; short version:
#
#   1. The old stage2/stage3 watchers were single long-lived Sage processes
#      looping over ALL jobs in one address space. Sage's internal caches
#      never freed between jobs, so memory climbed across the batch and the
#      kernel OOM-killer eventually killed that one process at 15.6GB RSS.
#   2. That kill left its systemd --user scope (the interactive terminal)
#      in a failed state; systemd then tore down the WHOLE scope 45s later
#      -- bash, Claude Code, every other job sharing that terminal, all
#      killed together. This is why the earlier session appeared to "hang"
#      with no visible error: the whole process tree was gone, not stuck.
#   3. Separately, 54 stage-1 jobs were launched simultaneously, each
#      individually `ulimit -v 6GB`'d but with no cap on their SUM
#      (54 x 6GB = 324GB worst case on a 62GB machine) -- a latent second
#      bug, unrelated to what actually triggered the crash this time, but
#      equally capable of causing one.
#
#   This orchestrator fixes all three: every (stage, job) unit of work runs
#   as its own short-lived `sage -c` subprocess (so the OS reclaims its
#   memory on exit, sidestepping Sage's global caches entirely), wrapped in
#   its own transient `systemd-run --user --scope` with a hard MemoryMax/
#   MemorySwapMax ceiling (so a blowup is contained to that job's own scope,
#   never cascading into the caller's terminal the way it did before), a
#   `ulimit -v` backstop inside that scope (so a memory blowup more often
#   surfaces as a clean Python MemoryError -- confirmed 2026-07-31 that
#   stage 3's per-property `_time_limited` wrapper already catches this
#   gracefully, once combined with the LatticePoset(check=False) fix in
#   face_lattice_pipeline.py -- than a SIGKILL), and a wall-clock `timeout`
#   on top of both. A single global semaphore bounds AGGREGATE concurrency
#   across every stage combined (not per-stage), sized against the most
#   conservative (largest) per-job memory ceiling in use, so the running
#   total is provably bounded regardless of which stages happen to overlap.
#
#   Memory ceilings below are informed by real measurements, not guesses:
#   isolated single-job peak RSS on the largest case in the current batch
#   (n=8, d=7, 65026 poset elements) was ~800MB for stage 2's
#   face_lattice(), and ~1.1GB for stage 3's is_distributive() (the one
#   property tested standalone) with LatticePoset(check=False). Ceilings
#   are set several times above these measured peaks, not tight to them --
#   the point of the ulimit/MemoryMax pair is a safety backstop, not a
#   performance tune, and stage 3's other O(N^2)-join/meet-dependent
#   properties (is_modular, is_semidistributive, etc.) are EXPECTED to hit
#   their ceiling and fail gracefully at this element count -- that's the
#   correct, safe outcome, not a bug to chase.

"""
Plain-Python scheduler for code/face_lattice_pipeline.py's three-stage Sage
pipeline (stage 1: polytope construction; stage 2: face lattice; stage 3:
poset statistics). Deliberately does NOT import Sage -- all Sage work
happens in per-job `sage -c` subprocesses this script launches and bounds;
the scheduler itself only touches the filesystem and `subprocess`/`Popen`.

Each (stage, job) unit of work runs in total isolation from every other:
its own systemd --user transient scope (hard memory ceiling, killed
independently of everything else if it misbehaves), its own `ulimit -v`
inside that scope, and its own wall-clock `timeout`. See the changelog
above and LOGBOOK.md 2026-07-31 for why this replaces the previous
long-lived-watcher design.

Status of any job, at any time, is entirely filesystem-visible (no live
process needs to be inspected, no in-memory state needs to be trusted):

    n{n}_d{d}_{a}_stage{S}.started              -- stage S subprocess for
                                                     this job has started
                                                     (pid, timestamp)
    n{n}_d{d}_{a}_stage{S}.log                   -- that subprocess's
                                                     stdout/stderr
    n{n}_d{d}_{a}_polytopeonly.json              -- stage 1 succeeded
    n{n}_d{d}_{a}_polytope-and-flattice.json     -- stage 2 succeeded
      (with a top-level "poset_stats" key once stage 3 has also succeeded)

A job whose ".started" file exists, whose output file does not, and whose
pid is no longer a live process, has crashed (OOM-killed, hit its
`timeout`, or an uncaught exception) -- distinguishable from "still
running" (pid alive) or "not started yet" (no ".started" file at all)
without needing to have been watching it live. This was the actual
diagnostic gap in the 2026-07-31 incident (see the shared phone-chat
transcript quoted in that day's LOGBOOK.md entry): there was no way to tell
"still computing" from "silently dead" after the terminal disappeared.

Usage:

    python3 pipeline_orchestrator.py            # runs the JOBS list below
    python3 pipeline_orchestrator.py --stage3-only   # only (re)run stage 3
                                                       # on already-completed
                                                       # stage-2 output

Or import run_pipeline(jobs, ...) directly for a custom job list/config.
"""

import argparse
import json
import os
import subprocess
import sys
import time

CODE_DIR = os.path.dirname(os.path.abspath(__file__))
OUTDIR = '../runs'  # relative to CODE_DIR, matching face_lattice_pipeline.py's
                     # own convention -- all subprocesses are launched with
                     # cwd=CODE_DIR so this resolves the same way for them.

# Bare `sage` on $PATH resolves to a broken /opt/sage-dev install on this
# machine (confirmed 2026-07-31: `ModuleNotFoundError: No module named
# 'sage'`) -- use the working conda env's binary by full path instead.
SAGE_BIN = '/home/jan/miniforge3/envs/sage/bin/sage'

# Per-job resource ceilings, one config per stage. `memory_max_gb` is the
# systemd cgroup's hard ceiling (a breach is a SIGKILL, contained to that
# job's own scope); `ulimit_gb` is the process's own virtual-memory cap,
# set a bit below memory_max_gb so it trips FIRST where possible, producing
# a clean Python MemoryError (catchable by _time_limited) rather than a
# SIGKILL. `timeout_s` is the wall-clock backstop on top of both.
STAGE_CONFIG = {
    1: dict(memory_max_gb=5, memory_swap_max_mb=512, ulimit_gb=4, timeout_s=180),
    2: dict(memory_max_gb=5, memory_swap_max_mb=512, ulimit_gb=4, timeout_s=300),
    3: dict(memory_max_gb=9, memory_swap_max_mb=512, ulimit_gb=8, timeout_s=900),
}

# Single GLOBAL concurrency cap across ALL stages combined (not per-stage) --
# sized against the largest ceiling in use (stage 3's 9GB) so the running
# total is provably bounded: 5 * 9GB = 45GB, leaving ~17GB of the machine's
# 62GB for the desktop/Claude Code/everything else sharing it, even in the
# worst case where every slot happens to be a stage-3 job at once. Also
# comfortably under nproc (12) so jobs aren't fighting each other for CPU
# either.
MAX_CONCURRENT = 5

POLL_INTERVAL_S = 2


def _job_basename(n, d, a_name):
    return f'n{n}_d{d}_{a_name}'


def _polytopeonly_path(n, d, a_name):
    return os.path.join(CODE_DIR, OUTDIR, _job_basename(n, d, a_name) + '_polytopeonly.json')


def _flattice_path(n, d, a_name):
    return os.path.join(CODE_DIR, OUTDIR, _job_basename(n, d, a_name) + '_polytope-and-flattice.json')


def _started_path(stage, n, d, a_name):
    return os.path.join(CODE_DIR, OUTDIR, _job_basename(n, d, a_name) + f'_stage{stage}.started')


def _log_path(stage, n, d, a_name):
    return os.path.join(CODE_DIR, OUTDIR, _job_basename(n, d, a_name) + f'_stage{stage}.log')


def _pid_alive(pid):
    try:
        os.kill(pid, 0)
        return True
    except (ProcessLookupError, PermissionError):
        return False
    except OSError:
        return False


def job_status(stage, n, d, a_name):
    """
    'not_started' / 'running' / 'done' / 'crashed', purely from the
    filesystem plus a liveness check on the recorded pid -- no reliance on
    any live orchestrator state. 'done' means this stage's own output
    signal is present (the polytopeonly/flattice file for stages 1/2, or a
    'poset_stats' key for stage 3).
    """
    out_done = _stage_output_done(stage, n, d, a_name)
    if out_done:
        return 'done'
    started = _started_path(stage, n, d, a_name)
    if not os.path.exists(started):
        return 'not_started'
    try:
        with open(started) as f:
            pid = json.load(f)['pid']
    except (OSError, json.JSONDecodeError, KeyError):
        return 'crashed'  # sentinel exists but is unreadable -- treat as dead
    return 'running' if _pid_alive(pid) else 'crashed'


def _stage_output_done(stage, n, d, a_name):
    if stage == 1:
        return os.path.exists(_polytopeonly_path(n, d, a_name))
    if stage == 2:
        return os.path.exists(_flattice_path(n, d, a_name))
    if stage == 3:
        path = _flattice_path(n, d, a_name)
        if not os.path.exists(path):
            return False
        with open(path) as f:
            return 'poset_stats' in json.load(f)
    raise ValueError(stage)


def _stage2_input_ready(n, d, a_name):
    return os.path.exists(_polytopeonly_path(n, d, a_name))


def _stage3_input_ready(n, d, a_name):
    path = _flattice_path(n, d, a_name)
    return os.path.exists(path)  # stage3_run_one_job handles the
                                  # no-'poset'-key (stage-2-gave-up) case
                                  # itself, same as before


def launch_job(stage, n, d, a_name, timeout_override=None):
    """
    Launch one (stage, job) unit of work as a fully isolated OS process:
    its own transient systemd --user scope with a hard memory ceiling, a
    `ulimit -v` backstop inside it, and a wall-clock `timeout` on top.
    Returns the Popen handle; caller tracks it and polls .poll().
    """
    cfg = STAGE_CONFIG[stage]
    timeout_s = timeout_override if timeout_override is not None else cfg['timeout_s']
    ulimit_kb = cfg['ulimit_gb'] * 1_000_000

    sage_expr = (
        f"load('face_lattice_pipeline.py'); "
        f"stage{stage}_run_one_job({n}, {d}, {a_name!r})"
    )
    inner_cmd = (
        f"ulimit -v {ulimit_kb}; "
        f"timeout {timeout_s} {SAGE_BIN} -c \"{sage_expr}\""
    )
    cmd = [
        'systemd-run', '--user', '--scope', '--collect',
        '-p', f"MemoryMax={cfg['memory_max_gb']}G",
        '-p', f"MemorySwapMax={cfg['memory_swap_max_mb']}M",
        '--', 'bash', '-c', inner_cmd,
    ]
    log_f = open(_log_path(stage, n, d, a_name), 'w')
    proc = subprocess.Popen(cmd, cwd=CODE_DIR, stdout=log_f, stderr=subprocess.STDOUT)
    return proc, log_f


def run_pipeline(jobs, max_concurrent=MAX_CONCURRENT, poll_interval=POLL_INTERVAL_S,
                  stages=(1, 2, 3)):
    """
    jobs: list of (n, d, a_name) tuples -- the full worklist, run through
    whichever of `stages` are requested (default all three, in order,
    per-job -- stage 2 for a job only launches once stage 1's output
    exists, stage 3 only once stage 2's does). A single global semaphore
    (size max_concurrent) bounds concurrent subprocesses across ALL stages
    combined, not per-stage -- see MAX_CONCURRENT's comment for why.

    Bounded, not infinite: exits once every job has reached a terminal
    state for the requested stages (done, or crashed and not retried --
    this function does not auto-retry; a crashed job just stays crashed and
    is reported at the end, since blindly retrying whatever crashed a
    memory-bounded process is more likely to repeat the failure than fix
    it).
    """
    in_flight = {}  # (stage, n, d, a_name) -> (Popen, log_file)
    terminal = {}   # (stage, n, d, a_name) -> 'done' | 'crashed'

    def all_stage_jobs():
        for n, d, a_name in jobs:
            for stage in stages:
                yield (stage, n, d, a_name)

    def ready_to_launch(key):
        stage, n, d, a_name = key
        if key in in_flight or key in terminal:
            return False
        if job_status(stage, n, d, a_name) != 'not_started':
            return False  # already done, or a .started sentinel from a
                           # PRIOR run of this orchestrator is still live/
                           # unresolved -- handled by the polling loop below,
                           # not re-launched here
        if stage == 1:
            return True
        if stage == 2:
            return _stage2_input_ready(n, d, a_name)
        if stage == 3:
            return _stage3_input_ready(n, d, a_name)
        raise ValueError(stage)

    all_keys = list(all_stage_jobs())
    print(f'pipeline_orchestrator: {len(jobs)} jobs x stages {stages} '
          f'= {len(all_keys)} units of work, max_concurrent={max_concurrent}')

    while True:
        # absorb any .started sentinel left by a PRIOR orchestrator run
        # (e.g. resuming after this script itself was interrupted) whose
        # process is still alive -- track it instead of relaunching
        for key in all_keys:
            if key in in_flight or key in terminal:
                continue
            stage, n, d, a_name = key
            status = job_status(stage, n, d, a_name)
            if status == 'done':
                terminal[key] = 'done'
            elif status == 'crashed':
                terminal[key] = 'crashed'
            # 'running' with no Popen handle (foreign/prior process) is left
            # alone here; it will show as 'done' or 'crashed' on a later
            # poll once it actually exits, same as any other in-flight job

        # launch newly-eligible work up to the concurrency cap
        for key in all_keys:
            if len(in_flight) >= max_concurrent:
                break
            if ready_to_launch(key):
                stage, n, d, a_name = key
                print(f'  launching stage{stage} n={n} d={d} a={a_name}')
                proc, log_f = launch_job(stage, n, d, a_name)
                in_flight[key] = (proc, log_f)

        # reap finished subprocesses
        for key in list(in_flight):
            proc, log_f = in_flight[key]
            if proc.poll() is not None:
                log_f.close()
                stage, n, d, a_name = key
                status = job_status(stage, n, d, a_name)
                terminal[key] = 'done' if status == 'done' else 'crashed'
                print(f'  finished stage{stage} n={n} d={d} a={a_name}: '
                      f'{terminal[key]} (exit={proc.returncode})')
                del in_flight[key]

        pending = [k for k in all_keys if k not in in_flight and k not in terminal]
        if not pending and not in_flight:
            break
        time.sleep(poll_interval)

    n_done = sum(1 for v in terminal.values() if v == 'done')
    n_crashed = sum(1 for v in terminal.values() if v == 'crashed')
    print(f'pipeline_orchestrator: finished. {n_done} done, {n_crashed} crashed.')
    if n_crashed:
        print('  crashed units:')
        for key, status in sorted(terminal.items()):
            if status == 'crashed':
                stage, n, d, a_name = key
                print(f'    stage{stage} n={n} d={d} a={a_name} '
                      f'(see {_log_path(stage, n, d, a_name)})')
    return terminal


DEFAULT_JOBS = [
    (n, d, a_name)
    for n in range(3, 9)
    for d in range(1, n)
    for a_name in ('ones', 'kozlov')
]


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--stage3-only', action='store_true',
                         help='only run stage 3 (on already-completed stage-2 output)')
    args = parser.parse_args()
    stages = (3,) if args.stage3_only else (1, 2, 3)
    result = run_pipeline(DEFAULT_JOBS, stages=stages)
    sys.exit(1 if any(v == 'crashed' for v in result.values()) else 0)
