# Recorded verification runs

Both commands completed successfully on 6 November 2026. Each was run once;
the elapsed times below are direct measurements of these two invocations.

## Environment and procedure

- CPython 3.12.14, Ubuntu 24.04.3 LTS, x86_64, Linux kernel 6.18.57.
- Reported CPU model: AMD EPYC 9V74 80-Core Processor. Nine logical CPUs were
  visible to the process; the verification tasks were run serially.
- The ancillary files were packed into a ZIP file and extracted into a new
  temporary directory. The manuscript and earlier working directories were
  not required by the verification programs.
- A fresh virtual environment was created with `venv`, with `with_pip=False`
  and `system_site_packages=False`. Its installed-distribution inventory was
  empty. Only the Python standard library was used.
- Both the entry point and its subprocesses ran with `-I -B`; user-site
  packages were disabled, optimization was off, and `PYTHON*` environment
  variables were removed. Python's isolated mode ignores `PYTHONHASHSEED`;
  these programs do not use random sampling.
- The extended run used a working directory outside the extracted package.
  The separate default run used a second empty working directory and absolute
  paths to the virtual-environment interpreter and verification script.
  This also checked that the programs do not depend on the caller's directory.

This is an isolated dependency and file setup on the recorded host. The
measurements do not claim a fresh operating-system installation or network
sandbox. The programs make no network requests.

## Measured command times

The following equivalent commands can be run from the downloaded source root:

```bash
python -I -B anc/verify_all.py
python -I -B anc/verify_all.py --extended
```

| Command | Complete command wall time | Time reported inside the entry point | Exit status |
| --- | ---: | ---: | ---: |
| Default | 2.322623 s | 2.291119 s | 0 |
| `--extended` | 33.255628 s | 33.223311 s | 0 |

Complete command wall times include interpreter startup and final output
collection. Inner times start just before the manifest check. All timings use
`time.perf_counter`. Times vary with hardware and system load; these are single
observations rather than performance guarantees.

For a comparable isolated run on a POSIX system, after extracting the complete
source package, use:

```bash
python3 -m venv --without-pip verify-venv
verify-venv/bin/python -I -B anc/verify_all.py --extended
```

No package installation is needed. Python 3.10 or later is required. Do not
enable `-O`, because the optional type A diagnostics use assertions.

## Checks that passed

The default invocation reconstructed all bounded cases and matched all seven
generated JSON files. In particular, the F4 reconstruction covered all 567
gap-four cases, with 497 one-column, 49 two-column, and 21 three-column cases.
The independent root-permutation program checked their 2,594 recorded rows
and 660 witness minors. The other required root systems also passed. The type
D sample check covered 55 signed representatives and 160 Hilbert coefficients.

The extended invocation repeated the default checks and then verified 417
filtered maxima in S6, 4,998 in S7, and the S6 horizontal diagnostics: 347,542
incidence instances, 29,968 greedy lifts, and 4,096 complete prefix witnesses.

Both runs ended with the exact output line:

```text
ALL REQUESTED CHECKS PASSED.
```

## Evidence files

| File | Contents |
| --- | --- |
| `default_stdout.txt` | Complete combined standard output and standard error of the separate default invocation. |
| `default_run_metrics.json` | Its exit status, environment, per-task timings, total times, and hashes. |
| `extended_stdout.txt` | Complete combined standard output and standard error of the extended invocation. |
| `run_metrics.json` | Its exit status, environment, per-task timings, total times, and hashes. |

The `default_prefix_wall_seconds` field in `run_metrics.json` describes only
the default phase within the extended invocation. The standalone default
measurement is in `default_run_metrics.json` and is the one used in the table.

The records identify the exact tested Python programs and distributed JSON
files through `CERTIFICATE_MANIFEST.sha256`. Its digest is stored in each
metrics file. The manifest is relative to `anc/`; it deliberately does not
cover this report, runtime logs, or the LaTeX manuscript. It verifies file
identity separately from the mathematical assertions checked by the programs.

## Independent final-package recheck (6 November 2026)

The `final_default_stdout.txt`, `final_extended_stdout.txt`, and `final_recheck_metrics.json` files record fresh standard-library checks on Windows. Both invocations used Python isolated mode with bytecode writes disabled and a working directory outside the source package. Both exited successfully. The earlier Linux records above remain the original measurements reported in the manuscript. Finite verification does not certify the arbitrary-rank geometric arguments.
