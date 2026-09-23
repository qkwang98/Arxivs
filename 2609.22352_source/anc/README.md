# Computational supplement: linearized Painleve II and IV

Companion to **Contour Computation of Linearized Painleve II and IV Solutions
with Monodromy-Based Error Control**, Oleg M. Kiselev.

This package contains the numerical implementations, automated tests,
saved results, and tools for regenerating the six English manuscript tables.
Run commands from the extracted package root (or the downloaded `anc` folder).

## Environment and tests

Use Python 3.12 and the package versions recorded in
`computational_preprint/requirements-high-precision.txt`:

```sh
python3.12 -m venv .venv
.venv/bin/python -m pip install -r computational_preprint/requirements-high-precision.txt
.venv/bin/python -m unittest discover -s computational_preprint -p 'test_*.py'
.venv/bin/python rebuild_tables_en.py --output tables_rebuilt
```

The suite contains 42 tests of the spectral and kernel identities, local
continuation, sensitivity equations, initial-basis error identity, and
refinement-budget decisions. Regenerated tables should match the manuscript
source tables byte for byte. The numerical computations do not require TeX.

## Recompute the parameter study

Always use a new output directory; experiment drivers protect existing data.

```sh
.venv/bin/python computational_preprint/parameter_study.py --output computational_preprint/results/recomputed_parameters
.venv/bin/python computational_preprint/check_parameter_truncation.py --input computational_preprint/results/recomputed_parameters
.venv/bin/python computational_preprint/build_parameter_report.py --input computational_preprint/results/recomputed_parameters --tables parameter_tables
```

The report generator produces its original Russian table headings; the
English rebuilding tool translates headings for the frozen manuscript data.
Numerical entries are unchanged. To restrict the first calculation, use
`--cases pii_u015 pii_u025 pii_w015 piv_theta035 piv_theta039` with a subset
of these names. The truncation and report commands expect all five cases.

## Final datasets

- `pii_comparison`: regular PII, three accuracy levels.
- `equal_accuracy_coarse_matched`, `equal_accuracy_fine`: complex PIV.
- `rigid_oscillatory_checked_e02`: transition and subsequent oscillations.
- `rigid_oscillatory_controls`: variable-tolerance RK and endpoint refinement.
- `parameter_study`: five additional backgrounds and truncation checks.

Other result directories preserve preliminary calculations and snapshots as
an audit trail. Their status fields distinguish completed and unsuccessful
runs. Historical path strings and protected-file hashes are provenance
metadata. The portable commands above use the distributed files.

The plotted data are saved in the results directory. Plot-generation
implementations are `computational_preprint/build_equal_accuracy_report.py`
and `computational_preprint/build_rigid_oscillatory_report.py`.
The English manuscript uses the same numerical graphics as the Russian
working version. The separate contour schematic is provided as TikZ in
the manuscript source.

## Accuracy and integrity

The refinement criterion is a computational a posteriori diagnostic.
Its indicators are observed increments, rather than certified interval
upper bounds. Comparisons are at matched solution errors, with monodromy
drift and Wronskian error measured separately. The long transition data
are archived here; they are not rerun by the parameter-study command.

`MANIFEST.json` gives SHA-256 checksums for the distributed files.
Checksums establish file identity, while analytical tests and refinement
experiments assess mathematical and numerical correctness.

OpenAI Codex (OpenAI) assisted with code and manuscript preparation under
the author's direction, as disclosed in the article. Numerical data and
plots are reproducible outputs of the supplied computational workflows.
