# arXiv source package

## Before upload

The author block in `main.tex` is populated as YINJIE LI, Independent Researcher, Nanjing, China, with the contact email shown on the title page. The Mathematics Subject Classification and key words are placed as an unnumbered first-page footnote, matching the requested title-page layout. Inspect arXiv's generated first page before final submission.

## Build

The manuscript inputs are `main.tex`, `references.bib`, and the generated `main.bbl`, all at archive root. The `anc/` directory is not needed by LaTeX. No figures or private local styles are required.

```sh
sh build.sh
```

The script runs PDFLaTeX, BibTeX, and two further PDFLaTeX passes. It falls back to `bibtex.original` when a distribution has a broken `bibtex` alternative, then to the bundled `.bbl` if neither executable is available. To explicitly test the arXiv-style bundled-bibliography route:

```sh
USE_BUNDLED_BBL=1 sh build.sh
```

The equivalent ordinary commands are:

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

Both a regenerated-bibliography build and a bundled-bibliography build were tested from clean final archive extractions. `main.bbl` is synchronized with the final source. Select `main.tex` and PDFLaTeX on arXiv and inspect arXiv's generated PDF before submitting.

## Reproducibility and contents

`anc/README.md` maps each exact certificate to its verifier. Current execution evidence is in `anc/release_verification/`; previous packaging logs are in `anc/archived_packaging_logs/`. Original nested source/proof bundles and their historical logs are preserved, with the current review distinguished from prior sessions.

The source ZIP and tar.gz have identical file paths and file bytes. They do not include the compiled paper, temporary TeX build files, private prompts, cover letters, or copyrighted reference PDFs. The final PDF and the broader reproducibility package are delivered separately.

`anc/lieb_4433_lean_round8.zip` contains the pinned order-14 Lean source. A separate final validation rebuilt the complete `Bridge.Young` proof chain successfully under Lean 4.19.0 and the pinned mathlib revision; the complete-theorem, generated-source, and final-axiom audits also passed. The formalization covers the order-14 bridge, its exact normalization, and the deduction of `(4,4,3,3)` permanental dominance from four explicitly stated Pate inequalities. It does not formalize the order-15 results or the full theorem through order 15. See `anc/release_verification/lean_final_validation_summary.md`. All required exact Python checks, including full cone regeneration, also completed successfully.
