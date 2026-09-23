#!/usr/bin/env python3
"""build_notebooklm_package.py

Changelog (reverse chronological):
  2026-09-05  Created.  Assembles a folder that can be uploaded to NotebookLM (or
              any other document-QA tool) covering ARTICLE 1 of this project --
              the manuscript, the cited literature we actually hold, and the
              working notes behind it.

              Why a script rather than a checked-in folder: everything it copies
              already exists in the repository, and duplicating ~15 MB of PDFs
              into git to make a convenience folder is a bad trade.  The output
              directory is gitignored; re-run the script to rebuild it.

              PROVENANCE IS ENFORCED, NOT ASSUMED.  This repo's literature/
              convention is that literature/ holds open-access material only,
              while literature/subscription/ holds items obtained through Jan's
              LiU subscription that are NOT freely redistributable.  Uploading a
              file to NotebookLM transfers it to Google.  So:
                * open-access items go in 02-cited-literature/;
                * anything restricted goes in 90-RESTRICTED-decide-before-upload/
                  with a warning file, and is NEVER placed alongside the rest.

              Later the same day: Jan settled both open points.  The series is
              article 1 = the convex hull (this package), article 2 = ff-vector
              counting, article 3 = the lattice-point question and open problems.
              And Ziegler's textbook -- the only restricted candidate -- is NOT
              to be uploaded, so it moved from CITED_RESTRICTED to CITED_WITHHELD
              and the package no longer emits a restricted folder at all.  The
              quarantine machinery is kept for article 2's package.

  2026-09-06  article/exterior-convex_draft_*.* renamed to
              article/exterior-convex_article1_draft_*.*, so the series naming is
              uniform (article1 / article2 / article3).  Source path and upload
              name updated to match; nothing else about the package changed.

Usage:
    python3 code/build_notebooklm_package.py [--out DIR] [--list]

    --out    where to build (default: artefacts/notebooklm-article1/, gitignored)
    --list   print the plan and exit, copying nothing
"""

import argparse
import shutil
import sys
from pathlib import Path

PROJ = Path(__file__).resolve().parent.parent          # 20-projects/exterior-convex
ROOT = PROJ.parent.parent                              # repository root

# --- the manuscript -------------------------------------------------------
# The reviewer's brief. Ships as 00-... so it sorts above everything else. Round 2 exists
# because round 1 produced three "critical findings" that were all misreadings of the working
# notes' account of ALREADY-FIXED bugs; the brief addresses that head-on.
BRIEF = [
    ("artefacts/notebooklm-brief-article1-round2.md",
     "00-BRIEF-READ-THIS-FIRST.md"),
]

MANUSCRIPT = [
    ("article/exterior-convex_article1_draft_4.pdf",
     "Snellman-ARTICLE1-draft4-Hilbert-functions-and-Minkowski-sums-of-Kozlov-simplices.pdf"),
]

# --- literature cited by article 1, that we actually hold -----------------
# (reference number in draft 4, source path relative to PROJ, upload name)
CITED_OPEN = [
    (1, "literature/Amata and Crupi - 2020 - HILBERT FUNCTIONS OF GRADED MODULES OVER AN EXTERIOR ALGEBRA AN ALGORITHMIC APPROACH.pdf",
        "Amata-Crupi-2020-Hilbert-functions-graded-modules-exterior-algebra-algorithmic.pdf"),
    (2, "literature/Amata and Crupi - 2020 - A generalization of Kruskal–Katona’s theorem.pdf",
        "Amata-Crupi-2020-A-generalization-of-Kruskal-Katona.pdf"),
    (3, "literature/Amata and Crupi - 2022 - ExteriorModules a package for computing monomial modules over an exterior algebra.pdf",
        "Amata-Crupi-2021-ExteriorModules-package.pdf"),
    (4, "literature/Aramova et al. - 1997 - Gotzmann Theorems for Exterior Algebras and Combinatorics.pdf",
        "Aramova-Herzog-Hibi-1997-Gotzmann-theorems-exterior-algebras.pdf"),
    (9, "literature/Kozlov - 1997 - Convex Hulls of f- and β-Vectors.pdf",
        "Kozlov-1997-Convex-hulls-of-f-and-beta-vectors.pdf"),
    (11, "literature/Kupreyeva - 2019 - Simplices of f-vectors (bachelor's thesis).pdf",
         "Kupreyeva-2019-Simplices-of-f-vectors-BSc-thesis.pdf"),
    (12, "literature/Linusson - 1999 - The Number of M-Sequences and f-Vectors.pdf",
         "Linusson-1999-The-number-of-M-sequences-and-f-vectors.pdf"),
    (15, "literature/skoldberg-monomial-golod-quotients-exterior-algebra.pdf",
         "Skoldberg-1999-Monomial-Golod-quotients-of-exterior-algebras.pdf"),
    (16, "literature/snellman-morenosocias_generic-ideals-exterior-algebra_arXiv-math0007089.pdf",
         "Snellman-MorenoSocias-2002-Generic-ideals-in-the-exterior-algebra.pdf"),
]

# Jan's own paper, cited in article 1's open-problem list; lives with the
# publication record rather than in literature/.
CITED_OPEN_ELSEWHERE = [
    (13, ROOT / "50-writing/preprints-publications/published/math_0010117_lifting-grobner-bases-from-the-exterior-algebra.pdf",
         "Nilsson-Snellman-2003-Lifting-Grobner-bases-from-the-exterior-algebra.pdf"),
]

# --- cited, held, but NOT freely redistributable --------------------------
# Anything listed here is copied into 90-RESTRICTED-decide-before-upload/ rather than into
# 02-cited-literature/, with a warning file, so it can never be swept into an upload by accident.
# Currently empty: the only candidate was Ziegler, and Jan decided on 2026-09-05 not to upload it
# (see CITED_WITHHELD below). The machinery stays because article 2's package will likely need it.
CITED_RESTRICTED: list[tuple[int, str, str, str]] = []

# --- cited, held, and deliberately NOT included ---------------------------
CITED_WITHHELD = [
    (18, "Ziegler 1995, Lectures on Polytopes, Springer GTM 152 -- a commercially published "
         "textbook, cited by article 1 only for standard polytope background. "
         "Jan's decision, 2026-09-05: do not upload. (This project's literature/ convention "
         "forbids downloading textbooks at all; the local copy predates the rule being written "
         "down.)"),
]

# --- cited but not held ---------------------------------------------------
CITED_MISSING = [
    (5, "Aramova & Herzog 2000, Almost regular sequences and Betti numbers, Amer. J. Math. 122"),
    (6, "Eisenbud 1995, Commutative Algebra with a View Toward Algebraic Geometry (textbook)"),
    (7, "Herzog & Hibi 2011, Monomial Ideals (textbook)"),
    (8, "Katona 1968, A theorem of finite sets (proceedings; page range unresolved -- see draft 4)"),
    (10, "Kruskal 1963, The number of simplices in a complex (proceedings)"),
    (14, "Schutzenberger 1959, RLE Quarterly Progress Report 55, MIT"),
    (17, "Stanley 1996, Combinatorics and Commutative Algebra, 2nd ed. (textbook)"),
]

# --- working notes, as generated Markdown previews ------------------------
NOTES_CORE = [
    ("working-notes/r-vectors-of-simplicial-complexes.md",
     "NOTE-1-r-vectors-and-ff-vectors.md"),
    ("working-notes/ids-modules-direct-sums-of-graded-ideals.md",
     "NOTE-2-ids-modules.md"),
    ("working-notes/amata-crupi-monomial-modules.md",
     "NOTE-3-Amata-Crupi-monomial-modules.md"),
    ("working-notes/kozlov-simplex-and-kozlov-polytope.md",
     "NOTE-4-Kozlov-simplex-and-Kozlov-polytope.md"),
    ("working-notes/kruskal-katona-and-the-amata-crupi-generalization.md",
     "NOTE-5-Kruskal-Katona-and-the-Amata-Crupi-generalization.md"),
    ("working-notes/multigraded-hilbert-functions.md",
     "NOTE-6-multigraded-Hilbert-functions.md"),
    ("working-notes/README.md",
     "NOTE-0-working-notes-index.md"),
]

NOTES_SUPPORTING = [
    ("working-notes/rank-r-kozlov-minkowski-proof-attempt.md",
     "PROOF-full-from-scratch-proof-and-Kozlov-audit.md"),
    ("working-notes/proper-hilbert-functions-kozlov-minkowski.md",
     "PROOF-claim-with-definitions-and-citations.md"),
    ("working-notes/right-angle-simplices-notes.md",
     "DETAIL-right-angle-simplices-extremal-matrix-H-representations.md"),
    ("working-notes/skoldberg-indicator-module.md",
     "DETAIL-Skoldberg-indicator-module.md"),
    ("working-notes/counting-ff-vectors.md",
     "ARTICLE2-MATERIAL-counting-ff-vectors-Linusson-extended.md"),
    ("crupi-amata-bugreport/2026-08-07-1107-note-theorem-4-2-review.md",
     "REVIEW-Amata-Crupi-Theorem-4.2-adversarial-review.md"),
    # Added 2026-09-06: these two say what has already been tried on the rank-r
    # V-description, which is the reviewer's main task. Including them is what stops
    # a second review from re-proposing the prefix-sum route or the all-circuits
    # hope, both of which are already known to fail.
    ("working-notes/pairwise-reduction-proof-strategies.md",
     "OPEN-PROBLEM-1-pairwise-reduction-four-strategies.md"),
    ("working-notes/strategy-a-attempt.md",
     "OPEN-PROBLEM-2-what-has-been-proved-and-what-failed.md"),
]

NOTES_BACKGROUND = [
    (ROOT / "30-notes/products-duals-and-polar-polytopes.md",
     "BACKGROUND-products-duals-and-polar-polytopes.md"),
    (ROOT / "30-notes/abstract-polytopes.md",
     "BACKGROUND-abstract-polytopes.md"),
    (ROOT / "30-notes/abel-summation.md",
     "BACKGROUND-abel-summation.md"),
    (ROOT / "30-notes/theorems-of-the-alternative.md",
     "BACKGROUND-theorems-of-the-alternative.md"),
]

README = """# NotebookLM package — exterior-convex, article 1

Built by `code/build_notebooklm_package.py` on {date}. Everything here is a **copy** of something
already in the repository; nothing here is a source of truth. Rebuild rather than edit.

## What this covers

Part I of the exterior-convex series *Hilbert functions over the exterior algebra and f-vectors in
higher rank*, subtitled *I: Minkowski sums of Kozlov simplices* — the manuscript in
`01-manuscript/`, the papers it cites, and the working notes behind it.

## Folders

| folder | what it is | upload? |
|---|---|---|
| `01-manuscript/` | the manuscript itself, draft 4 | yes — upload first |
| `02-cited-literature/` | the cited papers we hold, all open access | yes |
| `03-working-notes-core/` | the six notes matching the manuscript's sections, plus their index | yes |
| `04-working-notes-supporting/` | full proofs, the long exploratory record, the Theorem 4.2 review | yes, if you want depth |
| `05-background/` | cross-cutting notes from the repo's `30-notes/` | optional |

## Read `00-BRIEF-READ-THIS-FIRST.md` before the manuscript

It answers the previous review point by point and sets the task. It also states the one thing a
reviewer of this package must understand: **the working notes are a historical record of the
project, not a description of the current manuscript.** Passages describing errors are almost always
describing errors that were found and fixed, often weeks before the current draft. The previous
review reported three of them as critical live defects. The brief asks for every claimed defect to
be backed by a quotation from the manuscript itself.

**Upload the whole folder.** Nothing in it is withheld-by-default and nothing needs a decision at
upload time; the decisions were made when it was built, and are recorded below.

## Where this sits in the series

Article 1 is the manuscript here — the convex hull. Article 2 will be the *ff*-vector counting
result (Linusson's recursion extended to rank *r*); article 3 will be the lattice-point question and
the open problems. Draft 4 refers to both as companion papers.

## What is deliberately not here

Uploading a file to NotebookLM transfers it to Google. This repository distinguishes open-access
material (`literature/`) from material obtained via the LiU subscription and *not* freely
redistributable (`literature/subscription/`); `02-cited-literature/` is open access only. Nothing
from `literature/subscription/` is cited by article 1, so that distinction does not bite here.

Cited, held locally, and withheld by decision:

{withheld}

Cited and not held at all — mostly textbooks, which this project's conventions say not to download,
and two old conference proceedings:

{missing}

If NotebookLM is asked about any of these it will have only what the manuscript and the notes say
about them. That is worth knowing before trusting an answer about, say, exactly what Kruskal's 1963
paper states, or about a definition attributed to Ziegler.

## Suggested questions, once it is loaded

These are chosen to exercise the parts where the manuscript makes claims that the sources can
check, or where the notes and the manuscript deliberately differ:

- Does the manuscript's Corollary (facets of the Kozlov simplex) actually follow from Kozlov's
  Theorem 4.1, and is the facet description anywhere in Kozlov's paper?
- The manuscript claims Kozlov's own convention makes the properness restriction automatic. Where
  in his paper is that convention stated, and does his second proof depend on it?
- Compare the manuscript's Definition of an ids-module with Amata and Crupi's Definition 2.1. What
  does the manuscript add, and why?
- The Theorem 4.2 review claims the published clause is wrong for tied generator degrees. Reconstruct
  the counterexample from the review and check it against the Amata–Crupi paper itself.
- Linusson's paper counts f-vectors. What exactly would have to change to count ff-vectors instead?
  (The `ARTICLE2-MATERIAL-` note answers this; see whether NotebookLM gets there from Linusson
  alone, given only his paper and the manuscript.)
- Where do the manuscript and the working notes disagree, if anywhere?

## A caution

NotebookLM is grounded in these sources but still paraphrases, and it will not flag a subtle
misreading of a proof. This project has already been bitten once by exactly that failure mode — an
audit criticised Kozlov for an omission he had not made, because it checked his proof against a
definition from elsewhere rather than his own. Treat answers as leads to check, not as findings.
"""

RESTRICTED_NOTE = """# Read before uploading anything in this folder

These files are cited by article 1 and are held locally, but they are **not open access** and are
therefore **not** included in `02-cited-literature/`. Uploading a file to NotebookLM transfers it to
Google. Whether that is acceptable for these items is Jan's decision, not a default.

{items}

Deleting this folder is the safe option, and costs only that NotebookLM will answer questions about
standard polytope background from the manuscript's own summary instead of from the source.
"""


def plan():
    """Return a list of (kind, src, dest_subdir, dest_name)."""
    items = []
    for src, name in MANUSCRIPT:
        items.append(("manuscript", PROJ / src, "01-manuscript", name))
    for src, name in BRIEF:
        items.append(("brief", PROJ / src, ".", name))
    for _, src, name in CITED_OPEN:
        items.append(("cited", PROJ / src, "02-cited-literature", name))
    for _, src, name in CITED_OPEN_ELSEWHERE:
        items.append(("cited", Path(src), "02-cited-literature", name))
    for _, src, name, _why in CITED_RESTRICTED:
        items.append(("restricted", PROJ / src, "90-RESTRICTED-decide-before-upload", name))
    for src, name in NOTES_CORE:
        items.append(("note", PROJ / src, "03-working-notes-core", name))
    for src, name in NOTES_SUPPORTING:
        items.append(("note", PROJ / src, "04-working-notes-supporting", name))
    for src, name in NOTES_BACKGROUND:
        items.append(("note", Path(src), "05-background", name))
    return items


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(PROJ / "artefacts" / "notebooklm-article1"))
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--date", default="2026-09-05",
                    help="stamped into the README (no clock access in this script)")
    args = ap.parse_args()

    items, missing_files = plan(), []
    for kind, src, sub, name in items:
        if not src.exists():
            missing_files.append((kind, src))

    if args.list:
        for kind, src, sub, name in items:
            mark = " " if src.exists() else "!"
            print("%s %-10s %-34s %s" % (mark, kind, sub, name))
        if missing_files:
            print("\nMISSING (%d):" % len(missing_files))
            for kind, src in missing_files:
                print("   ", src)
        return 1 if missing_files else 0

    if missing_files:
        print("Refusing to build: %d source file(s) missing." % len(missing_files))
        for kind, src in missing_files:
            print("   ", src)
        print("Run with --list to see the whole plan.")
        return 1

    out = Path(args.out)
    if out.exists():
        shutil.rmtree(out)
    counts = {}
    for kind, src, sub, name in items:
        d = out / sub
        d.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, d / name)
        counts[sub] = counts.get(sub, 0) + 1

    missing_md = "\n".join("- [%d] %s" % (n, t) for n, t in CITED_MISSING)
    withheld_md = ("\n".join("- [%d] %s" % (n, t) for n, t in CITED_WITHHELD)
                   if CITED_WITHHELD else "- (none)")
    (out / "00-README-FIRST.md").write_text(
        README.format(date=args.date, missing=missing_md, withheld=withheld_md))
    if CITED_RESTRICTED:
        restricted_items = "\n".join(
            "## %s\n\n%s\n" % (name, why) for _, _src, name, why in CITED_RESTRICTED)
        (out / "90-RESTRICTED-decide-before-upload" / "00-READ-THIS-FIRST.md").write_text(
            RESTRICTED_NOTE.format(items=restricted_items))

    total = sum(counts.values())
    size = sum(f.stat().st_size for f in out.rglob("*") if f.is_file())
    print("Built %s" % out)
    for sub in sorted(counts):
        print("   %-38s %2d file(s)" % (sub, counts[sub]))
    print("   %-38s %2d files, %.1f MB" % ("TOTAL", total, size / 1048576))
    if CITED_RESTRICTED:
        print("\nUpload everything EXCEPT 90-RESTRICTED-decide-before-upload/ "
              "unless you have decided otherwise.")
    else:
        print("\nNothing is withheld at upload time: upload the whole folder.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
