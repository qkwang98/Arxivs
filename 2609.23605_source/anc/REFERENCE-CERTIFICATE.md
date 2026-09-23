# Certificate of Existence — references cited in article 1

*(`articles/article-1/exterior-convex_article1_latest.org`; written 2026-09-20, against the
version of that date. Line numbers refer to the `.org` source, which is the source of truth.)*

## Purpose

arXiv's 2026 enforcement policy imposes a one-year submission ban on authors for whom there is
"incontrovertible evidence" of unchecked large-language-model (LLM) output in a paper, and
explicitly names hallucinated or fabricated references as a trigger for that finding. This series
was written with substantial AI assistance (see each article's own Acknowledgements and Disclosure
sections), so it is worth being able to show, plainly and checkably, that this did not happen
here: every reference the article cites is a real, locatable publication, and every substantive
claim attributed to a reference is backed by text the author (or a reviewer) can go and read.

This document is that check, in the pattern of the same author's
`lattice-line-covers/references/REFERENCE-CERTIFICATE` (2026-08). For each cited key it records:
the full bibliographic entry as cited; which sentence of the article the reference supports, with
a line number in the `.org` source; and then *either* a verbatim quotation of the relevant passage
from a held copy of the source, with a locator, *or* an explicit statement that no primary copy is
held, plus what independent verification of the bibliographic data was done instead.

## Method, stated once

- **Quotations** were copied from `pdftotext -layout` extractions of the PDFs actually held in
  the working repository's `literature/` directory (or, for the two textbooks so marked, from
  copies in Jan's private reference library, fetched for the check and deleted after) — none were
  reconstructed from prior familiarity. `pdftotext` mangles ligatures and some mathematics; where
  a quotation shows artifacts of that (e.g. `w12x` for `[12]`, `Ž` for `(`), the mangling is the
  extractor's, reproduced as extracted rather than silently repaired.
- **Registry checks** name their source and date: MathSciNet lookups were done by Jan by hand
  (2026-09-14/16, folded into `exterior-convex-references.bib` with per-entry annotations);
  OpenAlex checks 2026-09-08; Crossref checks 2026-09-20 via `api.crossref.org` against the DOI.
- The bibliography file itself, `references/exterior-convex-references.bib` (synced from the
  working repository), carries the same verification annotations as comments; this document is
  the readable summary, that file the operational record.

## Findings worth reading first

1. **One incorrect pagination was found and corrected** (2026-09-14, Jan's MathSciNet lookup):
   `Katona1968` had carried pages 209–214; MathSciNet MR0290982 gives *Theory of Graphs (Proc.
   Colloq., Tihany, 1966)*, **pp. 187–207**, Academic Press. The suspected Academic
   Press/Akadémiai Kiadó co-publication split was *not* the cause — 209–214 was simply wrong.
2. **One unverifiable reference was removed** (2026-09-14): `Schutzenberger1959` (MIT RLE
   Quarterly Progress Report 55) is not indexed in MathSciNet and its fields had only ever been
   recorded from memory; its role as the third name beside Kruskal–Katona is taken by
   `ClementsLindstroem1969` (MR0246781), which is indexed and was checked.
3. **The last from-memory entry was verified rather than removed** (2026-09-20): `Meshalkin1963`
   (the English translation — the printing the article cites, per Jan's 2026-09-16 decision) was
   checked against Crossref via DOI `10.1137/1108023`: *Theory of Probability & Its Applications*
   **8**(2) (1963), 203–204 — every field recorded from memory matched, and the entry now carries
   the DOI. Jan's standing question of whether this citation should instead be dropped from the
   article is thereby moot.
4. **One citation was made more precise** (2026-09-20): the article's `rem-no-support-functions`
   said the face-decomposition identity for Minkowski sums "is" Ziegler's Proposition 7.12; the
   proposition as printed is the normal-fan common-refinement statement, of which the identity is
   an immediate consequence. The article now says "follows from". See entry 15.
5. **`AmataCrupi2021`'s year is 2021**, not the 2022 in the held PDF's filename: Crossref for DOI
   `10.2140/jsag.2021.11.71` gives *J. Software for Algebra and Geometry* **11**, 71–81, issued
   2021-12-31. The 2026-09-14 provenance question in `CITATIONS-TO-VERIFY.md` is closed.

---

## A. Primary source held — quoted

### 1. Kozlov (1997) — `Kozlov1997`

**Citation:** D. N. Kozlov, *Convex hulls of f- and β-vectors*, Discrete & Computational
Geometry **18** (1997), 421–431. mrnumber 1476604 in the `.bib`.

**Claims supported:** `.org:176` (the simplex "Kozlov proved … to be the convex hull of the
f-vectors of simplicial complexes on n vertices"), `.org:222`, and the restatement as the
article's own starting point, `.org:762` (`[cite/t:@Kozlov1997 Theorem 4.1]`).

**Quotation** (held PDF, §4): "Theorem 4.1. The convex hull of the set of f-vectors of
simplicial complexes on n vertices is given by conv{F̃₁, F̃₂, …, F̃ₙ}." The paper also carries a
second, direct proof: "5. A Direct Proof of Theorem 4.1".

### 2. Linusson (1999) — `Linusson1999`

**Citation:** S. Linusson, *The number of M-sequences and f-vectors*, Combinatorica **19**
(1999), 255–266.

**Claim supported:** `.org:221` — "*Linusson* counts it" (the set of f-vectors).

**Quotation** (held PDF, abstract): "We give a recursive formula for the number of M-sequences
(a.k.a. f-vectors for multicomplexes or O-sequences) given the number of variables and a maximum
degree. … The recursive formula is generalized to the number of f-vectors …".

### 3. Amata & Crupi (2020) — `AmataCrupi2020`

**Citation:** L. Amata, M. Crupi, *Hilbert functions of graded modules over an exterior algebra:
an algorithmic approach*, Int. Electron. J. Algebra **27** (2020), 271–287.

**Claims supported:** `.org:232` (the generalization of Kruskal–Katona to graded modules, jointly
with `AmataCrupi2020KK`), `.org:1080` (`[cite/t:@AmataCrupi2020 Definition 2.1]`, the definition
of monomial submodule the paper scopes to), `.org:1181` (initial submodules are monomial;
Hilbert-function invariance).

**Quotations** (held PDF): "Definition 2.1. A graded submodule M of F is a monomial submodule if
M is a submodule generated by monomials of F, i.e., M = I₁g₁ ⊕ ··· ⊕ Iᵣgᵣ" — the direct-sum
form the article's Definition cites verbatim. Abstract: "…the existence of the unique
lexicographic submodule of F with the same Hilbert function as M is proved by a new algorithmic
approach. Such an approach allows us to establish a criterion for determining if a sequence of
nonnegative integers defines the Hilbert function of a quotient of a free E-module only via the
combinatorial Kruskal–Katona's theorem."

### 4. Amata & Crupi (2020) — `AmataCrupi2020KK`

**Citation:** L. Amata, M. Crupi, *A generalization of Kruskal–Katona's theorem*, An. Şt. Univ.
Ovidius Constanţa **28**(2) (2020), 35–51, DOI 10.2478/auom-2020-0018.

**Claim supported:** `.org:232` and `.org:1181`, as above.

**Quotation** (held PDF, first page): title and DOI as cited; "Kruskal proved a theorem on
bounding the f-vectors of simplicial complexes in a way similar to Macaulay's theorem [18].
Katona independently proved …" — the paper's own framing of what it generalizes.

### 5. Aramova, Herzog & Hibi (1997) — `AramovaHerzogHibi1997`

**Citation:** A. Aramova, J. Herzog, T. Hibi, *Gotzmann theorems for exterior algebras and
combinatorics*, J. Algebra **191** (1997), 174–211.

**Claims supported:** `.org:488` (background list of `thm-invariance`) and `.org:619` — the
Kruskal–Katona theorem "in this form [cite/t:@AramovaHerzogHibi1997 Theorem 4.1]".

**Quotation** (held PDF; `pdftotext` renders `[nn]` as `wnnx` and parentheses as `Ž.`):
"THEOREM 4.1. Let (h₁, …, hₙ) be a sequence of integers. Then the following conditions are
equivalent: (a) 1 + Σⁿᵢ₌₁ hᵢtⁱ is the Hilbert series of a graded K-algebra E/I;
(b) 0 ≤ h_{i+1} ≤ h_i^{(i)}, 0 < i ≤ n−1." — exactly the algebraic form the article states.

### 6. Sköldberg (1999) — `Skoldberg1999`

**Citation:** E. Sköldberg, *Monomial Golod quotients of exterior algebras*, J. Algebra
**218**(1) (1999), 183–189.

**Claim supported:** `.org:596` — Sköldberg "proves that the latter two [the exterior face ring
and the artinified Stanley–Reisner ring] have identical Hilbert functions and, more strongly,
that their module categories are equivalent by an explicit sign-twisting functor commuting with
Ext."

**Quotation** (held PDF, p. 186–187): the functor F is defined by "xᵢ ∘ m = (−1)^{Σ_{j<i} αⱼ}
xᵢm" on a module with "the same underlying k-space", and "PROPOSITION 1. The functors F and G
defined above are additive, exact, mutually quasi-inverse equivalences of categories that commute
with Exts." Same underlying k-space + multidegree-preserving gives the Hilbert-function identity
the article states.

### 7. Kupreyeva (2019) — `Kupreyeva2019`

**Citation:** Aliaksandra Kupreyeva, *Simplices of f-vectors*, Bachelor's thesis
LiTH-MAT-EX--2019/05--SE, Linköpings universitet, 2019 (advised by Jan Snellman; DiVA:
urn:nbn:se:liu:diva-159826).

**Claim supported:** `.org:1039` — `[cite/t:@Kupreyeva2019 Figure 3.1]`: "it draws conv(F₇³),
the hull truncated at cardinality …".

**Quotation** (held PDF): "The process is shown in Figure 3.1 for T₇³ = conv(F₇³) ∋ (p, x, y) ↦
(x, y). Red crosses correspond to the f-vectors and green dots are the other lattice points that
T₇³ contains." with the figure captioned "Figure 3.1: T₇³".

### 8–9. The two Macaulay2 package papers — `AmataCrupi2018ExteriorIdeals`, `AmataCrupi2021`

**Citations:** L. Amata, M. Crupi, *ExteriorIdeals: a package for computing monomial ideals in an
exterior algebra*, J. Softw. Algebra Geom. **8** (2018); and *ExteriorModules: a package for
computing monomial modules over an exterior algebra*, J. Softw. Algebra Geom. **11** (2021),
71–81, DOI 10.2140/jsag.2021.11.71.

**Claims supported:** `.org:2192` and `.org:3164` — the Methods section's software list.

**Held:** both PDFs, headed "Journal of Software for Algebra and Geometry" with the titles as
cited. `ExteriorIdeals` 1.1 is also JSAG-certified and ships with Macaulay2 (the package source
in the working repository's `code/` carries the JSAG certification block). Year of the second:
see finding 5 above.

### 10. Ziegler (1995) — `Ziegler1995` *(held in the private library, not in `literature/`)*

**Citation:** G. M. Ziegler, *Lectures on Polytopes*, Graduate Texts in Mathematics 152,
Springer, 1995.

**Claim supported:** `.org:2483` — `rem-no-support-functions`, naming the usual proof route that
the paper deliberately avoids: "the face of ΣPₚ exposed by φ is Σₚ F(φ, Pₚ), which follows from
[Ziegler Prop. 7.12], the common-refinement description of the normal fan of a Minkowski sum".

**Quotation** (Lecture 7, p. 198 of the copy checked): "Proposition 7.12. The normal fan of a
Minkowski sum is the common refinement of the individual fans: N(P + P′) = N(P) ∧ N(P′)." —
preceded by "Here we work out only the case of two summands, as the extension to more summands is
then obvious." The face-decomposition identity the article quotes is the standard immediate
consequence; the article's wording was adjusted on 2026-09-20 from "is" to "follows from"
(finding 4). *Provenance note:* the book is commercially published; the copy consulted lives in
Jan's private NAS reference library, outside this repository and outside the open-access-only
`literature/` corpus, per the workspace's standing convention.

### 11. Herzog & Hibi (2011) — `HerzogHibi2011` *(held in the private library, not in `literature/`)*

**Citation:** J. Herzog, T. Hibi, *Monomial Ideals*, Graduate Texts in Mathematics 260, Springer,
2011, DOI 10.1007/978-0-85729-106-6.

**Claim supported:** `.org:488` — standard-background list of `thm-invariance` (Hilbert-function
invariance under initial/generic-initial submodules).

**Quotation** (copy checked 2026-09-20): "Corollary 6.1.5. Let I ⊂ S be a graded ideal and < a
monomial order on S. Then S/I and S/in<(I) have the same Hilbert function, i.e. H(S/I, i) =
H(S/in<(I), i) for all i." Chapter 4 ("generic initial ideals … together with their complete
proofs", per the book's own introduction) covers the gin half. Same provenance note as entry 10.

---

## B. No primary copy held — bibliographic data independently verified

### 12. Kruskal (1963) — `Kruskal1963`

**Citation:** J. B. Kruskal, *The number of simplices in a complex*, in: Mathematical
Optimization Techniques, Univ. of California Press, Berkeley–Los Angeles, 1963, 251–278.

**Claim supported:** `.org:618` — one half of the Kruskal–Katona attribution for `thm-kk`.

**Verification:** MathSciNet MR0154827 (27 #4771), Jan's lookup 2026-09-14: title, pages,
publisher and year all match as recorded. MathSciNet names no editor, so the folklore "ed. R.
Bellman" remains unasserted in the `.bib`. No copy held; historical attribution only.

### 13. Katona (1968) — `Katona1968`

**Citation (as corrected):** G. O. H. Katona, *A theorem of finite sets*, in: Theory of Graphs
(Proc. Colloq., Tihany, 1966), Academic Press, New York–London, 1968, 187–207.

**Claim supported:** `.org:618`, as above.

**Verification:** MathSciNet MR0290982 (45 #76), Jan's lookup 2026-09-14 — which *corrected* the
previously recorded pagination; see finding 1. No copy held.

### 14. Clements & Lindström (1969) — `ClementsLindstroem1969`

**Citation:** G. F. Clements, B. Lindström, *A generalization of a combinatorial theorem of
Macaulay*, J. Combinatorial Theory **7** (1969), 230–238.

**Claim supported:** `.org:618` — third member of the `thm-kk` attribution (its theorem
specializes to the squarefree Kruskal–Katona statement at k_i = 1); it replaced the removed
Schützenberger reference (finding 2).

**Verification:** MathSciNet MR0246781 (40 #50), checked by Jan 2026-09-14 (recorded in the
`.bib`'s annotation of the same date). No copy held.

### 15–17. The local-LYM trio — `Yamamoto1954`, `Meshalkin1963`, `Lubell1966`

**Citations:** K. Yamamoto, *Logarithmic order of free distributive lattice*, J. Math. Soc.
Japan **6** (1954), 343–353, DOI 10.2969/jmsj/00630343. — L. D. Meshalkin, *Generalization of
Sperner's theorem on the number of subsets of a finite set*, Theory Probab. Appl. **8**(2)
(1963), 203–204, DOI 10.1137/1108023. — D. Lubell, *A short proof of Sperner's lemma*,
J. Combinatorial Theory **1**(2) (1966), 299, DOI 10.1016/S0021-9800(66)80035-2.

**Claim supported:** `.org:658` — "The three are Daniel Lubell, Koichi Yamamoto and Lev
Meshalkin, who proved the global form independently between 1954 and 1966." Historical
attribution of the (global) LYM inequality; the article *uses* only the local form, which it
takes from the literature as standard and which is also machine-checked (Mathlib's
`Finset.card_div_choose_le_card_shadow_div_choose`, see `lean/Spine/LYM.lean`).

**Verification:** Yamamoto and Lubell against OpenAlex (2026-09-08; W2084913436, W2073286344 —
both DOIs resolve in the recorded form; Lubell's famous single page 299 confirmed). Meshalkin
against Crossref (2026-09-20, finding 3). The Russian original (Teor. Verojatnost. i Primenen.
**8**, 219–220, per Jan's MathSciNet lookup) is kept in the `.bib` as `Meshalkin1963ru`,
deliberately uncited — the article cites the English translation. No copies held; the
independence-and-dates claim is the standard history (each paper's venue and year as verified
are consistent with it: 1954, 1963, 1966, three journals, three authors).

### 18. Aramova & Herzog (2000) — `AramovaHerzog2000`

**Citation:** A. Aramova, J. Herzog, *Almost regular sequences and Betti numbers*, Amer. J.
Math. **122**(4) (2000), 689–719, DOI 10.1353/ajm.2000.0025.

**Claim supported:** `.org:488` — background list of `thm-invariance`.

**Verification:** DOI recorded and resolving; listed in `CITATIONS-TO-VERIFY.md` as the one
no-copy reference most worth actually *obtaining* (it supports a theorem rather than history);
still not held as of this writing. The invariance statement it is cited for is independently
covered by entries 5 and 11, both quoted above.

### 19. Eisenbud (1995) — `Eisenbud1995`

**Citation:** D. Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, GTM 150,
Springer, 1995, DOI 10.1007/978-1-4612-5350-1.

**Claim supported:** `.org:488` — background list of `thm-invariance`, cited as "Ch. 15".

**Verification:** MathSciNet MR1322960; commercial textbook, no copy held anywhere reachable
(checked the private library too, 2026-09-20). **The chapter-level pointer "Ch. 15" is therefore
the one locator in this article not verified against a primary copy** — flagged rather than
silently trusted. (It is cited alongside three other references for the same standard fact, two
of them quoted in this certificate, so the claim itself is covered.)

### 20–21. Software — `SageMath`, `Macaulay2`

**Citations:** the SageMath and Macaulay2 systems, cited in the form each project's own
publication-citation page requests, with the versions actually used recorded in the article's
Methods section (`.org:2192`, `.org:3164`).

**Verification:** not bibliographic claims in the hallucination-relevant sense; both systems'
recommended citation forms were followed (the `.bib` notes the SageMath wiki's recommendation
explicitly), and every computational claim they back is indexed, script by script, in the
article's §10 and reproducible from `verification-code/`.

---

*Prepared 2026-09-20 on jts-pc. Every quotation in section A was extracted from the named PDF
during the preparation of this document and re-read against its context once before the file was
finalized. Nothing in this document was supplied from memory of the cited works.*
