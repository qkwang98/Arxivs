# A positive-certificate proof of permanental dominance for (4,4,3,3)

Date: 2026-09-10.

## Result and verification status

This note gives a proof, by an explicit positive rational certificate, of

\[
\frac{d_{(4,4,3,3)}(A)}{12012}\le\operatorname{per}A
\]

for every complex Hermitian positive semidefinite matrix of order fourteen.
There is no rank, spectrum, support, or reality restriction. The proof invokes
previously established permanental dominance only for the four partitions
\((6,5,3),(6,4,4),(5,5,4),(5,3,3,3)\).

The certificate's exact finite identities have been regenerated and checked
in two Young representation bases. Separate literal character-sum checks at
small orders and an exact complex rank-thirteen stress test also passed.
These are local computational checks, not external peer review or a
proof-assistant formalization. The arbitrary-PSD implication is proved below;
it is not inferred from numerical tests. The new inequality and certificate
have not been externally reviewed.

The proof is independent of the previous rank-seven, spectral-buffer,
KKT, moment, and special-family results. In particular, their exact route
obstructions are not premises that need to be bypassed algebraically.

## 1. Notation and the bridge theorem

For a partition \(\nu\vdash n\), let \(\chi^\nu\) be its ordinary irreducible
character, \(f^\nu=\chi^\nu(e)\), and

\[
d_\nu(A)=\sum_{\sigma\in S_n}\chi^\nu(\sigma)
                   \prod_{i=1}^n a_{i,\sigma(i)},
\qquad \bar d_\nu=d_\nu/f^\nu.
\]

There is no normalization by \(n!\) in \(d_\nu\).

**Theorem 1 (bridge inequality).** For every Hermitian PSD matrix
\(A\in M_{14}(\mathbb C)\),

\[
\boxed{\begin{aligned}
59512\,d_{(4,4,3,3)}(A)\ \le\;&4035\,d_{(6,5,3)}(A)
 +6725\,d_{(6,4,4)}(A)\\
&+39759\,d_{(5,5,4)}(A)
 +23636\,d_{(5,3,3,3)}(A).
\end{aligned}}\tag{1.1}
\]

The hook formula gives

\[
(f^{4433},f^{653},f^{644},f^{554},f^{5333})
=(12012,15015,9009,6006,15015).
\]

Consequently (1.1) is exactly the convex inequality

\[
\boxed{\bar d_{4433}\le
\frac{20175}{238048}\bar d_{653}
+\frac{20175}{238048}\bar d_{644}
+\frac{79518}{238048}\bar d_{554}
+\frac{118180}{238048}\bar d_{5333}.}\tag{1.2}
\]

All four weights are positive and their sum is one. Subscripts written
without commas in these displays abbreviate the explicitly stated partitions.

**Corollary 2.** Permanental dominance holds for \((4,4,3,3)\), and hence
for all ordinary immanants of order at most fourteen.

**Proof of the corollary.** The established Pate theorem covers partitions
with at most three parts exceeding two, and also those with four such parts
whose second and third parts agree. Thus all four terms on the right of
(1.2) are bounded above by \(\operatorname{per}A\). Equation (1.2) proves
the target. All other order-fourteen partitions were already covered by
that theorem. This is only the ordinary symmetric-group immanant statement:
it is not the all-orders, all-subgroup version of Lieb's conjecture. \(\square\)

Pate's coverage theorem is explicitly reproduced as Theorem 3.1 of
Divya--Somasundaram [2]; its applicability to complex Hermitian PSD matrices
is part of that paper's definition of the problem. See also [1,3].

The rest of the note proves Theorem 1 without using any permanental-dominance
assumption.

## 2. A family of universally nonnegative immanant forms

### 2.1 Projectors and a partially transposed swap

Fix \(n\), take \(d=n\), and work on
\(\mathcal H=(\mathbb C^d)^{\otimes n}\). Let \(U_\sigma\) permute tensor
factors by

\[
U_\sigma(v_1\otimes\cdots\otimes v_n)
=v_{\sigma^{-1}(1)}\otimes\cdots\otimes v_{\sigma^{-1}(n)}.
\]

For \(I\subseteq[n]\) and \(\alpha\vdash|I|\), write

\[
P_\alpha^I=\frac{f^\alpha}{|I|!}
\sum_{\sigma\in S_I}\chi^\alpha(\sigma^{-1})U_\sigma.
\tag{2.1}
\]

This is an orthogonal projector. In the standard tensor basis it is real
and symmetric. Projectors for nested symmetric groups commute when the
larger projector is central in the larger group; projectors on disjoint
factor sets also commute.

Choose \(k\in\{1,2\}\) and split the factor indices into

\[
O=[n-2k],\quad L=\{n-2k+1,\ldots,n-k\},\quad
R=\{n-k+1,\ldots,n\}.
\]

Let \(\eta\vdash n-2k\), \(\mu\vdash n-k\), and set

\[
P=P_\eta^O,\qquad Q=P_\mu^{O\cup L}.
\]

For \(k=1\), put \(B=I\). For \(k=2\), choose
\(\varepsilon\in\{+1,-1\}\) and put

\[
B=\tfrac12\bigl(I+\varepsilon U_{(n-1,n)}\bigr).
\tag{2.2}
\]

Thus \(B\) is the symmetric or alternating projector on the last two
factors. The three projectors \(P,Q,B\) commute.

Let

\[
\tau_k=\prod_{a=1}^{k}(n-2k+a,\ n-k+a),
\]

and let \(\Gamma_R\) denote partial transpose on all factors in \(R\).
The elementary identity

\[
\left(U_{(a,b)}\right)^{\Gamma_b}
=|\Omega\rangle\langle\Omega|_{ab},
\qquad |\Omega\rangle=\sum_{j=1}^{d}e_j\otimes e_j,
\tag{2.3}
\]

shows that

\[
E=U_{\tau_k}^{\Gamma_R}\succeq0.
\]

The \(k\) pairs are disjoint, so \(E\) is a tensor product of the positive
operators in (2.3), with the identity on \(O\). In particular \(P\)
commutes with \(E\), and \(PE\succeq0\).

Define

\[
Y=QB\,PE\,BQ\succeq0.
\tag{2.4}
\]

The local sandwich rule for partial transpose gives

\[
\boxed{W:=Y^{\Gamma_R}=QB\,P U_{\tau_k}\,BQ.}\tag{2.5}
\]

For precision, this is *not* an application of a nonexistent multiplicative
rule for partial transpose. Relative to \((O\cup L)|R\), \(Q\) is local
on the first side and \(B\) is local on the second. The identity being used is

\[
[(C\otimes D)X(C\otimes D)]^{\Gamma_R}
=(C\otimes D^T)X^{\Gamma_R}(C\otimes D^T),
\]

with \(C=Q\), \(D=B\), \(B^T=B\), and
\((PE)^{\Gamma_R}=P U_{\tau_k}\).

For a fully decomposable tensor \(v=v_1\otimes\cdots\otimes v_n\),
partial-transpose duality gives

\[
\langle v,Wv\rangle
=\langle v_{O\cup L}\otimes\overline{v_R},
Y(v_{O\cup L}\otimes\overline{v_R})\rangle\ge0.
\tag{2.6}
\]

The operator \(W\) need not be PSD on all tensors. Its nonnegativity on
fully decomposable tensors, established by (2.6), is exactly what is needed.

### 2.2 Central averaging and character coefficients

Average over conjugation by the entire symmetric group:

\[
\mathcal Z(W)=\frac1{n!}\sum_{\pi\in S_n}U_\pi WU_\pi^{-1}.
\]

Every summand has nonnegative expectation on every fully decomposable tensor,
because permutations preserve decomposability. The central group-algebra
element \(\mathcal Z(W)\) acts on the \(\nu\)-isotypic summand by

\[
\frac{\operatorname{Tr}_{V^\nu}\rho_\nu(W)}{f^\nu}.
\]

For a Gram matrix \(A=(\langle v_i,v_j\rangle)\), the usual central-projector
identity is

\[
\langle v,P_\nu^{[n]}v\rangle=\frac{f^\nu}{n!}d_\nu(A).
\tag{2.7}
\]

It follows that

\[
0\le\langle v,\mathcal Z(W)v\rangle
=\frac1{n!}\sum_{\nu\vdash n}
       \operatorname{Tr}_{V^\nu}\rho_\nu(W)\,d_\nu(A).
\tag{2.8}
\]

Since the projectors commute and are idempotent, cyclicity of trace reduces
\(\operatorname{Tr}\rho_\nu(QBP U_{\tau_k}BQ)\) to
\(\operatorname{Tr}\rho_\nu(QBP U_{\tau_k})\).
Restriction to \(S_{n-2k}\) decomposes the selected \(\eta\)-summand into
\(f^\eta\) identical copies of a skew-tableau multiplicity space. Therefore

\[
\operatorname{Tr}_{V^\nu}\rho_\nu(W)
=f^\eta t_{\eta,\mu,\varepsilon}^{\nu},
\tag{2.9}
\]

where the coefficient \(t\) is the multiplicity-space trace described in
the next section. Equations (2.8)--(2.9) prove the following lemma.

**Lemma 3 (partial-transpose witness).** For every choice of the indicated
parameters and every complex Hermitian PSD Gram matrix,

\[
\boxed{L_{k,\eta,\mu,\varepsilon}(A):=
\sum_{\nu\vdash n}t_{\eta,\mu,\varepsilon}^{\nu}d_\nu(A)\ge0.}
\tag{2.10}
\]

For \(k=1\), the parameter \(\varepsilon\) is omitted. No permanental
upper bound for any immanant has been used in this lemma.

## 3. Exact computation of the witness coefficients

The branching multiplicity space in (2.9) has a basis indexed by standard
skew tableaux \(T\) of shape \(\nu/\eta\), with \(2k\) boxes. Equivalently,
these are chains from \(\eta\) to \(\nu\) in the Young graph. Let
\(D_\mu\) be the diagonal projector selecting chains whose shape after the
first \(k\) added boxes is \(\mu\).

Number the added boxes \(1,\ldots,2k\) in tableau order, and let
\(a_i\) be the column-minus-row content of box \(i\). In Young's orthogonal
form, the adjacent transposition \(s_i\) has diagonal entry

\[
(S_i)_{T,T}=\frac1{a_{i+1}-a_i}.
\]

When interchanging \(i,i+1\) gives another standard tableau \(T'\),

\[
(S_i)_{T',T}=\sqrt{1-\frac1{(a_{i+1}-a_i)^2}};
\]

otherwise there is no off-diagonal entry. The rational seminormal form has
the same diagonal and off-diagonal entry
\(1+1/(a_{i+1}-a_i)\) in the corresponding basis convention. These are
standard realizations of symmetric-group irreducibles; see [4].

For \(k=1\),

\[
t_{\eta,\mu}^{\nu}=\operatorname{tr}(D_\mu S_1).
\tag{3.1}
\]

For \(k=2\), the pair swap is \(\tau_2=s_2s_1s_3s_2\), and

\[
\boxed{t_{\eta,\mu,\varepsilon}^{\nu}
=\frac12\operatorname{tr}
\left[D_\mu(I+\varepsilon S_3)S_2S_1S_3S_2\right].}\tag{3.2}
\]

At most \(4!=24\) tableaux occur in any of these trace calculations.
Thus (3.1)--(3.2) are small, explicit algebraic calculations, not a
numerical semidefinite-programming assertion. Every coefficient below is
rational. The accompanying verifier checks all coefficients independently
in both displayed representation forms. Square roots along every closed
walk in the orthogonal calculation simplify to exact rational numbers;
the verifier tests that the radicands are perfect rational squares.

## 4. The twenty-term positive certificate

Use the following parameters and positive weights. In the table, each
\(L_j\) means the witness (2.10) with the displayed parameters; a dash
means the irrelevant \(k=1\) sign parameter.

| j | k | eta | mu | epsilon | positive weight w_j |
|---:|---:|---|---|:---:|---:|
| 1 | 1 | (4,4,3,1) | (5,4,3,1) | — | 1251 |
| 2 | 1 | (4,3,3,1,1) | (4,4,3,1,1) | — | 151889/10 |
| 3 | 1 | (3,3,3,3) | (4,3,3,3) | — | 33602 |
| 4 | 1 | (4,3,3,2) | (4,3,3,2,1) | — | 71276273/64925 |
| 5 | 1 | (4,3,2,2,1) | (4,3,3,2,1) | — | 47246294/9275 |
| 6 | 1 | (3,3,3,2,1) | (4,3,3,2,1) | — | 340767671/194775 |
| 7 | 1 | (4,3,3,1,1) | (4,3,3,1,1,1) | — | 6526677/67840 |
| 8 | 1 | (4,3,2,1,1,1) | (4,3,3,1,1,1) | — | 19283/50 |
| 9 | 1 | (3,3,3,1,1,1) | (4,3,3,1,1,1) | — | 54404623/339200 |
| 10 | 1 | (3,3,3,3) | (3,3,3,3,1) | — | 163/795 |
| 11 | 1 | (3,3,2,2,2) | (3,3,3,2,2) | — | 1793/3180 |
| 12 | 1 | (3,3,3,2,1) | (3,3,3,2,1,1) | — | 326/3975 |
| 13 | 2 | (5,3,2) | (5,4,3) | -1 | 20175 |
| 14 | 2 | (4,3,3) | (4,4,3,1) | 1 | 11956 |
| 15 | 2 | (4,3,3) | (4,4,4) | -1 | 58752 |
| 16 | 2 | (4,3,2,1) | (4,4,3,1) | -1 | 31904 |
| 17 | 2 | (4,2,2,2) | (4,3,3,2) | -1 | 19932 |
| 18 | 2 | (4,2,2,1,1) | (4,3,3,1,1) | -1 | 80251/30 |
| 19 | 2 | (3,3,2,1,1) | (3,3,3,1,1,1) | 1 | 489/5300 |
| 20 | 2 | (3,2,2,2,1) | (3,3,3,2,1) | -1 | 1141/2120 |

Exact substitution of (3.1)--(3.2) gives

\[
\boxed{\begin{aligned}
\sum_{j=1}^{20}w_j L_j(A)
={}&4035d_{653}(A)+6725d_{644}(A)+39759d_{554}(A)\\
&+23636d_{5333}(A)-59512d_{4433}(A).
\end{aligned}}\tag{4.1}
\]

This equality is coefficientwise on **all 135 irreducible characters of
\(S_{14}\)**; all coefficients other than these five cancel exactly.
The complete expanded rows are printed in Appendix A and stored in
`certificate.json`.

Each \(w_j>0\), and each \(L_j(A)\ge0\) by Lemma 3. Therefore the right
side of (4.1) is nonnegative for every PSD matrix. This proves Theorem 1.
Together with Corollary 2, it completes the target proof. \(\square\)

An elementary normalization audit is

\[
\begin{aligned}
59512\cdot12012
={}&4035\cdot15015+6725\cdot9009\\
 &+39759\cdot6006+23636\cdot15015.
\end{aligned}
\]

Thus the bridge is an equality on diagonal matrices, as it must be. No
strict inequality is claimed on the entire PSD cone.

## 5. Coverage, assumptions, and non-circularity

Every PSD matrix of order fourteen is a Gram matrix in \(\mathbb C^{14}\).
The tensor proof therefore includes full rank, singular matrices, arbitrary
complex phases, and zero Gram vectors. No division by a matrix entry,
determinant, permanent, or eigenvalue is used. In particular, zero diagonal
entries cause no exception.

The only imported PDC theorems appear in Corollary 2, *after* the universal
bridge inequality has been proved. They concern four known partitions,
never the target \((4,4,3,3)\). The partial-transpose witness lemma itself
uses only orthogonal projectors, the PSD operator (2.3), tensor-product
expectations, and finite-group representation identities.

The route is not the previously obstructed cone of Young permutation
characters with block-merging or majorization inequalities. Its generators
are instead central averages of partially transposed PSD operators. It
also does not assume an operator ordering between different central
projectors, nor the false permanent-on-top conjecture. Nonnegativity is
asserted only on decomposable Gram tensors, which is proved in (2.6).

This proof closes the specified order-fourteen ordinary-immanant case.
It does **not** prove Lieb's conjecture for all matrix orders or all
subgroup characters.

## 6. Reproducibility and actual audit scope

Run from this directory with Python 3:

```
python verify_all.py
```

All checks use only the Python standard library. No optimizer, floating-point
arithmetic, network access, or optional package is required for verification.

`verify_certificate.py` regenerates all twenty coefficient rows from skew
Young tableaux rather than trusting the stored row values. It does this in
both rational seminormal form and orthogonal form with exact square-root
simplification. It checks the positive rational weights, cancellation on
all 135 partitions, all five character degrees, and the final normalized
convex weights. It also enumerates all order-fourteen partitions to confirm
that the imported Pate coverage criterion leaves only the target.

`adversarial_exact_checks.py` independently computes ordinary character
values using the Murnaghan--Nakayama rule. Literal group-algebra character
sums reproduce the small-order witness traces for \((n,k)=(4,1),(4,2),
(5,2),(6,2)\). A separate complex rank-thirteen PSD example tests all twenty
witnesses and the bridge using exact Gaussian-integer monomials. The example
is a connected fan of PSD triangles, each with eigenvalues
\(0,3-\sqrt3,3+\sqrt3\); their common kernel is exactly the constants.
The example has two-vertex-connected, phase-frustrated support. These tests
are additional failure checks, not a substitute for Lemma 3's proof on all
Gram tensors.

`operator_identity_checks.py` separately checks the partial-transpose
sandwich and the product-tensor expectation identity in a small exact
complex tensor model. It uses a local *complex* Hermitian projector to make
conjugation and transpose mistakes detectable.

The finite coefficient certificate was discovered computationally, then
reconstructed with exact rational arithmetic. The analytic argument and
finite identities were checked locally by separate mathematical derivations
and code paths. There was no external mathematician audit, no parallel
independent-agent audit, and no Lean/Isabelle formalization during this run.
A peer-review or formalization claim is not being made.

## References

[1] T. H. Pate, *Tensor inequalities, xi-functions and inequalities involving
immanants*, Linear Algebra and its Applications **295** (1999), 31--59.
DOI: https://doi.org/10.1016/S0024-3795(99)00035-X.
The imported coverage theorem is reproduced explicitly in [2, Theorem 3.1].

[2] K. U. Divya and K. Somasundaram, *Permanent dominance conjecture for
derived partitions*, Bulletin of the Institute of Combinatorics and its
Applications **95** (2022), 84--92. Relevant pages: 86 and 88.
https://bica.the-ica.org/Volumes/95/Reprints/BICA2021-24-Reprint.pdf.

[3] I. M. Wanless, *Lieb's permanental dominance conjecture*, arXiv:2202.01867
(2022), also DOI 10.4171/90-2/48.
https://arxiv.org/abs/2202.01867.

[4] D. Grinko, A. Burchardt, and M. Ozols, *Gelfand--Tsetlin basis for
partially transposed permutations, with applications to quantum information*,
arXiv:2310.02252. The ordinary Young orthogonal and seminormal forms and the
partially transposed swap identity are standard background; the certificate
in this note is derived separately.
https://arxiv.org/abs/2310.02252.

## Appendix A. All expanded witness forms

In this appendix \(d_{a_1,\ldots,a_\ell}\) always means the **unnormalized**
immanant for partition \((a_1,\ldots,a_\ell)\). Each form below is
nonnegative on every complex Hermitian PSD matrix of order fourteen by
Lemma 3. Terms absent from a row have coefficient zero.

### Witness 1

\[
\begin{aligned}
L_{1}={}&d_{6,4,3,1} -d_{5,5,3,1} -\frac{1}{3}d_{5,4,4,1}\\
&-\frac{1}{6}d_{5,4,3,2} -\frac{1}{8}d_{5,4,3,1,1}
\end{aligned}
\]

### Witness 2

\[
\begin{aligned}
L_{2}={}&\frac{1}{2}d_{5,4,3,1,1} -d_{4,4,4,1,1} -\frac{1}{4}d_{4,4,3,2,1}\\
&-\frac{1}{7}d_{4,4,3,1,1,1}
\end{aligned}
\]

### Witness 3

\[
\begin{aligned}
L_{3}={}&d_{5,3,3,3} -d_{4,4,3,3} -\frac{1}{7}d_{4,3,3,3,1}
\end{aligned}
\]

### Witness 4

\[
\begin{aligned}
L_{4}={}&\frac{1}{8}d_{5,3,3,2,1} +\frac{1}{6}d_{4,4,3,2,1} +\frac{1}{3}d_{4,3,3,3,1}\\
&+d_{4,3,3,2,2} -d_{4,3,3,2,1,1}
\end{aligned}
\]

### Witness 5

\[
\begin{aligned}
L_{5}={}&\frac{1}{4}d_{5,3,3,2,1} +\frac{1}{2}d_{4,4,3,2,1} -d_{4,3,3,3,1}\\
&-\frac{1}{3}d_{4,3,3,2,2} -\frac{1}{5}d_{4,3,3,2,1,1}
\end{aligned}
\]

### Witness 6

\[
\begin{aligned}
L_{6}={}&d_{5,3,3,2,1} -d_{4,4,3,2,1} -\frac{1}{4}d_{4,3,3,3,1}\\
&-\frac{1}{6}d_{4,3,3,2,2} -\frac{1}{8}d_{4,3,3,2,1,1}
\end{aligned}
\]

### Witness 7

\[
\begin{aligned}
L_{7}={}&\frac{1}{9}d_{5,3,3,1,1,1} +\frac{1}{7}d_{4,4,3,1,1,1} +\frac{1}{3}d_{4,3,3,2,1,1}\\
&-d_{4,3,3,1,1,1,1}
\end{aligned}
\]

### Witness 8

\[
\begin{aligned}
L_{8}={}&\frac{1}{4}d_{5,3,3,1,1,1} +\frac{1}{2}d_{4,4,3,1,1,1} -\frac{1}{2}d_{4,3,3,2,1,1}\\
&-\frac{1}{6}d_{4,3,3,1,1,1,1}
\end{aligned}
\]

### Witness 9

\[
\begin{aligned}
L_{9}={}&d_{5,3,3,1,1,1} -d_{4,4,3,1,1,1} -\frac{1}{5}d_{4,3,3,2,1,1}\\
&-\frac{1}{9}d_{4,3,3,1,1,1,1}
\end{aligned}
\]

### Witness 10

\[
\begin{aligned}
L_{10}={}&\frac{1}{7}d_{4,3,3,3,1} +d_{3,3,3,3,2} -d_{3,3,3,3,1,1}
\end{aligned}
\]

### Witness 11

\[
\begin{aligned}
L_{11}={}&\frac{1}{3}d_{4,3,3,2,2} -d_{3,3,3,3,2} -\frac{1}{5}d_{3,3,3,2,2,1}
\end{aligned}
\]

### Witness 12

\[
\begin{aligned}
L_{12}={}&\frac{1}{8}d_{4,3,3,2,1,1} +\frac{1}{4}d_{3,3,3,3,1,1} +\frac{1}{2}d_{3,3,3,2,2,1}\\
&-d_{3,3,3,2,1,1,1}
\end{aligned}
\]

### Witness 13

\[
\begin{aligned}
L_{13}={}&\frac{2}{15}d_{5,4,3,1,1} -\frac{1}{5}d_{5,4,4,1} -\frac{11}{75}d_{6,4,3,1}\\
&-\frac{1}{3}d_{5,5,3,1} +\frac{1}{5}d_{6,5,3} +d_{5,5,4}\\
&+\frac{1}{3}d_{6,4,4}
\end{aligned}
\]

### Witness 14

\[
\begin{aligned}
L_{14}={}&-\frac{1}{2}d_{5,4,3,1,1} +d_{4,4,4,1,1} -\frac{1}{7}d_{5,4,4,1}\\
&-d_{4,4,4,2} +\frac{11}{28}d_{5,4,3,2} -\frac{1}{2}d_{4,4,3,3}\\
&+\frac{1}{7}d_{6,4,3,1} +\frac{1}{4}d_{4,4,3,2,1}
\end{aligned}
\]

### Witness 15

\[
\begin{aligned}
L_{15}={}&\frac{1}{10}d_{4,4,4,1,1} -\frac{1}{6}d_{5,4,4,1} +\frac{1}{3}d_{5,5,4}
\end{aligned}
\]

### Witness 16

\[
\begin{aligned}
L_{16}={}&\frac{1}{12}d_{4,4,3,1,1,1} -\frac{29}{192}d_{5,4,3,1,1} -\frac{1}{6}d_{4,4,4,1,1}\\
&+\frac{1}{2}d_{5,4,4,1} -\frac{1}{4}d_{4,4,4,2} -\frac{19}{64}d_{5,4,3,2}\\
&+\frac{1}{4}d_{5,5,3,1} +\frac{37}{192}d_{4,4,3,2,1}
\end{aligned}
\]

### Witness 17

\[
\begin{aligned}
L_{17}={}&\frac{1}{2}d_{4,3,3,3,1} -\frac{1}{2}d_{5,3,3,3} +d_{4,4,4,2}\\
&+\frac{1}{4}d_{5,4,3,2} -d_{4,4,3,3} +\frac{1}{10}d_{4,3,3,2,1,1}\\
&-\frac{1}{8}d_{5,3,3,2,1} -\frac{1}{4}d_{4,4,3,2,1}
\end{aligned}
\]

### Witness 18

\[
\begin{aligned}
L_{18}={}&-\frac{1}{5}d_{4,4,3,1,1,1} -\frac{1}{10}d_{5,3,3,1,1,1} +\frac{1}{4}d_{5,4,3,1,1}\\
&+\frac{1}{15}d_{4,3,3,1,1,1,1} +d_{4,4,4,1,1} +\frac{1}{3}d_{4,3,3,2,2}\\
&+\frac{1}{5}d_{4,3,3,2,1,1} -\frac{1}{4}d_{5,3,3,2,1} -\frac{1}{2}d_{4,4,3,2,1}
\end{aligned}
\]

### Witness 19

\[
\begin{aligned}
L_{19}={}&\frac{1}{12}d_{5,3,3,1,1,1} -\frac{1}{3}d_{4,3,3,1,1,1,1} -\frac{1}{3}d_{3,3,3,3,1,1}\\
&+\frac{1}{2}d_{3,3,3,2,1,1,1}
\end{aligned}
\]

### Witness 20

\[
\begin{aligned}
L_{20}={}&-\frac{2}{3}d_{4,3,3,3,1} +\frac{2}{15}d_{3,3,3,2,2,1} +\frac{2}{5}d_{3,3,3,3,1,1}\\
&-\frac{2}{9}d_{4,3,3,2,2} +\frac{2}{3}d_{3,3,3,3,2} +\frac{1}{15}d_{3,3,3,2,1,1,1}\\
&-\frac{2}{15}d_{4,3,3,2,1,1} +\frac{1}{3}d_{4,4,3,2,1}
\end{aligned}
\]

