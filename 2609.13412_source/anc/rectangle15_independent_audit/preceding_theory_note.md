# Partial-swap witnesses, a content formula, and an infinite immanant-dominance family

Research note and exact certificates — 11 September 2026

## Scope and status

The order-14 result for (4,4,3,3) is accepted as established input and is not reproved. The final proof and the twenty witness definitions referred to in the request were not present among the accessible files. Consequently, this note does not identify the original twenty-witness cone. It defines and investigates a specific, dimension-independent partial-swap construction, proves a general theorem for arbitrary local group-algebra filters, and completely enumerates its **central-projector** subcone at orders 14 and 15.

The main mathematical outputs are:

* A positivity theorem for arbitrary two-block Young/branching filters, with an explicit character-trace formula.
* A content-polynomial formula for every witness with one symmetric block.
* A uniform three-witness convex-dominance theorem for (m,4,3,3), for every integer m >= 6.
* An exact seven-witness bridge for (5,4,3,3), implying its PDC case.
* Exact additional three-row bridges at orders 16 and 17, and a separate exact order-17 certificate for (6,5,3,3).
* Exact finite generator matrices and rank certificates for the central-projector cones, and an integer separating functional excluding PDC for (3,3,3,3,3) from the order-15 cone.

These are mathematical proofs and exact certificates produced and checked in this run, not externally audited or Lean-formalized results. Publication priority for the new explicit consequences has not been established by an exhaustive literature review. The underlying tensor-contraction philosophy has important antecedents in Pate's work; it must not be advertised as an entirely new foundational principle.

## 1. Notation

For a partition lambda of n, let f^lambda = chi^lambda(e),

\[
d_\lambda(A)=\sum_{\sigma\in S_n}\chi^\lambda(\sigma)
                    \prod_{i=1}^n a_{i,\sigma(i)},
\qquad \bar d_\lambda=d_\lambda/f^\lambda.
\]

All matrices below are complex Hermitian positive semidefinite, including singular matrices. Let H be a finite-dimensional complex Hilbert space, let U be the unitary permutation representation on H^{tensor n}, and write x=x_1 tensor ... tensor x_n for a decomposable tensor with Gram matrix A. A consistent choice of the permutation convention gives

\[
\langle x,U(\sigma)x\rangle=\prod_i a_{i,\sigma(i)}.
\]

Using the inverse convention gives the same character sums. The central orthogonal idempotent is

\[
e_\nu=\frac{f^\nu}{n!}\sum_{\sigma\in S_n}
       \chi^\nu(\sigma^{-1})\sigma,
\quad
\langle x,U(e_\nu)x\rangle=\frac{f^\nu}{n!}d_\nu(A).
\]

For a box in row i and column j, its content is c=j-i. Put

\[
\kappa_\lambda=\sum_{b\in\lambda}c(b),
\qquad
\gamma_\lambda=\sum_{b\in\lambda}c(b)^2-\binom{|\lambda|}{2}.
\]

These are respectively the eigenvalues of the transposition class sum and the 3-cycle class sum.

## 2. General partial-swap positivity

### Theorem 1

Let n=p+q, let a in C[S_p] and b in C[S_q] be arbitrary, and let

\[
\tau_k=(1,p+1)\cdots(k,p+k),\qquad 1\le k\le\min(p,q).
\]

Embed a and b in the two disjoint blocks and set

\[
W=(a\otimes b)^*\tau_k(a\otimes b),
\qquad t_\nu=\operatorname{Tr}_{S^\nu}\rho_\nu(W).
\]

Then

\[
\sum_{\nu\vdash n}t_\nu d_\nu(A)\ge0.
\tag{1}
\]

This includes central Young projectors, orthogonal tableau projectors, branching-path projectors, and arbitrary local linear combinations of them. No positivity or idempotence assumption on a and b is needed.

### Proof

The filtered tensor has the form u tensor v across the two blocks. Split the coordinates of u and v into the k swapped factors and the remaining factors, writing u_{I,R} and v_{I,S}. Direct expansion gives

\[
\langle u\otimes v,U(\tau_k)(u\otimes v)\rangle
 =\sum_{R,S}\left|\sum_Iu_{I,R}\overline{v_{I,S}}\right|^2\ge0.
\tag{2}
\]

Equivalently this is Tr(R_u R_v), where R_u and R_v are the reduced positive semidefinite operators on the swapped factors. The contraction is linear in u and conjugate-linear in v.

Conjugating W by a permutation preserves its nonnegative expectation on decomposable tensors. Its central average is

\[
Z(W)=\frac1{n!}\sum_g gWg^{-1}
 =\sum_\nu\frac{t_\nu}{f^\nu}e_\nu.
\]

Therefore

\[
\langle x,U(Z(W))x\rangle
 =\frac1{n!}\sum_\nu t_\nu d_\nu(A)\ge0.
\]

Every complex PSD matrix has a Gram representation, proving (1), without any invertibility assumption. QED.

### Central-projector coefficients

For a=e_alpha and b=e_beta, with alpha of p and beta of q, cyclicity of trace gives

\[
t_\nu=\frac{f^\alpha f^\beta}{p!q!}
\sum_{\sigma\in S_p,\pi\in S_q}
\chi^\alpha(\sigma)\chi^\beta(\pi)
\chi^\nu((\sigma\oplus\pi)\tau_k).
\tag{3}
\]

Thus exact integer character computation suffices to generate a ray. The positive common prefactor is irrelevant for cone membership. Dividing the integer vector in (3) by the positive gcd of its entries gives the primitive raw-immanant vector used in the cone files.

For k >= 1 these central-projector witnesses are balanced:

\[
\sum_\nu f^\nu t_\nu=0.
\tag{4}
\]

Indeed, the left side is the regular-representation trace of W. By trace cyclicity it is the trace of tau_k(e_alpha tensor e_beta), whose identity coefficient is zero: tau_k is not in the block subgroup. In normalized coordinates, every generator therefore has coefficient sum zero.

### Why a naive linear squared norm cannot prove dominance

If a self-adjoint operator Q satisfies <x,Qx>=||Lx||^2 for one linear map L on the original tensor space and every product vector x, then Q=L*L. Product rank-one projectors span the Hermitian operators, so equality of their expectations determines the operator. Its central average has only nonnegative irreducible traces and yields no negative immanant coefficient.

The mixed conjugation in (2) is consequently essential. This observation does not contradict the established order-14 proof; it identifies information omitted by the informal phrase “a squared norm.”

## 3. A content-polynomial theorem for a symmetric block

For a horizontal p-strip nu/beta, define

\[
P_{\nu/\beta}(z)=\prod_{b\in\nu/\beta}(z+c(b)).
\]

Here “horizontal strip” means no two added boxes lie in the same column. Equivalently, nu_i >= beta_i >= nu_{i+1}. Let

\[
N^{\nu}_{p,\beta,k}
 =\frac1{(p-k)!}\sum_{j=0}^{p-k}
 (-1)^{p-k-j}\binom{p-k}{j}
 P_{\nu/\beta}(j-p+1),
\tag{5}
\]

and put N=0 when nu/beta is not a horizontal p-strip. These integers are the coefficients in the Newton expansion

\[
P_{\nu/\beta}(z)
 =\sum_{k=0}^{p}N^{\nu}_{p,\beta,k}(z+k)^{\overline{p-k}},
\tag{6}
\]

where u^{overline r}=u(u+1)...(u+r-1).

### Theorem 2: Pieri–content witnesses

For every beta of q and 1 <= k <= min(p,q),

\[
\Phi_{p,\beta,k}(A)
 :=\sum_{\nu\vdash p+q}N^{\nu}_{p,\beta,k}d_\nu(A)\ge0.
\tag{7}
\]

Moreover,

\[
\sum_\nu f^\nu N^{\nu}_{p,\beta,k}=0.
\tag{8}
\]

### Proof

Use the symmetric projector e_(p) on the p new labels and e_beta on q old labels. Pieri's rule says the corresponding subgroup type occurs with multiplicity one in S^nu precisely when nu/beta is horizontal, and not otherwise. Its projected dimension is f^beta.

Let J_i=sum_{j<i}(j,i) be the Jucys–Murphy elements, with the old labels preceding the new labels. On the beta-isotypic restriction inside S^nu,

\[
\prod_{r=1}^p(z+J_{q+r})
\]

acts by the scalar P_{nu/beta}(z). This follows from the usual branching eigenvalues, or from the central content-product identity together with cancellation of the old-label factor.

Expand the product by inserting new labels successively into permutation cycles. Its terms are exactly the permutations whose cycles contain at most one old label, with weight z^{c_0}, where c_0 counts cycles made entirely of new labels. Suppose k old labels occur in nontrivial cycles. Modulo permutations of the symmetric new block, such a term reduces to k disjoint cross-block swaps. Its trace against e_(p)e_beta is therefore the same as the trace of tau_k against that projector. Conjugation by S_q makes the choice of old labels immaterial.

The weighted number of these terms is

\[
p!\binom qk[t^{p-k}](1-t)^{-z-k}
 =\binom pk(q)_k(z+k)^{\overline{p-k}},
\]

where (q)_k=q(q-1)...(q-k+1). One can see the generating function by giving each of k selected old roots a nonempty ordered sequence of new labels and giving each entirely-new cycle weight z.

Writing

\[
\omega_k=\frac1{f^\beta}
\operatorname{Tr}_{S^\nu}(\tau_k(e_{(p)}\otimes e_\beta)),
\]

and taking traces gives

\[
P_{\nu/\beta}(z)
 =\sum_k\binom pk(q)_k\omega_k(z+k)^{\overline{p-k}}.
\]

Comparison with (6) yields

\[
\operatorname{Tr}_{S^\nu}(\tau_k(e_{(p)}\otimes e_\beta))
 =\frac{f^\beta}{\binom pk(q)_k}N^{\nu}_{p,\beta,k}.
\tag{9}
\]

The factor is positive and independent of nu. Theorem 1 proves (7); (4) proves (8). QED.

### Low-contraction formulas

For horizontal nu/beta, put Delta=kappa_nu-kappa_(p)-kappa_beta and Gamma=gamma_nu-gamma_(p)-gamma_beta. Then

\[
N_{p,\beta,1}^{\nu}=\Delta,
\qquad
N_{p,\beta,2}^{\nu}=\frac{\Delta^2-pq-\Gamma}{2}.
\tag{10}
\]

For p=4 and k=3,

\[
N_{4,\beta,3}^{\nu}=P_{\nu/\beta}(-2)-P_{\nu/\beta}(-3).
\tag{11}
\]

More generally, if the added strip contains boxes of every content k-1,k,...,p-1, then N_{p,beta,k}^{nu}=0: every evaluation in (5) has one of these boxes as a zero factor. This is a sufficient vanishing criterion, not a claimed converse.

These formulas explain why small contractions produce sparse structured inequalities. In particular, roots at -2 and -3 force whole sets of Pieri children to disappear.

For arbitrary alpha, beta, the one-swap formula is also explicit:

\[
t_\nu=\frac{f^\alpha f^\beta}{pq}
 c_{\alpha\beta}^{\nu}
 (\kappa_\nu-\kappa_\alpha-\kappa_\beta).
\tag{12}
\]

Indeed, block averaging of one swap is the cross-transposition sum divided by pq; this sum is the difference of the three transposition class sums. Its scalar on the projected subgroup type is the displayed content difference, and the restriction multiplicity is the Littlewood–Richardson coefficient.

## 4. A uniform three-witness family

### Theorem 3

Let m >= 6 be an integer, n=m+10, and lambda=(m,4,3,3). Define the following seven partitions and coefficients:

| i | mu_i | r_i(m) |
|---|---|---|
| 1 | (m+4,3,3) | 3m(17m^2+74m-351) |
| 2 | (m+3,4,3) | 9(m-3)(m^2+27m-8) |
| 3 | (m+3,3,3,1) | 14m^3+21m^2-711m+1296 |
| 4 | (m+2,4,3,1) | 18(m-3)(7m-24) |
| 5 | (m+2,3,3,2) | 10(5m^2-41m+114) |
| 6 | (m+1,4,3,2) | 90(m-3)(m-6) |
| 7 | (m+1,3,3,3) | 90(m-1)(m-6) |

Then

\[
180(5m-9)d_\lambda(A)\le\sum_{i=1}^7r_i(m)d_{\mu_i}(A).
\tag{13}
\]

Equivalently,

\[
\bar d_\lambda(A)\le\sum_{i=1}^7c_i(m)\bar d_{\mu_i}(A),
\qquad
c_i(m)=\frac{r_i(m)f^{\mu_i}}{180(5m-9)f^\lambda},
\tag{14}
\]

with c_i(m) >= 0 and sum_i c_i(m)=1.

### Proof: a polynomial identity of three positive witnesses

Set

\[
D_m=\Phi_{4,(m,3,3),3},\qquad
E_m=\Phi_{m,(4,3,3),1},\qquad
F_m=\Phi_{m+1,(3,3,3),2}.
\]

Their nonzero raw-immanant coefficient columns are the following; an entry can vanish at a particular m.

| Partition | D_m | E_m | F_m |
|---|---|---|---|
| (m+4,3,3) | 4m(m-2)(m-1) | 4m | 3m(m+1) |
| (m+3,4,3) | (m-3)(m-2)(m-1) | 3m-1 | 0 |
| (m+3,3,3,1) | (m-18)(m-2)(m-1) | 3(m-2) | m(m-9) |
| (m+2,4,3,1) | -6(m-3)(m-2) | 2(m-3) | 0 |
| (m+2,3,3,2) | -10(m-7)(m-2) | 2(m-5) | -4(2m-5) |
| (m+1,4,3,2) | 30(m-3) | m-9 | 0 |
| (m+1,3,3,3) | 60(m-4) | m-12 | 36 |
| (m,4,3,3) | -120 | -10 | 0 |

Here is a direct all-parameter derivation of the sparsity, rather than interpolation from examples. A horizontal four-strip on (m,3,3) produces

\[
\nu=(m+a,3+b,3,c),\qquad a+b+c=4,\quad c\le3.
\]

Its content polynomial is

\[
P(z)=(z+m)^{\overline a}(z+2)^{\overline b}(z-3)^{\overline c}.
\]

If b >= 2, both P(-2) and P(-3) vanish. Thus D_m has only the eight children b=0,1 and c=0,1,2,3 listed in the table. Substitution in (11) gives its displayed column. The horizontal children of (4,3,3) have the same eight shapes; (10) gives E_m. The horizontal children of (3,3,3) have the four shapes with second row 3, and (10) gives F_m. This proves the entire table for every m >= 6.

Now take the positive combination

\[
9D_m+90(m-3)E_m+5(m-3)F_m.
\tag{15}
\]

The coefficient of d_lambda is -180(5m-9), and the remaining coefficients are exactly r_1,...,r_7. This proves (13).

For sign verification put t=m-6 >= 0. The seven coefficients become

\[
\begin{aligned}
r_1&=3(t+6)(17t^2+278t+705),\\
r_2&=9(t+3)(t^2+39t+190),\\
r_3&=14t^3+273t^2+1053t+810,\\
r_4&=18(t+3)(7t+18),\\
r_5&=10(5t^2+19t+48),\\
r_6&=90(t+3)t,\\
r_7&=90(t+5)t.
\end{aligned}
\]

All are nonnegative. Finally, each witness in (15) is balanced by (8), giving

\[
\sum_i r_i(m)f^{\mu_i}=180(5m-9)f^\lambda.
\]

This proves the convex normalization in (14). QED.

### PDC consequence

The first six right-hand shapes have at most three parts greater than 2. They are in Pate's class (p,q,r,2^s,1^t). The seventh has the form (p,q^2,r), with q=r=3, and is in Pate's 1999 class. Thus every right-hand normalized immanant is at most the permanent. The convex weights in (14) prove

\[
\bar d_{(m,4,3,3)}(A)\le\operatorname{per}(A),\qquad m\ge6.
\tag{16}
\]

The external PDC classes used here are from Pate (1998, 1999), not newly proved in this note.

## 5. The order-15 endpoint: an exact seven-witness bridge

Define Phi_i by the following table, with Phi normalized exactly as in (5)–(7), not by primitive gcd reduction.

| i | p | beta | k | positive integer multiplier |
|---|---:|---|---:|---:|
| 1 | 1 | (7,4,3) | 1 | 80 |
| 2 | 5 | (4,3,3) | 1 | 240 |
| 3 | 3 | (4,4,4) | 3 | 3 |
| 4 | 4 | (5,3,3) | 3 | 10 |
| 5 | 4 | (4,4,3) | 3 | 3 |
| 6 | 4 | (4,4,3) | 4 | 3 |
| 7 | 6 | (3,3,3) | 2 | 30 |

The exact identity is

\[
\begin{aligned}
80\Phi_1+240\Phi_2+3\Phi_3+10\Phi_4+3\Phi_5+3\Phi_6+30\Phi_7
=20\big(&495d_{(9,3,3)}+226d_{(8,4,3)}\\
&+12d_{(7,5,3)}+4d_{(7,4,4)}-198d_{(5,4,3,3)}\big).
\end{aligned}
\tag{17}
\]

This is a finite exact certificate: the seven coefficient vectors are specified without ambiguity by the integer formula (5), and the standard-library verifier checks every coordinate. For a manually inspectable version, their only nonzero coordinates are displayed below.

| nu | Phi_1 | Phi_2 | Phi_3 | Phi_4 | Phi_5 | Phi_6 | Phi_7 |
|---|---:|---:|---:|---:|---:|---:|---:|
| (9,3,3) | 0 | 20 | 0 | 240 | 0 | 0 | 90 |
| (8,4,3) | 7 | 14 | 0 | 24 | 96 | 24 | 0 |
| (8,3,3,1) | 0 | 9 | 0 | -156 | 0 | 0 | -20 |
| (7,5,3) | 3 | 0 | 0 | 0 | 0 | 0 | 0 |
| (7,4,4) | 1 | 0 | 24 | 0 | -12 | -12 | 0 |
| (7,4,3,1) | -3 | 4 | 0 | -36 | -84 | -36 | 0 |
| (7,3,3,2) | 0 | 0 | 0 | 60 | 0 | 0 | -20 |
| (6,4,4,1) | 0 | 0 | -30 | 0 | 6 | 24 | 0 |
| (6,4,3,2) | 0 | -4 | 0 | 60 | 60 | 60 | 0 |
| (6,3,3,3) | 0 | -7 | 0 | 60 | 0 | 0 | 36 |
| (5,4,4,2) | 0 | 0 | 40 | 0 | 20 | -60 | 0 |
| (5,4,3,3) | 0 | -10 | 0 | -120 | 0 | -120 | 0 |
| (4,4,4,3) | 0 | 0 | -60 | 0 | -180 | 240 | 0 |

By Theorem 2 every Phi_i is nonnegative. The relevant dimensions are

\[
f^{(5,4,3,3)}=75075,\quad
f^{(9,3,3)}=12740,\quad f^{(8,4,3)}=35035,\quad
f^{(7,5,3)}=45045,\quad f^{(7,4,4)}=25025.
\]

Consequently (17) gives

\[
\boxed{\bar d_{(5,4,3,3)}\le
\frac{14}{33}\bar d_{(9,3,3)}+
\frac{791}{1485}\bar d_{(8,4,3)}+
\frac{2}{55}\bar d_{(7,5,3)}+
\frac{2}{297}\bar d_{(7,4,4)}.}
\tag{18}
\]

The numerator weights over denominator 1485 are 630,791,54,10, summing to 1485. All right-hand partitions have three rows, proving the order-15 PDC consequence using the cited established class.

Together with Theorem 3 and the accepted order-14 input, this yields PDC for (m,4,3,3) for every integer m >= 4. Only the m=4 member uses the supplied established result.

### A further order-15 consequence

Pate's 1992 node-moving theorem says that moving the last node of a row whose length is strictly greater than the next row and greater than 1 to a new singleton row decreases the normalized immanant. Applied to the first row of (5,4,3,3), it gives

\[
\bar d_{(4,4,3,3,1)}\le\bar d_{(5,4,3,3)}\le\operatorname{per}.
\]

The only order-15 partitions outside the explicitly stated Pate (1998,1999) class are (5,4,3,3), (4,4,3,3,1), and (3,3,3,3,3). This follows either by listing partitions or by considering the parts at least 3. Thus, combined with those known classes, the present proof establishes every ordinary order-15 PDC case except (3,3,3,3,3). This is not a claim that the last case is false.

More generally, repeated use of the same node-moving theorem gives PDC for (m,4,3,3,1^t), m >= 4 and t >= 0, with the single m=4,t=0 endpoint supplied by the original input.

## 6. Additional exact certificates, and what is only experimental

The folder `additional_certificates` gives exact positive rational combinations of primitive witnesses, independently re-evaluated by the content formula. They include the following alternative three-row bridges:

\[
\bar d_{(6,4,3,3)}\le
\frac{37200\bar d_{(10,3,3)}+60128\bar d_{(9,4,3)}+
12452\bar d_{(8,5,3)}+1595\bar d_{(8,4,4)}}{111375},
\tag{19}
\]

and

\[
\bar d_{(7,4,3,3)}\le
\frac{4775\bar d_{(11,3,3)}+9121\bar d_{(10,4,3)}+
2400\bar d_{(9,5,3)}+336\bar d_{(9,4,4)}}{16632}.
\tag{20}
\]

Both use six witnesses. An additional 38-witness exact certificate proves PDC for (6,5,3,3) at order 17 by a convex combination of three-row immanants. Its larger coefficients are retained in the JSON certificate rather than obscuring the main structural theorem.

No uniform theorem for arbitrary (a,b,3,3) is claimed. A shifted copy of the seven-witness order-15 pattern was infeasible in the tested restricted searches at m=6 and 7. The final three-witness family was obtained by changing the cancellation objective: retain positive terms belonging to known PDC classes, instead of demanding that every four-row term cancel. This is a substantive structural distinction, not interpolation from successful small cases.

## 7. The enumerated cone

Let C_n be the conical hull, in normalized-immanant coordinates, of all central-projector partial-swap witnesses (3), with p+q=n, all alpha of p and beta of q, and 1 <= k <= min(p,q). Unordered block pairs are counted once. Zero vectors are removed; positive multiples are identified by primitive gcd normalization.

This is not asserted to equal the cone obtained from all noncentral branching filters in Theorem 1.

| n | Number of partitions | Parameter labels | Zero labels | Distinct nonzero generator rays | Exact linear-span rank |
|---:|---:|---:|---:|---:|---:|
| 14 | 135 | 5095 | 834 | 3366 | 134 |
| 15 | 176 | 8112 | 1310 | 5398 | 175 |

“Generator rays” does not mean “extreme rays.” Redundancy removal and facet enumeration were not completed. The rank assertions are exact: each supplied modular minor is nonsingular modulo 1000003, while balance gives the matching upper bound p(n)-1.

### Exact computation

Characters were computed by Murnaghan–Nakayama with integer beta sets and checked against full integer character orthogonality. The double character sum was evaluated by exact marked-cycle enumeration. For each block permutation, record its induced permutation on the k marked endpoints, the lengths of intervening unmarked paths, and its cycles disjoint from the endpoints. For given unmarked cycles rho the multiplicity is (p-k)!/z_rho. Combining the two blocks gives the cycle type after the swap. All type marginals were checked to equal the appropriate products of conjugacy-class sizes.

This enumeration was independently compared against direct permutation enumeration for every k at block sizes (2,3), (3,3), (3,4), and (4,4). Every nonzero symmetric-first-block witness at n=14 and 15 was also recomputed by the independent content formula: 813 and 1132 labelled witnesses respectively, with exact agreement. The general positivity proof does not depend on numerical testing of matrices.

### Exhaustive floating-point PDC queries

Every non-permanent partition was queried for membership of e_(n)-e_lambda in C_n.

| n | Queries | LP feasible | LP infeasible | Numerical difficulty |
|---:|---:|---:|---:|---:|
| 14 | 134 | 131 | 2 | 1 |
| 15 | 175 | 172 | 1 | 2 |

These counts describe floating-point discovery, not a fully certified membership classification. At n=14 the two numerically infeasible targets were (3,3,3,3,2) and (3,3,2,2,2,2); numerical difficulty occurred for (2,2,2,2,2,2,2). At n=15 the infeasible target was (3,3,3,3,3), and numerical difficulty occurred for (3,2,2,2,2,2,2) and (2,2,2,2,2,2,2,1). The JSON files preserve the statuses. The latter two numerical difficulties must not be described as mathematical exclusions.

Using only k=1, the initial floating-point searches found 49 feasible PDC targets at n=14 and 60 at n=15. Higher contractions therefore materially enlarge the usable cone; they are not cosmetic copies of the first-content inequality.

## 8. Exact limitations

### 8.1 The order-15 rectangular target is outside C_15

The file `dual_15_33333.json` specifies 176 integers y_nu in [0,10000], one per partition. For every primitive raw-immanant generator r in the full order-15 matrix, exact integer verification gives

\[
\sum_\nu r_\nu f^\nu y_\nu\ge0.
\]

In fact the smallest value over the stored generator rays is 98. Yet

\[
y_{(15)}=9700,\qquad y_{(3,3,3,3,3)}=10000.
\]

The target functional therefore has pairing -300, or -3/100 after division by 10000. Farkas separation proves

\[
e_{(15)}-e_{(3^5)}\notin C_{15}.
\]

The separator is also nonnegative on individual immanant nonnegativity rays and on all Schur lower-bound rays: all y_nu >= 0 and y_(1^15)=0. Thus adjoining those basic inequalities does not remove this obstruction. The separator also satisfies y_nu <= 9700 for every nu other than (3^5). Consequently it is nonnegative on every other PDC ray e_(15)-e_nu. Even adjoining PDC for **all other order-15 partitions** cannot produce the missing target. Equivalently, this cone cannot dominate bar d_(3^5) by any convex combination of the other normalized immanants: the latter have dual value at most 9700, whereas the target has value 10000. The y values are a formal separating functional, **not** the immanants of a PSD matrix. They do not refute PDC.

### 8.2 Incompleteness is already visible at order 3

For n=3 the central partial-swap cone is exactly generated by

\[
\operatorname{per}-\bar d_{(2,1)},\qquad
\bar d_{(2,1)}-\det.
\]

Allowing arbitrary two-block filters does not enlarge it: the only nontrivial block group is S_2, whose group algebra splits into its two one-dimensional orthogonal idempotents; the traces depend on the two nonnegative squared filter coefficients.

Nevertheless the valid inequality

\[
3\operatorname{per}(A)-2d_{(2,1)}(A)+\det(A)\ge0
\tag{21}
\]

is outside this cone. It appears in the recent immanant/entanglement literature; it is not claimed as new here. In normalized coordinates its vector is (3,-4,1), separated by the assignment (per,bar d_(2,1),det)=(1,1,0).

For completeness, here is a direct proof of validity. A zero diagonal entry in a PSD matrix makes the corresponding row and column zero, so the assertion is immediate. Otherwise diagonally scale to a correlation matrix. Let S=|a_12|^2+|a_23|^2+|a_31|^2 and r=Re(a_12 a_23 a_31). The left side of (21) is 2(S+6r). If r >= 0 it is nonnegative. If r=-u<0, PSD implies S+2u <= 1, while AM-GM implies S >= 3u^(2/3). Consequently 3u^(2/3)+2u <= 1, so u <= 1/8. Therefore S >= 3u^(2/3) >= 6u. Diagonal scaling preserves the inequality. QED.

This proves a genuine limitation: the two-block partial-swap construction is a useful general theory of sufficient inequalities, not a complete characterization of every immanant-positive linear form.

## 9. Closure and interpretation

If h is any immanant-positive class function on S_n and chi^beta is an irreducible character of S_m, then induction preserves positivity:

\[
d_{\operatorname{Ind}_{S_n\times S_m}^{S_{n+m}}(h\boxtimes\chi^\beta)}(A)
 =\sum_{|I|=n}d_h(A[I])d_\beta(A[I^c])\ge0.
\tag{22}
\]

The equality follows by writing induction as a sum over block cosets; a permutation contributes precisely for its invariant subsets I. The right side is nonnegative because principal submatrices are PSD and ordinary immanants are nonnegative by their projector formula. This proves closure, not merely an algorithmic observation.

For normalized characters the descendant weights are

\[
\frac{c_{\lambda\beta}^{\nu}f^\nu}
 {\binom{n+m}{n}f^\lambda f^\beta},
\]

which sum to one by the dimension formula for induction. Thus a dominance relation propagates to relations between convex mixtures of Littlewood–Richardson descendants. It does not automatically isolate one descendant, so it must not be mistaken for a free PDC lifting theorem.

All seven shapes in Theorem 3 dominate lambda in the Young-diagram dominance order. That fact alone would not prove the result: dominance order is not sufficient for normalized-immanant comparison on the PSD cone. For example, J_2 direct-sum J_2 has bar d_(2,2)=2 and bar d_(3,1)=4/3, although (3,1) dominates (2,2). The useful extra structure here is the horizontal-strip content polynomial and its forced zeros.

The order-15 bridge is not a consequence merely of the scalar bounds 0 <= bar d_nu <= per and Schur's determinant lower bound. As formal scalar inequalities those bounds permit target=1, per=1, det=0, and all four bridge RHS values=0. This does not prove independence from every inequality in Pate's papers, and no such exhaustive independence claim is made.

## 10. Literature boundary and remaining work

Pate's 1997 paper already explicitly develops a general inequality-generating machine. His 1999 paper derives xi-functions from tensor contractions and quadratic forms and treats substantial PDC classes. Huber–Maassen and the recent work of Rico and coauthors also give operator-theoretic formulations of immanant inequalities. The block-positive/central-averaging perspective by itself is therefore not a defensible claim of wholly new theory.

The concrete additional content established in this note is the proved content/finite-difference description used here, the uniform three-witness family with explicit coefficients, the order-15 finite bridge, and the certified cone obstruction. Whether the content formula or particular higher-order consequences already occur in equivalent form in the older literature remains a priority-check question. The searches performed located no prior explicit proof for the (5,4,3,3) case, but absence of a search hit is not a proof of priority.

The original twenty-witness definitions remain necessary to determine whether their construction equals this central cone, lies inside the broader two-block filter mechanism, or includes additional operations. The present full cone enumeration cannot settle that missing-data issue. No claim is made to settle PDC for (3^5), to classify the entire arbitrary-filter cone, or to derive an all-(a,b,3,3) theorem.

## References used for external results

1. T. H. Pate, *Immanant Inequalities and Partition Node Diagrams*, Journal of the London Mathematical Society s2-46 (1992), 65–80. DOI: 10.1112/jlms/s2-46.1.65.
2. T. H. Pate, *A machine for producing inequalities involving immanants and other generalized matrix functions*, Linear Algebra and its Applications 254 (1997), 427–466. DOI: 10.1016/S0024-3795(96)00512-5.
3. T. H. Pate, *Row Appending Maps, Psi-Functions, and Immanant Inequalities for Hermitian Positive Semi-Definite Matrices*, Proceedings of the London Mathematical Society 76 (1998), 307–358. DOI: 10.1112/S0024611598000100.
4. T. H. Pate, *Tensor inequalities, xi-functions and inequalities involving immanants*, Linear Algebra and its Applications 295 (1999), 31–59. DOI: 10.1016/S0024-3795(99)00035-X.
5. F. Huber and H. Maassen, *Matrix forms of immanant inequalities*, arXiv:2103.04317 (2021).
6. I. M. Wanless, *Lieb's permanental dominance conjecture*, arXiv:2202.01867 (2022).
7. A. Rico, D. Grinko, R. Krebs, L. H. Zaw, *Entanglement Structure and Matrix Inequalities from Isotypic Measurements*, Physical Review Letters 137, 100203 (2026), DOI: 10.1103/nvk2-h8d5. Related preprint arXiv:2511.13822, under the earlier title *Detection of many-body entanglement partitions in a quantum computer*.

The new claims above are proved directly; the cited PDC classes and node-moving theorem are the only external dominance inputs used in their PDC corollaries.
