# A positive-witness proof for the rectangular immanant (3,3,3,3,3)

## Main theorem

For every complex Hermitian positive-semidefinite matrix A of order 15,

\[
 d_{(3,3,3,3,3)}(A)\le 6006\operatorname{per}(A),
 \qquad\text{equivalently}\qquad
 \bar d_{(3,3,3,3,3)}(A)\le\operatorname{per}(A).
\]

The proof is a finite positive combination of 125 explicitly defined witnesses:
106 central-projector partial-swap witnesses and 19 branching-refined witnesses.
It does not assume PDC for any other partition. The latter witnesses genuinely
extend the central-projector cone: one witness used in the proof has strictly
negative pairing with the previously certified separator.

All coefficients of the final certificate have been checked by exact integer
arithmetic. The verifier reconstructs the central witnesses from character
sums, not from the previously supplied cone matrix. No floating-point solver
or tolerance occurs in verification. The certificate and the mathematical
positivity proof together establish the theorem; experimental matrix tests
are not used in the proof.

The proof and its computation have not received an external audit or Lean
formalization in this run. No historical-priority claim is made for the
general branching inequality in isolation.

## 1. Notation

For a partition nu of n, let chi^nu be the ordinary irreducible character of
S_n, let f^nu=chi^nu(e), and set

\[
 d_\nu(A)=\sum_{\sigma\in S_n}\chi^\nu(\sigma)
                \prod_{i=1}^n a_{i,\sigma(i)},
 \qquad \bar d_\nu=d_\nu/f^\nu.
\]

A box in row i and column j has content j-i. Write gamma prec beta when beta
is obtained from gamma by adding one box. The central orthogonal idempotent
in C[S_m] belonging to eta is

\[
 e_\eta^{(m)}=\frac{f^\eta}{m!}
   \sum_{\sigma\in S_m}\chi^\eta(\sigma^{-1})\sigma.
\]

Each S_m below acts on the first m labels. For a nonzero rational coefficient
vector, `primitive` means: clear denominators by their positive least common
multiple, and then divide by the positive greatest common divisor. Never
reverse the sign of a vector during this normalization.

## 2. The new branching-refined one-swap inequality

### Theorem 2.1

Let n>=2, beta partition n-1, and gamma prec beta partition n-2. Put

\[
 c=c(\beta\setminus\gamma).
\]

Then, for every complex Hermitian PSD matrix A of order n,

\[
 \boxed{\quad
 B_{\beta,\gamma}(A):=
 \sum_{\nu\succ\beta}
 \frac{d_\nu(A)}{c(\nu\setminus\beta)-c}
 \ge0.\quad}
 \tag{2.1}
\]

The sum is over all one-box extensions of beta. None of its denominators is
zero. The coefficients may have either sign.

### Proof: positivity

Let

\[
 b=e_\beta^{(n-1)}e_\gamma^{(n-2)},\qquad
 s=(n-1,n),\qquad W=b s b.
\]

The two idempotents commute, so b is an orthogonal projection. It is usually
noncentral in C[S_{n-1}]. Given a Gram realization A=(<x_i,x_j>), write
x=x_1 tensor ... tensor x_n. Applying b affects only the first n-1 factors,
so

\[
 b x=u\otimes v,\qquad
 u\in H^{\otimes(n-1)},\quad v=x_n\in H.
\]

Separating the last factor of u and using the swap identity gives

\[
 \langle x,W x\rangle
 =\langle u\otimes v,s(u\otimes v)\rangle
 =\bigl\|(I\otimes\langle v,\cdot\rangle)u\bigr\|^2\ge0.
 \tag{2.2}
\]

Here the inner product is conjugate-linear in its first entry. In particular,
(2.2) is a valid complex, not merely real, squared-norm identity.
Conjugating W by a permutation preserves nonnegativity on decomposable tensors.
Its central average therefore has nonnegative expectation on every Gram tensor.

For any self-adjoint W with this property, central averaging and Schur's lemma
give

\[
 Z(W)=\frac1{n!}\sum_{g\in S_n}gWg^{-1}
 =\sum_{\nu\vdash n}\frac{\operatorname{Tr}_{S^\nu}(W)}{f^\nu}e_\nu,
\]

and consequently

\[
 \langle x,Z(W)x\rangle
 =\frac1{n!}\sum_\nu\operatorname{Tr}_{S^\nu}(W)d_\nu(A)\ge0.
 \tag{2.3}
\]

### Proof: exact trace, without numerical representation matrices

Define the Jucys--Murphy elements

\[
 J_m=\sum_{i<m}(i,m).
\]

The group-algebra identity needed here is elementary:

\[
 sJ_n-J_{n-1}s=1.
 \tag{2.4}
\]

Indeed, J_n=sJ_{n-1}s+s. The standard content eigenvalue rule follows from
J_m=K_m-K_{m-1}, where K_m is the sum of all transpositions in S_m and acts
on S^eta by the sum of the contents of eta. We use the ordinary
multiplicity-free Young branching rule.

Fix an irreducible S^nu. If nu does not cover beta, b acts as zero. Otherwise,
let Q be the action of b on S^nu. Young branching gives

\[
 \operatorname{Tr}Q=f^\gamma.
\]

Writing u_0=c(nu minus beta), the content rule gives

\[
 J_nQ=u_0Q,\qquad J_{n-1}Q=cQ.
\]

Multiply (2.4) by Q and take the trace. Cyclicity yields

\[
 (u_0-c)\operatorname{Tr}(Qs)=\operatorname{Tr}Q=f^\gamma.
 \tag{2.5}
\]

Since Q is a projection,

\[
 \operatorname{Tr}_{S^\nu}(W)=\operatorname{Tr}(QsQ)
 =\operatorname{Tr}(Qs)
 =\frac{f^\gamma}{c(\nu\setminus\beta)-c(\beta\setminus\gamma)}.
 \tag{2.6}
\]

An addable box of beta cannot have the same content as a removable box of
beta: comparison of their row indices gives a strict inequality in one
direction or the other. Thus division in (2.5) is legitimate.

Substituting (2.6) into (2.3) and dividing by f^gamma>0 proves (2.1). This
argument applies to every Gram realization, including rank-deficient ones. QED.

### What information the refinement retains

The central filter e_beta averages over all predecessors gamma of beta.
The refinement retains the final predecessor, and hence the content of the
last box added inside the large tensor block. The coefficients become
reciprocals of individual content differences instead of their averaged
values. This is a genuine additional choice of local filter, not a search
inside the previous central-projector cone.

## 3. A used witness that escapes the certified old cone

Choose

\[
 \beta=(4,4,4,1,1),\qquad \gamma=(4,4,3,1,1).
\]

The removed box has content 1. The addable-box contents of beta are 4,-2,-5,
so (2.1) becomes

\[
 \frac13d_{(5,4,4,1,1)}
 -\frac13d_{(4,4,4,2,1)}
 -\frac16d_{(4,4,4,1,1,1)}\ge0.
\]

Its primitive raw coefficient vector is therefore

\[
 R_{120}=2d_{(5,4,4,1,1)}-2d_{(4,4,4,2,1)}-d_{(4,4,4,1,1,1)}.
 \tag{3.1}
\]

The three dimensions are 100100, 75075, and 50050, respectively. Dividing
(3.1) by 50050 gives the normalized inequality

\[
 4\bar d_{(5,4,4,1,1)}
 -3\bar d_{(4,4,4,2,1)}
 -\bar d_{(4,4,4,1,1,1)}\ge0.
 \tag{3.2}
\]

On these coordinates, the old integer separator has values 3726,4911,2501.
Its pairing with (3.2) is

\[
 4(3726)-3(4911)-2501=-2330<0.
 \tag{3.3}
\]

It follows from the previously established separator that this witness is
outside C_15, including the enlargement by every other order-15 PDC ray.
The witness is term 120 of the actual proof certificate, not merely an
unused separating example.

## 4. The exact finite certificate

### 4.1 Definition of its central witnesses

For p+q=15, alpha partition p, beta partition q, and 1<=k<=min(p,q), let

\[
 \tau_k=(1,p+1)\cdots(k,p+k),
\]

and define the integer coefficients

\[
 F_{\alpha,\beta,k}(\nu)
 =\sum_{\sigma\in S_p,\ \pi\in S_q}
   \chi^\alpha(\sigma)\chi^\beta(\pi)
   \chi^\nu((\sigma\oplus\pi)\tau_k).
 \tag{4.1}
\]

Set

\[
 R_{\alpha,\beta,k}(A)
 =\sum_{\nu\vdash15}
  \operatorname{primitive}(F_{\alpha,\beta,k})(\nu)d_\nu(A).
 \tag{4.2}
\]

The selected vectors are all nonzero. Formula (4.1) differs from the trace of
(e_alpha tensor e_beta) tau_k (e_alpha tensor e_beta) by the positive factor
f^alpha f^beta/(p! q!), so the partial-swap positivity theorem implies
R_{alpha,beta,k}(A)>=0. Positive primitivization preserves the sign.

For k=1 the verifier uses the equivalent, positively proportional vector

\[
 c_{\alpha\beta}^{\nu}
 \bigl(\kappa_\nu-\kappa_\alpha-\kappa_\beta\bigr),
 \tag{4.3}
\]

where kappa is total content. To verify the proportionality, the trace of
one fixed cross-block transposition is the trace of the sum of all pq such
transpositions divided by pq. That sum is K_15-K_p-K_q. On the subgroup type
alpha tensor beta, it gives the scalar in (4.3), with multiplicity
c_{alpha,beta}^nu and dimension f^alpha f^beta. Thus (4.1) is (4.3) multiplied
by p!q!/(pq)>0. The verifier calculates the multiplicity by the exact
character inner product on S_p times S_q.

### 4.2 Definition of its branching witnesses

For each listed pair gamma prec beta of sizes 13 and 14, define

\[
 R_{\beta,\gamma}(A)=
 \sum_{\nu\vdash15}
 \operatorname{primitive}\left(
  {\bf1}_{\nu\succ\beta}
  \frac1{c(\nu\setminus\beta)-c(\beta\setminus\gamma)}
 \right)(\nu)d_\nu(A).
 \tag{4.4}
\]

These are nonnegative by Theorem 2.1.

### 4.3 The identity

The complete labels, primitive raw coefficient vectors, and positive integer
multipliers z_i are in `certificate.json`. A full plain-text rendering is in
`certificate.txt`. There are no omitted terms or unspecified parameters.
The first 106 terms are (4.2); the last 19 are (4.4).

For the positive integer M printed in both files, the exact identity is

\[
 \boxed{\quad
 \sum_{i=1}^{125}z_i R_i(A)
 =M\bigl(6006\operatorname{per}(A)-d_{(3,3,3,3,3)}(A)\bigr),
 \qquad z_i\in\mathbb Z_{>0},\ M\in\mathbb Z_{>0}.
 \quad}
 \tag{4.5}
\]

For definiteness, M is the following 115-digit integer:

```
2622150535278170077084028849035651351078346354137625907361158186255438546087020178852205591785682843258976630527200
```

Equation (4.5) is an identity of raw-immanant coefficient vectors. Its only
nonzero coordinates are 6006M at (15) and -M at (3,3,3,3,3). Every other one of
the 176 partition coordinates is exactly zero. No tolerance or numerical
residual is being interpreted as zero.

### 4.4 Conclusion

Every R_i is nonnegative on every complex Hermitian PSD matrix, and every
z_i and M is positive. Equation (4.5) therefore proves

\[
 6006\operatorname{per}(A)-d_{(3,3,3,3,3)}(A)\ge0.
\]

The hook-length formula gives

\[
 f^{(3,3,3,3,3)}=\frac{15!}{217728000}=6006.
\]

Dividing by 6006 proves the main theorem. No other PDC case is needed in this
argument. Singular matrices are covered directly by the Gram-tensor proof,
without approximation or an invertibility assumption. QED.

## 5. Reproducible exact verification

Run, in the bundle directory,

```sh
python verify.py
```

Only the Python standard library is needed. The program reconstructs all
106 selected central coefficient vectors, all 19 branching coefficient
vectors, and all 176 coordinates of the integer identity. It also checks
positive multipliers, primitive normalizations, degree balance, character
degrees and character orthogonality through order 15, and the negative
separator pairing (3.3). No old cone matrix is read.

The central reconstruction avoids enumerating 15! permutations. Here is the
finite counting argument implemented in `exact_algebra.py`.

Mark the k swapped labels in each block. Deleting the unmarked elements
from cycles of sigma produces a permutation s of the k marks, tail lengths
a_1,...,a_k between successive marks, and a partition rho of lengths of the
unmarked-only cycles. For fixed s,a,rho, the number of permutations is

\[
 \frac{(p-k)!}{z_\rho},\qquad
 z_\rho=\prod_j j^{m_j(\rho)}m_j(\rho)!.
\]

This follows by assigning the distinct unmarked labels to the ordered tails
and then to the remaining disjoint cycles. Its cycle type is rho together
with |C|+sum_{i in C}a_i for each cycle C of s. Use corresponding data
(t,b,eta) for the second block.

After applying the cross-block swap, the cycles on the marked labels are
the cycles C of s composed with t. Each such cycle has full length

\[
 2|C|+\sum_{i\in C}\bigl(b_i+a_{t(i)}\bigr),
\]

and the unmarked-only cycles rho and eta remain. This gives the three cycle
types in (4.1), with multiplicity

\[
 \frac{(p-k)!(q-k)!}{z_\rho z_\eta}.
\]

Simultaneous relabelling of both sets of marks permits s to be restricted to
one representative of each conjugacy class, with the factor k!/z_{type(s)}.
The second permutation t is enumerated fully. The verifier checks both the
total p!q! and every marginal class count, and then evaluates the exact
character sum (4.1). Characters are computed by the Murnaghan--Nakayama rule
in beta-set form.

The exact final check is simply integer vector arithmetic:

```
total[nu] = sum(z_i * R_i[nu] for i in range(125))
assert total[(15,)] == 6006 * M
assert total[(3,3,3,3,3)] == -M
assert all(other coordinates are zero)
```

`verification_log.txt` records a successful full reconstruction and check.
This is a certificate verification, not an LP-feasibility assertion.

## 6. Independent checks not used in the proof

The branching formulas were additionally tested against direct permutation
sums on 12 exact Gaussian-integer Gram matrices at each order 3,4,5,6,7,
covering every one-step branching witness at those orders. These are exact
finite tests, not a substitute for Theorem 2.1.

A separate rectangular route used the dual Jacobi--Trudi identity

\[
 s_{(3^5)}=e_5^3-2e_4e_5e_6+e_3e_6^2+e_4^2e_7-e_3e_5e_7.
\]

If D_(a,b,c)(A) is the sum of products of determinants over all ordered
partitions of the index set into subsets of sizes a,b,c, this gives

\[
 d_{(3^5)}=D_{(5,5,5)}-2D_{(6,5,4)}+D_{(6,6,3)}
             +D_{(7,4,4)}-D_{(7,5,3)}.
\]

That character identity was checked on all 176 conjugacy classes exactly.
It supplied an independent evaluator for 113 numerical PSD matrices:
80 random complex Gram matrices of ranks 5,6,8,10,15, 25 mixtures with the
identity, and eight equicorrelation matrices. No violating matrix was found.
These matrix tests are numerical only and make no contribution to the proof
of the universal inequality. Details are in `experimental_checks.json`.

## 7. Dependencies and scope

The new ingredient is Theorem 2.1: noncentral local filtering along one edge
of the Young branching graph. No multiblock positivity conjecture, conjectural
rank reduction, inequality for a conjugate shape, or PDC induction hypothesis
is invoked. Only two kinds of universally positive witnesses occur.

Standard representation-theoretic background is the Young branching rule,
the content eigenvalue description of the Jucys--Murphy elements, character
orthogonality, the hook-length formula, and Murnaghan--Nakayama. A primary
reference for the branching/content framework is A. M. Vershik and A. Yu.
Okounkov, *A New Approach to the Representation Theory of the Symmetric
Groups. 2*, arXiv:math/0503040v3. The partial-swap positivity mechanism is
established input in this project; its specialization needed for the new
branching theorem was proved explicitly above.

The result is for the ordinary irreducible immanant indexed by (3^5).
It does not claim the full all-orders permanental-dominance conjecture or
the version for arbitrary subgroup characters. Combining it with the
other order-15 cases established in the conversation closes the ordinary
order-15 frontier specified in the task.
