# Independent audit of the order-15 rectangular ordinary-immanant PDC proof

Audit date: 11 September 2026.

## Verdict

The supplied argument proves

\[
\boxed{d_{(3,3,3,3,3)}(A)\le 6006\,\operatorname{per}(A)}
\]

for every complex Hermitian positive-semidefinite \(15\times15\) matrix \(A\), including singular matrices.

No fatal error or substantive mathematical gap was found in the branching-refined positivity theorem, its trace/content formula, or the 125-witness certificate. The supplied verifier was rerun; every selected witness was independently reconstructed by a separate character algorithm; the complete 176-coordinate identity was checked exactly; and the full central-projector cone used in the separation claim was independently regenerated.

Two qualifications are logically separate from this conclusion. First, the broader phrase “through order 15” uses the preceding note’s explicitly accepted order-14 case \((4,4,3,3)\), whose proof was not supplied and therefore was not independently audited here. Second, historical priority remains only partially resolved: the relevant content coefficients are classical symmetric-group representation theory, and not every older Pate paper was available in full text during the audit.

### Answers to the seven requested questions

1. **Is the branching-refined positivity theorem valid?** Yes.
2. **Is the trace/content coefficient formula correct?** Yes, including support, sign, the factor \(f^\gamma\), and the nonzero denominator.
3. **Is the 125-witness exact certificate correct?** Yes. All 106 central and 19 branching-refined primitive vectors were regenerated and the final identity was checked in all 176 coordinates.
4. **Does it prove PDC for \((3^5)\) on the full complex PSD cone?** Yes. No positive-definiteness or invertibility assumption is required.
5. **Does this complete ordinary-immanant PDC through order 15?** Yes, conditional only on the previously accepted order-14 endpoint used by the project. The order-15 closure itself was checked from the supplied and independently regenerated order-15 ingredients.
6. **Which parts are genuinely new?** The reciprocal-content representation-theoretic coefficient is not new. Novelty of the exact general positivity family and of the \((3^5)\) consequence was not conclusively established from the accessible older literature.
7. **What remains before public circulation?** Preserve the exact certificate and verifier, document the earlier-case dependencies, cite the classical representation-theory antecedents, and qualify priority claims until the inaccessible older literature has been checked. No mathematical repair of the rectangular proof is indicated by this audit.

## 1. Branching-refined positivity theorem

### 1.1 The filter is an orthogonal projection

Set

\[
b=e_\beta^{(n-1)}e_\gamma^{(n-2)}.
\]

Each \(e_\eta^{(m)}\) is a self-adjoint central idempotent in \(\mathbb C[S_m]\), with involution \(\sigma^*=\sigma^{-1}\). The embedded element \(e_\gamma^{(n-2)}\) belongs to \(\mathbb C[S_{n-1}]\), while \(e_\beta^{(n-1)}\) is central in that larger algebra. Hence the two idempotents commute and

\[
b^*=b,\qquad b^2=b.
\]

Thus \(b\) acts as an orthogonal projection in every unitary representation. The proof does not require \(e_\gamma^{(n-2)}\) to be central in \(\mathbb C[S_{n-1}]\).

### 1.2 The squared-norm positivity is valid over the complex numbers

Let

\[
A=(\langle x_i,x_j\rangle),\qquad x=x_1\otimes\cdots\otimes x_n,
\]

and put \(s=(n-1,n)\), \(W=bsb\). Since \(b\) acts only on the first \(n-1\) tensor positions,

\[
bx=u\otimes v,\qquad v=x_n.
\]

Write

\[
u=\sum_{R,i}u_{R,i}\,e_R\otimes e_i,
\qquad
v=\sum_i v_i e_i.
\]

Direct expansion gives

\[
\begin{aligned}
\langle u\otimes v,s(u\otimes v)\rangle
&=\sum_R\left|\sum_i u_{R,i}\overline{v_i}\right|^2\\
&=\bigl\|(I\otimes\langle v,\cdot\rangle)u\bigr\|^2\ge0.
\end{aligned}
\]

Therefore \(\langle x,bsbx\rangle\ge0\) for every decomposable Gram tensor. The conjugation is in the correct place, so the argument is genuinely complex-Hilbert-space positivity, not a real-only computation.

This proves nonnegativity on decomposable tensors; it does **not** claim that \(bsb\) is a positive-semidefinite operator on the entire tensor space. That distinction is important because some irreducible trace coefficients are negative.

For every permutation \(g\), \(g^{-1}x\) is still decomposable, so

\[
\langle x,gWg^{-1}x\rangle=\langle g^{-1}x,Wg^{-1}x\rangle\ge0.
\]

Consequently the central average of \(W\) has nonnegative expectation on every Gram tensor.

## 2. Jucys–Murphy identity and trace/content formula

### 2.1 The group-algebra identity has the correct sign

Define

\[
J_m=\sum_{i<m}(i,m),\qquad s=(n-1,n).
\]

Conjugation gives

\[
sJ_{n-1}s=\sum_{i<n-1}(i,n)=J_n-s,
\]

hence

\[
J_n=sJ_{n-1}s+s.
\]

Multiplying on the left by \(s\) yields

\[
\boxed{sJ_n-J_{n-1}s=1.}
\]

There is no missing sign or transposition factor.

### 2.2 Young branching and the rank of the filtered subspace

Fix an irreducible \(S^\nu\) and write \(Q=\rho_\nu(b)\).

If \(\nu\) does not cover \(\beta\), the restriction of \(S^\nu\) to \(S_{n-1}\) contains no \(S^\beta\), so \(Q=0\).

If \(\nu\succ\beta\), the multiplicity-free Young branching rule first selects one \(S^\beta\) and then one \(S^\gamma\) inside it. Therefore

\[
\operatorname{Tr}Q=\dim\operatorname{im}Q=f^\gamma.
\]

Put

\[
u=c(\nu\setminus\beta),\qquad c=c(\beta\setminus\gamma).
\]

On the selected subspace the Jucys–Murphy operators act by their content eigenvalues:

\[
J_nQ=uQ,\qquad J_{n-1}Q=cQ.
\]

The corresponding left-sided identities follow from the same spectral decomposition, or by adjointness.

Multiplying the group-algebra identity by \(Q\) and taking trace gives

\[
\begin{aligned}
\operatorname{Tr}Q
&=\operatorname{Tr}(sJ_nQ)-\operatorname{Tr}(J_{n-1}sQ)\\
&=u\,\operatorname{Tr}(sQ)-c\,\operatorname{Tr}(Qs)\\
&=(u-c)\operatorname{Tr}(Qs).
\end{aligned}
\]

Since \(Q^2=Q\), cyclicity gives

\[
\operatorname{Tr}(QsQ)=\operatorname{Tr}(Qs).
\]

Hence

\[
\boxed{
\operatorname{Tr}_{S^\nu}(bsb)
=\frac{f^\gamma}{c(\nu\setminus\beta)-c(\beta\setminus\gamma)}.
}
\]

This is the claimed trace/content formula.

### 2.3 The denominator is always nonzero

Suppose the removable box \(\beta\setminus\gamma\) is in row \(r\). Its content is

\[
c=\beta_r-r.
\]

An addable box of \(\beta\) in row \(i\) has content

\[
u=\beta_i+1-i,
\]

where a trailing zero part is allowed for a new row. Then

\[
u-c=\beta_i-\beta_r+1+r-i.
\]

If \(i\le r\), this is strictly positive. If \(i>r\), removability implies \(\beta_r>\beta_{r+1}\ge\beta_i\), so

\[
u-c\le r-i<0.
\]

Thus \(u-c\ne0\) in all cases.

## 3. Normalization from irreducible traces to raw immanants

The central average has the irreducible expansion

\[
Z(W)=\sum_{\nu\vdash n}\frac{t_\nu}{f^\nu}e_\nu,
\qquad
t_\nu=\operatorname{Tr}_{S^\nu}(W).
\]

For a Gram tensor,

\[
\langle x,e_\nu x\rangle=\frac{f^\nu}{n!}d_\nu(A).
\]

Therefore

\[
\langle x,Z(W)x\rangle
=\frac1{n!}\sum_{\nu\vdash n}t_\nu d_\nu(A).
\]

The factor \(f^\nu\) cancels. Consequently the coefficient of the **raw immanant** \(d_\nu\) is the irreducible trace \(t_\nu\), not \(t_\nu/f^\nu\).

Substituting the branching trace gives

\[
\langle x,Z(W)x\rangle
=
\frac{f^\gamma}{n!}
\sum_{\nu\succ\beta}
\frac{d_\nu(A)}{c(\nu\setminus\beta)-c(\beta\setminus\gamma)}\ge0.
\]

Dividing by the positive common factor proves the displayed branching inequality.

For the central-projector witnesses, with \(E=e_\alpha\otimes e_\beta\), cyclicity and \(E^2=E\) give

\[
\operatorname{Tr}(E\tau_kE)=\operatorname{Tr}(\tau_kE),
\]

so

\[
t_\nu=\frac{f^\alpha f^\beta}{p!q!}F_{\alpha,\beta,k}(\nu).
\]

The proportionality factor is positive and independent of \(\nu\). For \(k=1\), averaging one cross-block transposition gives the equivalent content/Littlewood–Richardson expression

\[
t_\nu=\frac{f^\alpha f^\beta}{pq}
 c_{\alpha\beta}^{\nu}
(\kappa_\nu-\kappa_\alpha-\kappa_\beta),
\]

so the primitive integer normalization used by the verifier preserves the inequality direction.

No normalization error was found in the supplied proof or certificate.

## 4. Full complex Hermitian PSD cone, including singular matrices

Every complex Hermitian positive-semidefinite matrix has a Gram representation. The positivity proof above is stated directly for arbitrary Gram vectors and nowhere assumes that those vectors are linearly independent, that \(A\) is invertible, or that \(\det A>0\).

Therefore singular PSD matrices are included directly. No approximation by positive-definite matrices or continuity argument is needed.

## 5. Independent verification of the 125-witness certificate

### 5.1 Supplied verifier

The supplied `verify.py` and `exact_algebra.py` were inspected and rerun. The supplied verifier reconstructs the witnesses rather than merely trusting the success log. The rerun passed and is preserved as `supplied_verifier_rerun.log`.

### 5.2 Independent reconstruction route

The independent verifier imports none of the supplied algebra code.

Its character computation is substantially independent: it expands Schur functions through the Jacobi–Trudi determinant and evaluates products of complete homogeneous symmetric functions as induced trivial characters by assigning permutation cycles to labelled block capacities. This differs from the supplied Murnaghan–Nakayama implementation.

Dimensions are independently computed by recursive Young branching, rather than the supplied hook-length code.

For the central character sums, the independent implementation constructs concrete block permutations, composes them with the actual cross-block swaps on all 15 labels, and traverses the resulting permutation cycles directly. It does not use the supplied marked-cycle length formula. Both implementations share the mathematically justified orbit-compression principle; that common principle was separately checked against exhaustive permutation enumeration in 12 small block configurations: every allowed swap number for \((2,3)\), \((3,3)\), \((3,4)\), and \((4,4)\).

The independent run established:

- character tables and dimensions through order 15 passed exact checks;
- all 19 branching-refined witnesses were regenerated;
- all 106 selected central witnesses were regenerated from defining character sums;
- 43 selected symmetric-block rows were also checked by the independent content-polynomial formula;
- every stored primitive vector agreed exactly;
- the primitive sign convention was preserved;
- all 125 multipliers were strictly positive integers;
- every witness satisfied the exact dimension-balance relation;
- all 176 final partition coordinates were checked exactly.

The final vector has exactly two nonzero coordinates:

\[
(15):\quad 6006M,
\qquad
(3,3,3,3,3):\quad -M,
\]

with

```text
M = 2622150535278170077084028849035651351078346354137625907361158186255438546087020178852205591785682843258976630527200.
```

Every other one of the 176 coordinates is exactly zero.

The target dimension is

\[
f^{(3^5)}=\frac{15!}{217728000}=6006.
\]

Thus the exact identity is

\[
\sum_{i=1}^{125}z_iR_i
=M\bigl(6006\operatorname{per}-d_{(3^5)}\bigr),
\qquad z_i>0,\ M>0.
\]

Since every \(R_i\) is nonnegative on the full complex PSD cone, this proves the theorem.

### 5.3 Direct finite checks of the branching trace formula

As a supplementary check independent of the universal algebraic proof, the branching trace was expanded directly as a group-algebra character sum at orders 2 through 6. There were 209 exact comparisons with the content formula, and all passed. These finite checks are corroborative; the theorem itself rests on the general proof in Sections 1–2.

## 6. Independent regeneration of the old central cone and the escape witness

The supplied rectangular verifier checks the negative pairing of the selected branching term with a stored separator, but does not regenerate every generator of the old central cone. The independent cone verifier filled that gap.

It regenerated the complete order-15 central-projector partial-swap cone and obtained exactly:

\[
8112\text{ parameter labels},\qquad
1310\text{ zero labels},\qquad
5398\text{ distinct nonzero primitive rays}.
\]

Every regenerated central ray had nonnegative dimension-weighted pairing with the stored separator. The minimum pairing was exactly

\[
98.
\]

The separator also had the required signs on all other order-15 PDC rays, the individual immanant-nonnegativity rays, and the Schur lower-bound rays.

For the certificate’s term 120,

\[
\beta=(4,4,4,1,1),\qquad
\gamma=(4,4,3,1,1),
\]

the removed content is \(1\), while the addable contents are \(4,-2,-5\). The primitive branching inequality is

\[
2d_{(5,4,4,1,1)}
-2d_{(4,4,4,2,1)}
-d_{(4,4,4,1,1,1)}\ge0.
\]

The dimensions are

\[
100100,\qquad 75075,\qquad 50050.
\]

After division by \(50050\), the normalized-coordinate vector is

\[
4\bar d_{(5,4,4,1,1)}
-3\bar d_{(4,4,4,2,1)}
-\bar d_{(4,4,4,1,1,1)}.
\]

On these coordinates the old separator has values \(3726,4911,2501\), so the pairing is

\[
4(3726)-3(4911)-2501=-2330.
\]

Equivalently, the primitive raw vector has dimension-weighted pairing

\[
-116616500.
\]

Hence a branching-refined witness actually used in the certificate lies outside the regenerated central cone and its stated enlargement. This is a genuine cone enlargement, not merely an unused illustrative example.

This does **not** by itself prove independence from every inequality that may occur anywhere in Pate’s papers.

## 7. Order-15 closure

Pate’s stated class

\[
(p,q^w,r,2^s,1^t),\qquad 0\le w\le2,
\]

leaves exactly three order-15 partitions outside the class:

\[
(5,4,3,3),\qquad
(4,4,3,3,1),\qquad
(3,3,3,3,3).
\]

The audit independently regenerated the preceding note’s seven-witness bridge for \((5,4,3,3)\), both from the content formula and from the defining central character sums, and checked all 176 coordinates. The normalized consequence is

\[
\bar d_{(5,4,3,3)}
\le
\frac{
630\bar d_{(9,3,3)}
+791\bar d_{(8,4,3)}
+54\bar d_{(7,5,3)}
+10\bar d_{(7,4,4)}
}{1485}.
\]

The coefficients are nonnegative and sum to one. The right-hand partitions have three rows and belong to the stated previously established PDC class.

Pate’s normalized node-moving theorem then gives

\[
\bar d_{(4,4,3,3,1)}
\le
\bar d_{(5,4,3,3)}.
\]

The new 125-witness certificate handles the remaining rectangle \((3^5)\). Thus all order-15 ordinary-immanant cases are accounted for.

For the broader phrase “through order 15,” enumeration of the stated Pate class leaves no exception through order 13 and only \((4,4,3,3)\) at order 14. The preceding note explicitly treats that order-14 case as established input, but its original proof was not among the supplied materials. Accordingly:

- the order-15 closure is independently checked here;
- the theorem for \((3^5)\) is self-contained relative to the two universal witness-positivity mechanisms;
- the global statement “through order 15” retains the external dependency on the accepted order-14 proof.

## 8. Literature-priority audit

Mathematical correctness and historical novelty are separate questions.

### 8.1 Classical representation-theoretic antecedent

Vershik–Okounkov’s treatment of the Young graph and seminormal/orthogonal representations gives both branching-path projections and the reciprocal adjacent-content coefficient. Summing the classical diagonal coefficient over the \(f^\gamma\) tableaux sharing the retained branching path yields the same

\[
\frac{f^\gamma}{c(\nu\setminus\beta)-c(\beta\setminus\gamma)}
\]

trace. Therefore this coefficient formula should not be advertised as new representation theory.

The primary reference inspected during the audit was:

A. M. Vershik and A. Yu. Okounkov, *A New Approach to the Representation Theory of the Symmetric Groups. II*, arXiv:math/0503040v3.

### 8.2 Pate 1992/1997/1998/1999

The accessible literature established the following, while leaving some priority questions unresolved:

- **Pate 1992:** the publisher abstract supports the normalized node-moving theorem used in the order-15 closure. The full article was not inspected.
- **Pate 1997:** the bibliographic record for *A machine for producing inequalities involving immanants and other generalized matrix functions* was verified, but the full text was unavailable. Whether the present branching-refined inequality is already an instance of that general machine therefore remains unresolved.
- **Pate 1998:** publication metadata were verified; its relevant partition family is described by Pate’s subsequent 1999 abstract. Full-text equivalence checks were not performed.
- **Pate 1999:** the primary abstract explicitly describes tensor-contraction and quadratic-form antecedents and states the class \((p,q^w,r,2^s,1^t)\), \(0\le w\le2\). It also mentions a separate \((n+p,n^k)\) family for sufficiently large \(n\). The exact quantitative hypothesis of that theorem could not be inspected. In particular, one must check whether \(n=3,p=0,k=4\) is permitted before conclusively claiming that \((3^5)\) was not already covered.

Subsequent operator/Gram formulations of immanant inequalities also provide significant antecedents. No earlier explicit proof of the \((3^5)\) inequality was located in the accessible material, but absence from the accessible search is not a priority proof.

### 8.3 Priority verdict

The reliable priority conclusion is therefore:

- the projection/content representation ingredients are classical;
- tensor-contraction and operator formulations have substantial antecedents;
- the exact branching-refined positivity family may be new, but this audit did not establish that historical claim;
- the explicit \((3^5)\) consequence was not found in the literature checked, but prior occurrence was not conclusively excluded.

None of these historical uncertainties affects the mathematical correctness of the audited proof.

## 9. Issue classification

### Fatal errors

None found.

### Substantive but repairable mathematical gaps

None found in the rectangular proof or its exact certificate.

For a paper making the broader “through order 15” statement, the order-14 dependency should be explicitly supplied or cited. For a paper making a novelty claim, the unresolved Pate full-text comparisons should be completed. These are documentation and priority issues, not missing steps in the \((3^5)\) proof.

### Minor issues

No incorrect coefficient, sign, dimension factor, projection identity, or singular-PSD omission was found.

### Optional improvements

- Ship the independent full-cone verifier with the public certificate package.
- Cite the classical Young/seminormal reciprocal-content coefficient at first use.
- Preserve checksums and a versioned immutable certificate.
- If desired, formalize the finite certificate and/or representation-theoretic lemmas in a proof assistant; this would strengthen assurance but is not necessary for the current exact proof to be valid.

## 10. Public-circulation readiness

The following central claim is mathematically supported by the audited proof and exact certificate:

> For every complex Hermitian positive-semidefinite \(15\times15\) matrix \(A\), including singular matrices,
> \[
> d_{(3,3,3,3,3)}(A)\le6006\operatorname{per}(A).
> \]
> The proof is an exact positive combination of 106 central-projector partial-swap witnesses and 19 branching-refined one-swap witnesses.

Before public circulation, the proof should be accompanied by the exact certificate, the supplied verifier, the independent verifier, the cone-regeneration check, and a precise dependency note for the prior order-14 case. Historical novelty should be stated cautiously until the outstanding older full-text comparisons are completed.

No mathematical repair of the rectangular theorem was indicated by this audit.
