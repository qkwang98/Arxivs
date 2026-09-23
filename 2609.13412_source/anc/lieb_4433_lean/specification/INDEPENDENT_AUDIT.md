## Verdict

**The final argument establishes the claimed theorem.** No fatal error or substantive mathematical gap survived my audit.

The universal positivity argument is valid for complex Hermitian PSD matrices, the twenty-witness certificate checks exactly, the normalization produces the stated convex combination, and the four right-hand partitions satisfy the published Pate coverage criterion.

There is one source-access qualification: I verified the exact theorem statement and matrix domain in its published 2022 restatement, but could not retrieve Pate’s original 1999 paper. I distinguish that limitation from a mathematical gap below.

The detailed report and independently written verification code are available here:

:chatgpt-content-reference{index="6"} · :chatgpt-content-reference{index="7"}

### Answers to the six requested questions

| Question | Conclusion |
|---|---|
| 1. Is the bridge inequality valid for every complex Hermitian PSD matrix? | **Yes.** The proposed partial-transpose argument is valid. I also reconstructed a direct squared-norm proof that avoids partial transpose entirely. |
| 2. Is the exact twenty-witness certificate correct? | **Yes.** All twenty rows, positive rational weights, omitted coefficients, and the final cancellation checked exactly. |
| 3. Does the existing literature cover all four right-hand immanants? | **Yes.** Each satisfies the precise Pate criterion stated in the published literature. The original-paper access limitation is explained below. |
| 4. Does the argument prove the complete \((4,4,3,3)\) case? | **Yes.** No rank, reality, support, spectrum, or nonsingularity restriction remains. |
| 5. Does this imply ordinary-immanant permanental dominance through order \(14\)? | **Yes.** A short partition-size argument confirms that this is the only exception to the imported criterion in that range. |
| 6. What remains before public circulation? | No mathematical repair was identified. There is a minor reproduction-command correction. More precise bibliographic pinpointing and inclusion of the direct contraction proof would improve presentation, but are not missing proof steps. |

## 1. The universal positivity mechanism is valid

The proof does **not** make the invalid claim that partial transpose preserves positive semidefiniteness. Instead, it starts with a positive operator \(Y\), partially transposes it, and establishes nonnegativity of the resulting operator \(W\) only on the product tensors that are needed.

That distinction is correctly maintained.

### The partially transposed swap has the right normalization

For a swap \(F\) on two \(d\)-dimensional factors,
\[
F=\sum_{i,j}|i\rangle\langle j|\otimes|j\rangle\langle i|,
\]
so
\[
F^{\Gamma_R}
=\sum_{i,j}|ii\rangle\langle jj|
=|\Omega\rangle\langle\Omega|,
\qquad
\Omega=\sum_i|ii\rangle.
\]

The vector \(\Omega\) is unnormalized. Thus there is no missing factor of \(d\): such a factor would appear only after replacing \(\Omega\) by its normalized version. This agrees with the standard convention in the cited partially transposed permutation literature. citeturn593041view0

For \(k=2\), the proof transposes **both** right-hand factors. The two disjoint transposed swaps therefore give the product of two positive rank-one operators. The index convention for \(\tau_k\) matches the full swap between the \(k\)-factor blocks \(L\) and \(R\).

Since \(P\) acts only on \(O\), it commutes with \(E\), and \(PE\succeq0\). Hence
\[
Y=(QB)(PE)(QB)^*\succeq0.
\]

### The sandwich identity is legitimate

The rule used is
\[
[(C\otimes D)X(C\otimes D)]^{\Gamma_R}
=(C\otimes D^T)X^{\Gamma_R}(C\otimes D^T).
\]

This is a local sandwich identity, not a multiplicativity rule for arbitrary products. Here \(Q\) acts on \(O\cup L\), \(B\) acts on \(R\), and \(B^T=B\). Therefore the asserted identity
\[
Y^{\Gamma_R}=QB\,P U_{\tau_k}\,BQ=W
\]
is correct.

For a bipartite product \(x\otimes y\),
\[
\langle x\otimes y,Y^{\Gamma_R}(x\otimes y)\rangle
=
\langle x\otimes\overline y,Y(x\otimes\overline y)\rangle
\ge0.
\]
Only the right-hand factor is conjugated. This is valid for arbitrary complex coordinates.

### An independent proof without partial transpose

This provides a substantially independent verification of the most vulnerable analytic step.

Identify the tensor space with
\[
\mathcal H_O\otimes\mathcal K_L\otimes\mathcal K_R,
\qquad \mathcal K_L\cong\mathcal K_R.
\]
Let \(F\) swap the two \(\mathcal K\) factors.

Because \(P^2=P\) and \(P\) commutes with \(Q,B,U_{\tau_k}\), we can write
\[
W=K U_{\tau_k}K,
\qquad K=(PQ)\otimes B.
\]

For the product tensor under consideration, set
\[
x=v_{O\cup L},\qquad y=v_R,\qquad
u=PQx,\qquad z=By.
\]
Expand
\[
u=\sum_a e_a\otimes u_a
\]
in an orthonormal basis of \(\mathcal H_O\). Then
\[
\begin{aligned}
\langle v,Wv\rangle
&=\langle u\otimes z,(I_O\otimes F)(u\otimes z)\rangle\\
&=\sum_a\langle u_a,z\rangle\langle z,u_a\rangle\\
&=\sum_a|\langle z,u_a\rangle|^2\\
&=\big\|(I_O\otimes\langle z|)u\big\|^2
\ge0.
\end{aligned}
\]

Importantly, this does not assume that \(u\) remains decomposable after applying \(PQ\). Nor does it assume that \(z\) remains decomposable within the right-hand block after applying the alternating projector.

Thus the universal positivity claim survives a direct verification that uses neither partial transpose nor the supplied computational implementation.

## 2. The trace-to-immanant conversion has the correct factors

This is another place where a plausible-looking certificate could have proved the wrong inequality. I checked the conventions explicitly.

With the stated tensor action and the inner product conjugate-linear in its first variable,
\[
\langle v,U_\sigma v\rangle
=\prod_i A_{i,\sigma^{-1}(i)}.
\]
Consequently,
\[
\begin{aligned}
\langle v,P_\nu v\rangle
&=\frac{f^\nu}{n!}
  \sum_\sigma\chi^\nu(\sigma^{-1})
  \prod_i A_{i,\sigma^{-1}(i)}\\
&=\frac{f^\nu}{n!}d_\nu(A),
\end{aligned}
\]
by substituting \(\sigma\mapsto\sigma^{-1}\).

So the inverse convention produces exactly the immanant in the theorem. It does not introduce an unintended transpose, complex conjugation, or character normalization.

Now write
\[
h_\nu=\operatorname{Tr}_{V^\nu}\rho_\nu(W).
\]
Central averaging gives
\[
\mathcal Z(W)
=\sum_{\nu\vdash n}\frac{h_\nu}{f^\nu}P_\nu,
\]
and therefore
\[
\langle v,\mathcal Z(W)v\rangle
=\frac1{n!}\sum_{\nu\vdash n}h_\nu d_\nu(A).
\]

There are two essential consequences:

* The factor \(f^\nu\) cancels.
* The resulting coefficients multiply the **unnormalized** immanants \(d_\nu\).

There is no extra Schur–Weyl multiplicity. The trace is taken on one irreducible symmetric-group module, while \(P_\nu\) already acts on the whole tensor-space isotypic component.

Central averaging also preserves the required positivity: every permutation of a fully decomposable tensor remains fully decomposable. No claim that \(\mathcal Z(W)\) is PSD on all tensors is necessary.

### The \(f^\eta\) factor is also correct

The cyclic trace reduction is
\[
\operatorname{Tr}(QBP\tau BQ)
=\operatorname{Tr}(BQ^2BP\tau)
=\operatorname{Tr}(QBP\tau).
\]
It does not require commuting \(\tau\) past \(Q\).

On restriction to \(S_{n-2k}\),
\[
P_\eta V^\nu\cong V^\eta\otimes M_{\nu/\eta}.
\]
The relevant operators commute with this subgroup and act trivially on \(V^\eta\). Thus
\[
h_\nu
=f^\eta\operatorname{tr}_{M_{\nu/\eta}}(D_\mu B\tau)
=f^\eta t^\nu.
\]

It follows that
\[
\frac{f^\eta}{n!}\sum_\nu t^\nu d_\nu(A)\ge0.
\]
Dividing by the positive factor \(f^\eta/n!\) proves the witness inequality exactly as stated.

The proof has not forgotten \(f^\eta\). It removes that positive factor separately for each witness, which is legitimate before taking a positive combination of the witnesses.

Combining this calculation with the direct contraction proof even gives an explicit sum-of-squares identity:
\[
L(A)=\frac1{f^\eta}\sum_{\pi\in S_n}
\big\|(I_O\otimes\langle B y_\pi|)PQx_\pi\big\|^2,
\]
where
\[
U_\pi^{-1}v=x_\pi\otimes y_\pi
\]
is split into \((O\cup L)|R\).

This independently confirms both positivity and the remaining normalization.

## 3. The representation matrices compute the intended witnesses

The column-minus-row content convention, the diagonal
\[
\frac1{a_{i+1}-a_i},
\]
and the orthogonal off-diagonal coefficient
\[
\sqrt{1-\frac1{(a_{i+1}-a_i)^2}}
\]
agree with the standard Young representation convention. The cited background uses the same content and axial-distance definitions. citeturn593041view3turn593041view1

The intermediate projector \(Q\) becomes the diagonal selector \(D_\mu\), with eigenvalues \(0\) and \(1\). There is no additional factor \(f^\mu\) to insert: that normalization is already present in the central idempotent defining \(Q\).

For the last four labels,
\[
(1\ 3)(2\ 4)=s_2s_1s_3s_2,
\]
and the right-hand projector is
\[
B=\frac12(I+\varepsilon S_3).
\]
Moreover, \(S_3\) preserves the shape after the first two added boxes, so it commutes with \(D_\mu\).

Hence the displayed formula
\[
t^\nu
=\frac12\operatorname{tr}
\!\left[D_\mu(I+\varepsilon S_3)S_2S_1S_3S_2\right]
\]
is the trace of the actual positivity witness.

Using rational seminormal coordinates causes no positivity problem. Those matrices need not look orthogonal in the ordinary Euclidean inner product, but they are used only to compute representation-invariant traces. Positivity was established in the original Hilbert-space representation.

## 4. The exact certificate passed both supplied and independent checks

I inspected every supplied Python source and ran the complete suite under Python 3.13.5. All nine manifest entries matched. I also reran the suite with bytecode-cache lookup redirected to a fresh location, avoiding the supplied compiled `.pyc` file. That source-only run passed as well.

### What the supplied scripts actually verify

| Script | Verified scope | Limitation |
|---|---|---|
| `verify_certificate.py` | Regeneration of twenty rows in two representation forms; exact agreement with stored rows; positive weights; cancellation; degrees; diagonal identities; convex weights; partition enumeration | The two representation paths share tableau and trace infrastructure. The encoded Pate criterion is not a literature verification. |
| `operator_identity_checks.py` | Exact sandwich and complex product-expectation identities in a four-qubit model, for both signs | A finite model checks conventions but does not prove the universal identities. |
| `adversarial_exact_checks.py` | Literal character sums at four small-order settings, plus one exact complex order-fourteen PSD example | It shares some helpers with the main verifier. The matrix test is supplementary, not a universal proof. |

The small-group character-sum tests checked \(6,4,6,20\) witness choices at
\[
(n,k)=(4,1),(4,2),(5,2),(6,2),
\]
respectively.

The order-fourteen stress test enumerated 8,630 supported permutations over 50 conjugacy types. Its regenerated bridge slack was
\[
67\,267\,064\,932\,170\,752.
\]
All twenty witness values were nonnegative. The rank-thirteen and PSD assertions for that matrix rest on the triangle decomposition and common-kernel argument, rather than a formal rank/positivity proof inside the script.

### The independent reconstruction

The new checker imports none of the supplied verification code. It:

- reads the parameters and expanded witness forms directly from `FINAL_PROOF.md`;
- generates branching paths by adding outer corners, constructs full exact rational matrices, and factors the literal swap automatically;
- computes the full sandwich, checks the cyclic trace reduction and Coxeter relations, and computes degrees by branching rather than the hook formula.

The outcome was:

\[
\begin{array}{ll}
\text{Witness/partition coefficient positions checked:}&2700,\\
\text{Branching blocks checked:}&377,\\
\text{Largest matrix dimension:}&24.
\end{array}
\]

All printed parameters, all twenty Appendix A rows, and the JSON agree. The rows have 104 nonzero entries across 24 distinct partitions; all other coefficients are accounted for as zero.

This implementation still uses standard Young representation theory. Its independence is computational, not a separate foundation for that theory. The direct squared-norm proof above supplies the independent analytic route.

### The final coefficient identity is exact

Both implementations reproduce
\[
\begin{aligned}
\sum_{j=1}^{20}w_jL_j
={}&4035d_{653}+6725d_{644}+39759d_{554}\\
&+23636d_{5333}-59512d_{4433}.
\end{aligned}
\]
Every other coefficient is zero, and every \(w_j\) is strictly positive.

Therefore the universal witness inequalities prove precisely the bridge inequality claimed in the paper.

## 5. The normalization gives the stated convex combination

The independently computed degrees are
\[
(f^{4433},f^{653},f^{644},f^{554},f^{5333})
=(12012,15015,9009,6006,15015).
\]

The common diagonal normalization is
\[
\begin{aligned}
59512\cdot12012
&=714858144\\
&=4035\cdot15015+6725\cdot9009\\
&\quad+39759\cdot6006+23636\cdot15015.
\end{aligned}
\]

Thus the bridge becomes exactly
\[
\bar d_{4433}\le
\frac{20175}{238048}\bar d_{653}
+\frac{20175}{238048}\bar d_{644}
+\frac{79518}{238048}\bar d_{554}
+\frac{118180}{238048}\bar d_{5333}.
\]

All four coefficients are positive, and
\[
20175+20175+79518+118180=238048.
\]

This is genuinely a convex combination of normalized immanants. It is not merely an unnormalized inequality from which the desired conclusion would fail to follow.

## 6. The external theorem covers all four partitions

I checked the published Divya–Somasundaram PDF, including the matrix domain and normalization on page 85 and Theorem 3.1 on page 88. The domain is complex Hermitian PSD matrices, with normalization by character degree. citeturn160871view4

The stated Pate criterion covers partitions with at most three parts exceeding two, and those with four such parts when the second and third are equal. citeturn160871view3

Its application here is immediate:

| Partition | Applicable condition |
|---|---|
| \((6,5,3)\) | Three parts exceeding two |
| \((6,4,4)\) | Three parts exceeding two |
| \((5,5,4)\) | Three parts exceeding two |
| \((5,3,3,3)\) | Four such parts; second and third both equal \(3\) |

Accordingly, each normalized term on the right of the bridge is bounded by \(\operatorname{per}(A)\).

**Source-access qualification:** the original 1999 paper was not retrievable through the available journal endpoints. I therefore verified the precise published restatement and its hypotheses, rather than Pate’s original proof. This is not the same as merely accepting a Boolean criterion in the supplied code. It is sufficient to confirm the stated application of an established published theorem, while leaving a clearly identified bibliographic check available for additional assurance.

Wanless’s account independently corroborates the historical ordinary-immanant result through order thirteen and distinguishes it from the much broader subgroup conjecture; I did not substitute that historical summary for the exact four-part criterion. citeturn668483view4

### Why this covers every ordinary immanant through order fourteen

This consequence can be verified without trusting the partition-enumeration code.

A partition with five parts exceeding two has size at least \(15\).

A partition with four such parts that fails the equality condition has
\[
a\ge b>c\ge d\ge3,
\]
and therefore
\[
a+b+c+d\ge4+4+3+3=14.
\]
At total size at most fourteen, equality forces
\[
(a,b,c,d)=(4,4,3,3),
\]
with no additional parts.

Thus the target is the only exception to the imported criterion in the entire range \(n\le14\). Proving it completes that range.

## 7. Findings and readiness for circulation

**Fatal errors:** none found.

**Substantive but repairable gaps:** none found.

**Minor issue:** the root-level `FINAL_PROOF.md` says to run `python verify_all.py` “from this directory,” but the script is actually in `exact_certificate`. Following that instruction literally from the packet root produces a file-not-found error. The root-level command should be
```sh
python exact_certificate/verify_all.py
```
or the instruction should first change into that subdirectory.

This is a reproduction-instruction issue, not a mathematical defect.

**Optional improvements:** include the direct contraction proof above as an alternative to partial transpose, and make the imported theorem’s precise citation especially easy to locate. Checking Pate’s original theorem when accessible would strengthen bibliographic assurance. None of these is a missing mathematical repair.

No additional rank analysis, numerical search, or special-family testing is needed to make the present argument universal. Every PSD matrix is handled directly as a Gram matrix in \(\mathbb C^{14}\), including singular matrices and zero Gram vectors.

The result is suitable to circulate as a proof with an exact certificate, subject to ordinary further expert scrutiny. The conclusion should remain scoped to **ordinary-immanant permanental dominance through order fourteen**, not the full Lieb conjecture. The audit supports a completed proof of the stated case, not merely a promising computational certificate.
