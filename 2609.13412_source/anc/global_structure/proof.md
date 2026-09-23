# Structural results for ordinary-immanant permanental dominance

Research continuation, 11 September 2026

## Scope and status

The supplied partial-swap positivity theorem, Pieri/content formula, branching-refined one-swap theorem, the family (m,4,3,3), and the order-15 proof are working inputs. They are not reproved here. All statements concern complex Hermitian positive-semidefinite matrices, including singular matrices, and ordinary irreducible characters of the full symmetric group.

The new results of this continuation are:

1. A uniform, explicitly bounded long-first-row PDC theorem for an arbitrary tail, with a convex dominance formula and a proof by decreasing tail size.
2. A two-witness PDC theorem for (a,b,3,3), for all integers a>=b>=4 with 5a>=8b. Its sign proof is an exact symbolic certificate, not interpolation from finite orders.
3. An exact description of node-moving closure for the explicitly specified theorem classes, and exact enumeration of that closure for orders 16 through 30.
4. A density-zero theorem for this family-and-node-moving program, even after optimistically granting PDC for every rectangular-tail shape.
5. A boundary-compression theorem for arbitrary local partial-swap filters. At fixed swap size k, only the final k branching steps of each block can matter; the retained positive matrices have order at most k!.
6. As a special case, an exact saturation theorem: arbitrary local filters in the (n-1,1) one-swap architecture generate precisely the already established two-step branching cone.

This does not prove PDC for every partition, does not classify the unrestricted partial-swap cone, and does not prove that finitely many general mechanisms are impossible. Historical priority for the explicit new formulas has not been established. The new arguments and arithmetic certificates have been checked in this run, but not externally audited or formally verified.

### Important boundary on the frontier counts

The exact coverage set in Sections 5–6 is defined by the unconditional explicit Pate class (at most three parts above 2, or four with the middle two equal), the supplied (m,4,3,3) family, the supplied finite results, the two new theorems, and Pate's 1992 one-node-to-a-singleton operation. It is not advertised as the closure under every inequality in every Pate paper. In particular, Pate's 1999 abstract also reports sufficiently-wide rectangular-tail results, but the accessible material did not supply their quantitative threshold. Those are not inserted into the numerical membership predicate. Nor are unsearched positive combinations or induction/restriction consequences inserted by assumption.

The density result is stronger in this respect: it remains true after granting *all* rectangular-tail shapes, without a width threshold. The residual lists are therefore coverage records for a precisely specified theorem system, not lists of partitions declared mathematically open.

## 1. Notation and the accepted positivity input

For a partition lambda of n, write f^lambda=chi^lambda(1), d_lambda for the raw immanant, and dbar_lambda=d_lambda/f^lambda. The permanent is d_(n).

For a box in row i and column j, its content is j-i. Define

\[
\kappa_\rho=\sum_{b\in\rho}c(b),\qquad
C(\rho)=\max\{\rho_i-i:\rho_i>\rho_{i+1}\},
\]

where the next part after the last is zero. Thus C(rho) is the greatest content of a removable box. The empty partition will be treated separately.

For a horizontal p-strip nu/beta, let

\[
P_{\nu/\beta}(z)=\prod_{b\in\nu/\beta}(z+c(b)),
\]

and define

\[
N^\nu_{p,\beta,k}
=\frac{1}{(p-k)!}\sum_{j=0}^{p-k}
(-1)^{p-k-j}\binom{p-k}{j}P_{\nu/\beta}(j-p+1).
\tag{1.1}
\]

Set the coefficient to zero outside horizontal strips. The accepted theorem states that

\[
\Phi_{p,\beta,k}(A)=\sum_\nu N^\nu_{p,\beta,k}d_\nu(A)\ge0,
\quad 1\le k\le\min(p,|\beta|),
\tag{1.2}
\]

and that it is balanced:

\[
\sum_\nu f^\nu N^\nu_{p,\beta,k}=0.
\tag{1.3}
\]

For k=1 the coefficient has the especially simple form

\[
N^\nu_{p,\beta,1}=\kappa_\nu-\kappa_\beta-\binom p2.
\tag{1.4}
\]

All new convex normalizations below follow from (1.3), rather than from a numerical sum close to one.

## 2. The arbitrary-tail long-first-row theorem

### Theorem 2.1

Let rho be any nonempty partition of q, and let m be an integer satisfying

\[
m\ge\rho_1,\qquad m\ge q+C(\rho)-1.
\tag{2.1}
\]

Then ordinary PDC holds for lambda=(m,rho).

More precisely, range over partitions tau contained in rho for which rho/tau is a nonempty horizontal strip. Put j=q-|tau| and

\[
\nu_\tau=(m+j,\tau),
\]

\[
R_{m,\rho}(\tau)
=jm+\binom j2-\sum_{b\in\rho/\tau}c(b)-q+j.
\tag{2.2}
\]

Then R is nonnegative, and the exact convex bridge is

\[
\boxed{
\bar d_{(m,\rho)}(A)
\le\sum_{\tau\ne\rho}
\frac{R_{m,\rho}(\tau)f^{(m+j,\tau)}}{q f^{(m,\rho)}}
\bar d_{(m+j,\tau)}(A).
}
\tag{2.3}
\]

The coefficients sum to one. Every right-hand shape satisfies the same long-first-row criterion and has a strictly smaller tail. Thus repeated substitution terminates at the permanent.

Among m>=rho_1, condition m>=q+C(rho)-1 is also the exact threshold at which the single witness Phi_(m,rho,1) has no negative coordinate other than (m,rho).

### Proof

Pieri interlacing says that every child nu of rho under a horizontal m-strip can be written uniquely as nu=(m+j,tau), where rho/tau is a horizontal j-strip. The child with j=0 is exactly (m,rho).

Shifting every row of tau down by one changes its total content by -|tau|. Hence

\[
\kappa_{(m+j,\tau)}=\binom{m+j}{2}+\kappa_\tau-|\tau|.
\]

Substituting into (1.4) gives (2.2). For j=0 the coefficient is -q.

If a box is removed from row i by a horizontal strip, then rho_i>rho_(i+1), and the content of that box is at most rho_i-i<=C(rho). Consequently

\[
\sum_{b\in\rho/\tau}c(b)\le jC(\rho).
\]

Under (2.1),

\[
R_{m,\rho}(\tau)
\ge j(q-1)+\binom j2-q+j
=(j-1)q+\binom j2\ge0.
\tag{2.4}
\]

Therefore (1.2) gives q d_(m,rho)<=sum R d_nu. Dividing by q f^(m,rho) and using balance proves (2.3) and the sum-one assertion.

It remains to justify the induction, without assuming PDC for unspecified other shapes. Removing a single outer corner can introduce a new removable corner only immediately above or immediately to the left of it. The new maximal removable content can therefore increase by at most one. After removing j boxes,

\[
C(\tau)\le C(\rho)+j
\]

whenever tau is nonempty. It follows that

\[
|\tau|+C(\tau)-1\le q+C(\rho)-1\le m<m+j.
\]

Also m+j>=tau_1. Every nonempty right-hand tail therefore satisfies (2.1). Strong induction on q, uniform over m and the matrix order m+q, proves PDC. The empty tail is the permanent. No induction on consecutive matrix orders is used.

For sharpness of the one-witness threshold, remove a box of content C(rho). Its j=1 child has coefficient m-q-C(rho)+1. This is negative when m<q+C(rho)-1. This establishes the stated threshold, not a no-go theorem for positive combinations of several witnesses. QED.

### Consequences

For every fixed tail rho, only finitely many first-row lengths remain outside this theorem. Some recognizable subfamilies are

\[
(a,k^r),\qquad a\ge k,\quad a\ge(r+1)(k-1),
\tag{2.5}
\]

and

\[
(a,b,c,c),\qquad b>c,\quad a\ge2b+2c-2.
\tag{2.6}
\]

The b=c case in (2.6) is already in Pate's explicit class. Formula (2.5) permits both k and r to grow; it is not merely a result for one fixed rectangular tail.

By moving t boxes from the first row of (a+t,rho) into singleton rows, Pate's 1992 theorem also gives

\[
\boxed{
\bar d_{(a,\rho,1^t)}\le\operatorname{per}
\quad\text{if}\quad a+t\ge|\rho|+C(\rho)-1.
}
\tag{2.7}
\]

Here rho has no singleton parts; these are included in t. The exactness of this node-closure predicate is proved in Section 5.

## 3. A two-witness theorem for (a,b,3,3)

### Theorem 3.1

For all integers

\[
a\ge b\ge4,\qquad 5a\ge8b,
\tag{3.1}
\]

ordinary PDC holds for (a,b,3,3). Combined with the accepted b=4 family, this leaves only a bounded-ratio band in this two-parameter family, not an unbounded first-row search for each b.

When a>=2b+4, Theorem 2.1 already applies. In the remaining interval define

\[
D=\Phi_{b,(a,3,3),3},\qquad
E=\Phi_{a,(b,3,3),1},
\]

\[
W=(2b+4-a)D+b(b+1)(3a-4b+4)E.
\tag{3.2}
\]

Both multipliers are nonnegative in the interval, and the second is strictly positive.

For 0<=g<=b-3 and 0<=c<=3, put

\[
\nu_{g,c}=(a+b-g-c,\,g+3,\,3,\,c),
\tag{3.3}
\]

omitting a final zero. Let H_(g,c)(a,b) be its coefficient in W. Then

\[
H_{b-3,3}=-T,\qquad
T=2b(b+1)(b+8)(a-b+2)>0,
\tag{3.4}
\]

\[
H_{b-4,3}=0,
\tag{3.5}
\]

and every other H_(g,c) is nonnegative. Consequently

\[
\boxed{
\bar d_{(a,b,3,3)}
\le\sum_{(g,c)\ne(b-3,3)}
\frac{H_{g,c}(a,b)f^{\nu_{g,c}}}{T f^{(a,b,3,3)}}
\bar d_{\nu_{g,c}}.
}
\tag{3.6}
\]

These are exact convex coefficients. Every term with c<=2 belongs to Pate's at-most-three-large-parts class. Every surviving four-large-part term has the form

\[
(a+t,b-t,3,3),\qquad t\ge2,
\]

and satisfies 5(a+t)>=8(b-t). Induction on b therefore expresses the target as a convex combination entirely of Pate-class immanants. The base b=3 belongs to Pate's class; b=4 can either use the supplied theorem or its applicable part of this same argument.

### 3.1 Support and exact coefficient formulas

A horizontal b-strip on (a,3,3) gives shapes (3.3), initially with potentially larger g. The added contents are the three intervals

\[
a,a+1,\ldots,a+b-g-c-1;
\quad2,3,\ldots,g+1;
\quad-3,-2,\ldots,c-4.
\tag{3.7}
\]

When g>=b-2, the second interval contains every integer from 2 to b-1. Every evaluation point in (1.1), for p=b and k=3, is then a zero of the content polynomial. Thus the coefficient vanishes. This proves the fixed support 0<=g<=b-3. The other witness E has exactly this possible support by Pieri interlacing.

Here is a compact polynomial specification of every coefficient, requiring no character table. For an interval a,a+1,...,a+l-1 define

\[
S_1(a,l)=la+\frac{l(l-1)}2,
\]

\[
S_2(a,l)=la^2+a l(l-1)+\frac{l(l-1)(2l-1)}6,
\]

\[
S_3(a,l)=la^3+\frac{3a^2l(l-1)}2+
\frac{a l(l-1)(2l-1)}2+\frac{l^2(l-1)^2}4.
\tag{3.8}
\]

Let h=b-g-c and

\[
p_j=S_j(a,h)+S_j(2,g)+\sum_{r=0}^{c-1}(-3+r)^j.
\]

Set e_1=p_1, e_2=(p_1^2-p_2)/2, and e_3=(p_1^3-3p_1p_2+2p_3)/6. Let o_1,o_2,o_3 be the corresponding elementary symmetric functions of 0,1,...,b-1, computed by the same formulas. Then the D coefficient is

\[
n_1=e_1-o_1,\quad n_2=e_2-o_2-o_1n_1,
\]

\[
D_{g,c}=e_3-o_3-o_2n_1-(o_1-1)n_2.
\tag{3.9}
\]

This follows by comparing the three leading nontrivial coefficients in the Newton expansion from the accepted Pieri theorem. The E coefficient is

\[
E_{g,c}=\kappa_{\nu_{g,c}}-\kappa_{(b,3,3)}-\binom a2,
\tag{3.10}
\]

and finally

\[
H_{g,c}=(2b+4-a)D_{g,c}+b(b+1)(3a-4b+4)E_{g,c}.
\tag{3.11}
\]

At c=3, putting t=b-3-g, the first two rows simplify to

\[
D_{b-3,3}=-b(b+1)(b+2),\qquad E_{b-3,3}=-(b+6),
\]

\[
D_{b-4,3}=b(b+1)(3a-4b+4),\quad E_{b-4,3}=a-2b-4.
\]

These prove (3.4)–(3.5) identically.

### 3.2 Complete symbolic sign certificate

The general sign assertion for (3.11) is certified as follows. This is a finite exact proof of an infinite parameter region.

For c=0,1,2 set b=g+u+3. For c=3, the target t=0 and canceled row t=1 have already been handled, so set b=g+u+5. In each case g,u are nonnegative integers. Parameterize the real interval by

\[
a=\frac{8b}{5}+\left(\frac{2b}{5}+4\right)x,
\qquad0\le x\le1.
\tag{3.12}
\]

After substitution, H has degree at most four in x. Its exact Bernstein expansion is

\[
H=\sum_{k=0}^{4}\binom4k x^k(1-x)^{4-k}Q_{c,k}(g,u).
\tag{3.13}
\]

If H=sum_i A_i(g,u)x^i, these twenty polynomials are defined exactly by

\[
Q_{c,k}=\sum_{i=0}^k\frac{\binom ki}{\binom4i}A_i.
\tag{3.14}
\]

Their rational monomial coefficients are printed in full in `symbolic_certificate.json`; they are also regenerated from (3.8)–(3.14) by `verify_symbolic.py` using the small exact polynomial ring `polynomials.py`.

For each of the twenty Q polynomials the verifier checks:

* Q(g+10,u+10) has only nonnegative monomial coefficients.
* For every i=0,...,9, both Q(i,u+10) and Q(g+10,i) have only nonnegative monomial coefficients.
* On the remaining 10-by-10 grid, all relevant values are nonnegative, excluding b<4 and b=7.

This covers the entire nonnegative integer quadrant, not merely a finite range of matrix orders. It involves 420 nonnegative translated polynomials and 1,895 rational grid values.

The exception b=7 is not a missing case: integrality and 5a>=8b imply a>=12. Substituting b=7 and a=12+6x, all nineteen off-target H coordinates have nonnegative Bernstein coefficients for x in [0,1]. These coefficients are also given explicitly in the certificate. The case a>=18 is covered by Theorem 2.1. Thus every admissible integer a,b is covered.

Because the Bernstein basis in (3.13) is nonnegative, these exact checks prove the required sign assertions. There is no use of floating-point optimization in this proof. Balance gives the sum-one property in (3.6). The decrease of b for its remaining four-row terms completes the PDC proof. QED.

### 3.3 A useful failed extrapolation

A tempting stronger version replaced 5a>=8b by a>=3b/2+2, with the same two-witness combination. It survived the initial small-parameter tests but is false as a coefficient-sign assertion.

At a=170,b=112,g=101,c=3, the coordinate is nu=(178,104,3,3), and

\[
D_{g,c}=-6350400,\qquad E_{g,c}=418,
\]

\[
(2b+4-a)D_{g,c}+b(b+1)(3a-4b+4)E_{g,c}
=-19169472<0.
\]

This refutes only that stronger two-witness ansatz, not PDC for the target partition. It is why the final theorem uses a complete symbolic sign certificate rather than extrapolation from successful orders.

### 3.4 Size of the new region

At fixed a+b=N, admissible shapes in the family a>=b>=4 number N/2+O(1). The condition 5a>=8b permits b<=5N/13, so it covers 5N/13+O(1) of them. The asymptotic fraction is 10/13. By contrast, the long-first-row criterion alone gives asymptotic fraction 2/3. Thus the two-witness theorem adds asymptotic fraction 4/39 of this whole two-parameter family, or 4/13 of the band left by the long-row criterion. These are densities within this family, not within all partitions.

The b=4 input and a finite number of exact low-order certificates do not change these asymptotic fractions.

## 4. Boundary compression for arbitrary local filters

### Theorem 4.1: only the last k branching steps matter

Fix n=p+q and a swap size k<=min(p,q). Choose the k marked positions at the end of each block. Let tau_k exchange those positions in pairs. Consider the cone of coefficient vectors

\[
t_\nu=\operatorname{Tr}_{S^\nu}
\bigl((a\otimes b)^*\tau_k(a\otimes b)\bigr),
\quad a\in\mathbb C[S_p],\ b\in\mathbb C[S_q],
\tag{4.1}
\]

with arbitrary local filters, and their positive sums.

The same cone is obtained by restricting aa* and bb* to matrices of the following form. In a local irreducible S^alpha,

\[
S^\alpha\downarrow_{S_{p-k}}
=\bigoplus_{\gamma\vdash p-k}S^\gamma\otimes M_{\alpha/\gamma},
\]

and it suffices to use

\[
X_\alpha=\bigoplus_\gamma I_{S^\gamma}\otimes X_{\alpha/\gamma},
\qquad X_{\alpha/\gamma}\succeq0.
\tag{4.2}
\]

There is an analogous expression in the other block. The retained matrix sizes satisfy

\[
\dim M_{\alpha/\gamma}=f^{\alpha/\gamma}\le k!.
\tag{4.3}
\]

At the level of cone generators, one may further restrict to one pair of local irreducibles, one pair of predecessor shapes, and rank-one positive matrices in the two multiplicity spaces.

In particular, at fixed k, arbitrarily deep refinements inside the unmarked parts of the blocks cannot create any new central immanant inequality. All possible coherence that remains relevant is within the final k-box branching multiplicity spaces.

### Proof

By cyclicity, (4.1) equals Tr(tau_k(X tensor Y)), with X=aa*>=0 and Y=bb*>=0 in the finite group C*-algebras. The two variables enter bilinearly.

The swap commutes separately with S_(p-k) and S_(q-k), acting on the unmarked positions. In every global irreducible trace, conjugating X by S_(p-k) therefore leaves the coefficient unchanged. The same is true of Y and S_(q-k). We may replace X,Y by their independent conjugation averages. These averages preserve positivity.

Inside S^alpha, Schur's lemma and the restriction decomposition show that this conditional expectation has precisely the form (4.2). More explicitly, its gamma block is I_(S^gamma)/f^gamma tensor the partial trace of X over S^gamma. The partial trace is positive. The standard branching rule identifies the multiplicity dimension with the number of standard tableaux of the skew diagram alpha/gamma, which has k boxes, hence at most k! tableaux.

Conversely, every positive matrix of the form (4.2) is an element of the appropriate finite group C*-algebra and has a square root there, so it is an admissible aa*. Thus no enlargement has occurred. Decomposing into irreducible blocks, predecessor blocks and rank-one positive matrices gives the final cone-generator assertion by bilinearity. QED.

The dimension bound does not classify all global coefficient vectors. The number and shapes of alpha,beta,gamma,delta, their box contents, and their global couplings still vary with n. The result identifies exactly where deep-path redundancy ends; it does not claim that only finitely many global inequalities suffice.

### Theorem 4.2: complete saturation of the singleton-block architecture

For p=n-1,q=k=1, the cone in (4.1) is exactly generated by

\[
B_{\beta,\gamma}
=\sum_{\nu\succ\beta}
\frac{d_\nu}{c(\nu/\beta)-c(\beta/\gamma)},
\qquad\gamma\prec\beta.
\tag{4.4}
\]

Thus retaining more than the established final two shapes of a Young path, or using arbitrary noncentral linear combinations in the large block, cannot strengthen this particular architecture.

### Proof

Let X=bb* be an arbitrary positive large-block filter square. In a fixed local irreducible S^beta, let Q_(beta,gamma) be the orthogonal projector onto its S_(n-2) type gamma. The boundary-compression theorem and multiplicity-free branching show that the trace depends only on the nonnegative weights

\[
w_{\beta,\gamma}
=\operatorname{Tr}_{S^\beta}(Q_{\beta,\gamma}X_\beta)\ge0.
\]

For completeness, the diagonal compression of s=(n-1,n), on the path gamma<beta<nu, is the scalar

\[
\frac{1}{c(\nu/\beta)-c(\beta/\gamma)}.
\]

This is the established Jucys–Murphy calculation: sJ_n-J_(n-1)s=1, and J_n,J_(n-1) have the two corresponding content eigenvalues. Therefore

\[
\operatorname{Tr}_{S^\nu}(b^*sb)
=\sum_{\beta\prec\nu}\sum_{\gamma\prec\beta}
\frac{w_{\beta,\gamma}}
{c(\nu/\beta)-c(\beta/\gamma)}.
\tag{4.5}
\]

Every arbitrary-filter coefficient vector is a positive combination of (4.4). Conversely, each (4.4), up to the positive factor f^gamma, is realized by the filter e_beta e_gamma. QED.

This is a new saturation/no-improvement statement about an architecture, not a repetition of the old central-projector separator. It also does not prove that the union of all partial-swap architectures fails to establish PDC.

## 5. Exact node-moving closure of the explicit theorem system

We use Pate's operation: remove an outer box from a row of length greater than one and append a singleton row. It weakly decreases the normalized immanant and preserves the total matrix order.

### Lemma 5.1: reachability

Let lambda=mu union (1^t), where every part of mu is at least 2, and |lambda|=|alpha|=n. Then lambda is reachable from alpha by these node moves if and only if mu is a Young subdiagram of alpha.

Necessity is immediate: no row of length at least two can increase or be newly created. Conversely, remove the outer boxes of alpha outside mu, always retaining a partition, and turn each removed box into a singleton. A row outside mu can be reduced to length one. At the end the nonunit part is exactly mu and the remaining mass is n-|mu| singleton boxes. This is precisely lambda. QED.

This does not mean that PDC is monotone under adding arbitrary boxes: reachability holds at fixed total order, and it is the ancestor's PDC that implies the descendant's.

### Lemma 5.2: exact long-row node closure

Write lambda=(a,rho,1^t), with rho having no parts equal to one. The node closure of the long-row theorem contains lambda if and only if

\[
a+t\ge|\rho|+C(\rho)-1,
\tag{5.1}
\]

apart from the already trivial empty-tail/hook cases.

Sufficiency is (2.7). For necessity, suppose lambda is reached from a long-row seed alpha=(A,sigma,1^u), where sigma has nonunit parts. Reachability implies sigma contains rho. Write s=|sigma|-|rho|>=0. Total order gives A=a+t-s-u. The long-row criterion for alpha is

\[
A\ge|\sigma|+u+C(\sigma)-1.
\]

(The singleton tail does not change the maximum removable content when sigma is nonempty.) Thus

\[
a+t\ge|\rho|+2s+2u+C(\sigma)-1.
\]

Removing s boxes from sigma to obtain rho increases maximum removable content by at most s, so C(sigma)>=C(rho)-s. Substitution proves (5.1). QED.

### The explicit coverage set

Let S be the node closure of these seeds:

* Pate's explicit class: at most three parts greater than 2, or exactly four with second and third equal.
* The accepted family (m,4,3,3), m>=4.
* All supplied PDC cases through order 15, and the supplied exact (6,5,3,3) certificate at order 17. The other supplied order-16/17 certificates are already in the first-row family (m,4,3,3).
* Theorem 2.1 and Theorem 3.1.

For n>=18 the complement of S is exactly the following two regimes.

**Four large parts.** Write

\[
\lambda=(a,b,c,d,2^s,1^t),\qquad a\ge b>c\ge d\ge3.
\]

It is outside S if and only if all the following hold:

\[
t<b-c,
\tag{5.2}
\]

\[
a+t<2b+c+d+2s-2,
\tag{5.3}
\]

and it is not a shape with s=0,c=d=3 satisfying either b=4 or 5(a+t)>=8b.

**At least five large parts.** Write lambda=(a,rho,1^t) with rho having no singleton parts and with at least five parts of lambda greater than two. It is outside S if and only if

\[
a+t<|\rho|+C(\rho)-1.
\tag{5.4}
\]

### Proof of the classification

Pate's explicit class already covers all shapes with at most three large parts. For four large parts, a Pate ancestor with its second and third parts equal must add at least b-c boxes to the third row; this can be paid for exactly when t>=b-c. Conversely, that many singleton boxes can be incorporated into the third row to obtain the Pate ancestor (a,b,b,d,2^s,1^(t-b+c)). This proves the exact Pate node-closure test.

Neither node moves nor a Pate seed can create a fifth part greater than two. The (m,4,3,3) seeds and the new four-row family can have a four-large-part descendant only when s=0 and c=d=3. For the new family, allocating all t available singleton boxes to the first row is optimal: an ancestor second row B>=b has first row A=a+b+t-B, and 5A>=8B forces 5(a+t)>=13B-5b>=8b. Conversely, B=b attains this condition. The accepted b=4 family handles that entire slice.

Finally apply Lemma 5.2. In the four-large-part exceptional regime b>c, the largest removable content of rho=(b,c,d,2^s) is b-1, giving (5.3). In the five-or-more regime it gives (5.4). The supplied finite-order seeds cannot affect orders n>=18 because node moves preserve n. This exhausts the specified seed classes. QED.

The coarse distinction “four large parts with an unequal middle pair” versus “at least five large parts” is already present in the literature on Pate's classes, including Divya–Somasundaram (2022). The additions here are the exact closure conditions, the new uniform cuts, and the quantitative limitations below.

### Finite checks of the structural formulas

The files `frontier_counts.json` and `residual_shapes.json` give the exact enumeration for every 16<=n<=30. The verifier independently constructs node-moving reachability as a graph search and checks that it equals the analytic predicates for every partition, not merely for reported residuals. In total 27,945 partitions are checked.

| n | All partitions | Covered before the two new families | Covered after | Residual |
|---:|---:|---:|---:|---:|
|16|231|227|227|4|
|17|297|290|290|7|
|18|385|367|367|18|
|19|490|459|461|29|
|20|627|573|575|52|
|21|792|707|709|83|
|22|1002|869|882|120|
|23|1255|1056|1070|185|
|24|1575|1281|1296|279|
|25|1958|1538|1558|400|
|26|2436|1840|1872|564|
|27|3010|2186|2236|774|
|28|3718|2587|2652|1066|
|29|4565|3040|3124|1441|
|30|5604|3563|3685|1919|

These are exact counts for S, not classifications of full witness-cone feasibility. At order 30, 361 residuals have four large parts and 1,558 have at least five.

## 6. Why this does not yet become a finite global classification

### Theorem 6.1: density zero for the explicit family-and-node program

Let S_n be the covered set just defined, and let p(n) be the number of all partitions. Then

\[
\frac{|S_n|}{p(n)}\longrightarrow0.
\tag{6.1}
\]

More quantitatively,

\[
\frac{|S_n|}{p(n)}
\le\exp\left[-\pi\left(\sqrt{\frac23}-\frac23\right)\sqrt n+O(\log n)\right].
\tag{6.2}
\]

The same conclusion holds if, in addition, PDC is optimistically granted for every shape

\[
(a,k^r,2^s,1^t),\qquad a\ge k\ge3,
\tag{6.3}
\]

and all of their node-moving descendants are adjoined.

### Proof

All supplied fixed-order exceptions disappear asymptotically. All other seeds except the long-row class and (6.3), and all of their node descendants, have at most four parts greater than two. The number of such partitions of n is polynomial in n: their at most four large parts, the multiplicity of 2, and the multiplicity of 1 give a crude O(n^6) bound.

For a node descendant of a long-row seed, write lambda=(a,rho,1^t), q=|rho|, with each part of rho at least two. If ell is the length of rho, its bottom removable box has content at least 2-ell. Thus

\[
C(\rho)\ge2-\ell\ge2-q/2.
\]

The exact node-closure inequality (5.1) forces

\[
n-q=a+t\ge q+C(\rho)-1\ge q/2+1,
\]

so q<=2(n-1)/3. For each q, there are at most p(q) choices of rho and at most n+1 choices of a,t. Consequently

\[
|S_n|\le O(n^6)+(n+1)^2p(\lfloor2n/3\rfloor).
\tag{6.4}
\]

The Hardy–Ramanujan asymptotic p(n)=exp(pi sqrt(2n/3)+O(log n)) proves (6.1)–(6.2).

For the optimistic addition (6.3), the number of parameter choices at order n is polynomial. A node descendant's nonunit subdiagram below its first row and above its rows of length two lies inside a k-by-r rectangle. The number of all subdiagrams of that rectangle is binom(k+r,k). The first row and the number of two-rows contribute only polynomial factors.

Let x=max(k,r)/min(k,r)>=1. The elementary estimate binom(k+r,min(k,r)) <= [e(k+r)/min(k,r)]^min(k,r) gives

\[
\log\binom{k+r}{k}
\le\sqrt{kr}\,\frac{1+\log(1+x)}{\sqrt x}
\le(1+\log2)\sqrt{kr}\le(1+\log2)\sqrt n.
\]

The middle bound follows by differentiation: the displayed function is decreasing for x>=1, since 1+log(1+x)-2x/(1+x)>0 there. Because 1+log2<2pi/3, this contribution is smaller than the exponent already present in (6.4). The same density conclusion follows. QED.

This is a limitation of the stated family-and-node closure, not a Farkas separation from the complete partial-swap cone. In particular, it does not preclude a general identity within the existing broad positivity mechanism that handles the irregular shapes collectively.

### Unbounded structural complexity is concrete

For every r>=5, the staircase-with-short-rows-removed shape

\[
\Sigma_r=(r+2,r+1,\ldots,3),\qquad
|\Sigma_r|=r(r+5)/2,
\tag{6.5}
\]

lies outside the explicit coverage set. It has no singleton row, so it cannot be a nontrivial node descendant at the same order. It is not in a bounded-large-row Pate class, is not a four-row family, and fails the long-row criterion. Its number of distinct row lengths and removable corners is r; both are unbounded. Its Durfee size is also unbounded.

A finite union of templates with a uniformly bounded number of distinct row lengths cannot contain this sequence. Rectangles have one repeated row length and are not representative of this obstruction. This does not prove that a finite number of *general mechanisms* is impossible. It proves that bounding the number of diagram corners by inspection of low orders is not a valid global reduction.

## 7. What the results suggest, and what remains unproved

The current problem can now be divided more usefully than by order.

The first-row-heavy regime is uniformly solved for arbitrary tails, with an exact threshold for the one-witness argument. The repeated short-bottom regime (a,b,3,3) has a uniform two-witness solution over 5a>=8b and an explicit residual bounded-ratio band. Appended singleton rows are handled by exact node-closure conditions, not informal lifting between different orders.

The remaining central difficulty is diagrams with many large rows, no dominant first row even after singleton absorption, and potentially many distinct corners. This regime has asymptotic density one relative to the explicit theorem program. The analysis does not reduce that variable-length tail to finitely many fixed-parameter shape families.

For further local-filter work, Theorem 4.1 gives a precise computational replacement for full Young-path searches. At k=1, everything is scalar corner data; the singleton-block version is already saturated. For k=2, the genuinely unexhausted local information can be represented by positive matrices of order at most two on two-box branching multiplicity spaces. Coherent combinations in these spaces, and coupling the two nontrivial blocks, are structurally different from retaining a longer path in a one-swap singleton-block filter. Whether these coherent boundary filters give a useful uniform theorem for balanced rectangles or irregular staircases remains unproved here.

Induction/Littlewood–Richardson positivity closure is still valid as in the supplied proof, but it propagates mixture-to-mixture inequalities. No individual-descendant PDC lifting rule is assumed. Conjugating a Young diagram likewise does not automatically preserve a normalized-immanant upper bound on the complex PSD cone. Neither operation is inserted into the coverage set without an actual inequality.

## 8. Verification and reproducibility

Run `python verify.py` in this folder. Only the Python standard library is required.

The verifier regenerates the 20 symbolic Bernstein polynomials from the power-sum/Newton formulas, checks their identities and all infinite-region sign certificates, handles the complete b=7 exception, and proves the two special target/cancellation polynomial identities. It then independently compares 4,752 coefficient pairs from 154 parameter instances with the supplied finite-difference formula, checks all normalizations by integer dimensions, and checks 1,596 arbitrary-tail long-row examples and threshold tests. These finite examples are cross-checks; the infinite proofs are the symbolic certificate and Section 2's argument.

It also independently reconstructs the node-moving closure and checks the analytic classification and all 16..30 count records. The failed slope-3/2 ansatz is checked exactly, preventing it from being silently confused with the proved theorem.

The generic representation-theoretic boundary-compression proof and the asymptotic counting proof are mathematical arguments in this note; the program does not claim to formalize them.

## References and provenance

Established working inputs: the two research notes and exact certificate bundles supplied in this conversation, including the general partial-swap/Pieri theorem, the (m,4,3,3) family, and the rectangular order-15 proof.

External results used:

1. T. H. Pate, *Immanant Inequalities and Partition Node Diagrams*, Journal of the London Mathematical Society, s2-46 (1992), 65–80. DOI 10.1112/jlms/s2-46.1.65. The one-node-to-singleton comparison.
2. T. H. Pate, *Tensor inequalities, xi-functions and inequalities involving immanants*, Linear Algebra and its Applications 295 (1999), 31–59. DOI 10.1016/S0024-3795(99)00035-X. The explicit (p,q^w,r,2^s,1^t), 0<=w<=2, PDC classes. The abstract also reports sufficiently-wide rectangular-tail results, whose threshold was not supplied in the accessible material.
3. K. U. Divya and K. Somasundaram, *Permanent dominance conjecture for derived partitions*, Bulletin of the ICA 95 (2022), 84–92. The coarse four-large-row / five-or-more-large-row frontier is already recorded there; no general upward closure under adding boxes is supplied by that statement.
4. A. M. Vershik and A. Yu. Okounkov, *A New Approach to the Representation Theory of the Symmetric Groups. 2*, arXiv:math/0503040. Standard branching, content eigenvalues, and Young-basis facts.
5. G. H. Hardy and S. Ramanujan, *Asymptotic Formulae in Combinatory Analysis*, Proceedings of the London Mathematical Society s2-17 (1918), 75–115. DOI 10.1112/plms/s2-17.1.75. The partition-count asymptotic.

No claim of priority over the full Pate literature is made for the new explicit criterion or its particular consequences. The attachment-defined cone and the entire space of valid immanant inequalities remain different objects.
