# I38 Gaussian propeller stability — independent full-proof audit R2

**Verdict: PASS ORIGINAL WITHOUT REPAIRS**, conditional on the stipulated pinned OpenAI proofs and the explicitly identified primary theorem inputs. The original Theorem P holds with the author's constants and all its quantifiers: one positive constant for every finite number of labels and every ambient dimension at least two, with arbitrary measurable cells, no mass constraint, and empty cells allowed. I found no gap requiring a replacement lemma, changed constant, restricted class, or weaker conclusion. The global constant is implicit, not numerically certified. This is a proof decision only; substantiality, acceptance, and worldwide priority are not certified. The accepted count remains five.

I read the complete [author report](../iterations/i38-inequality-stability-discovery.md), all six operative files of the pinned propeller proof, its complete scalar and determinant elimination including the rational certificates, the HJN geometric proof and numerical-proof interface, the relevant Khot–Naor reduction, and the primary stability comparisons specified below. The original bytes were preserved. Expansions below explain why the original steps work; they are not repairs to a failed original proof.

The operative full brief, original brief, parent objections/checks, candidate, gate reviews, source identities, read passages, HTTP responses, searches and diagnostics are retained in [review sources](../sources/i38_propeller_stability_r2/) and [review experiments](../experiments/i38_propeller_stability_r2/). No author edits, shared-index edits, staging, commits, publication, or additional agents were performed.

## 1. Exact claim and premises

Write (B=3/(2\sqrt{2\pi})). For every finite (d\ge2,k\ge3), let (A=(A_i)_{i=1}^k) be a measurable partition of standard Gaussian space, modulo null sets. Put

\[
z_i=\int_{A_i}x\,d\gamma_d,
\quad F=\sum_i|z_i|^2,
\quad\Delta=B^2-F.
\]

Let (\mathcal P_{d,k}) consist of an origin-centered planar 120-degree three-sector propeller, extended by the orthogonal factor, rotated in (O(d)), relabelled, and padded with empty cells. The asserted distance is

\[
d_P(A)=\inf_{P\in\mathcal P_{d,k}}\frac12\sum_i\gamma_d(A_i\triangle P_i).
\]

The claim is (\Delta\ge c_Pd_P^2), not stability modulo translations or at prescribed unequal masses. Its distance exponent (1/2) is sharp. The claims about total mass outside three labels and their deviations from (1/3) follow from the same disagreement bound and are not additional findings.

The pinned premise is `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, manuscript `The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026` (G). The following operations are actually needed:

- [G main theorem and Gaussian maxima corollary](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026/build/main.tex): the finite all-label inequality, including singular Gaussian covariance and zero padding.
- [Extremizers](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026/build/sections/extremizers.tex): duality, optimal score cells, the merge identity, and Gram-Laplacian rank.
- [Scalars](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026/build/sections/scalars.tex), [geometry](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026/build/sections/geometry.tex), [elimination](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026/build/sections/elimination.tex), and [certificates](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026/build/sections/certificates.tex): the finite negative-pairwise equality exclusion, after checking its endpoint compatibility below.
- [Heilman–Jagannath–Naor, author PDF](https://web.math.princeton.edu/~naor/homepage%20files/PropR3.pdf), Theorem 1.1 and Remark 1.4, with its strict four-cell exclusion: uniqueness in dimension at most three. The author PDF's explicit uniqueness remark is absent from [arXiv v2](https://arxiv.org/abs/1112.2993v2). They are different retained versions; an inequality-only theorem was not silently promoted to uniqueness.

Ehrhard's convex-set translation inequality is used inside G's stipulated scalar operation, with its source hypotheses checked. There is no new invocation of it for infinitely many cells. Khot–Naor's Lemmas 3.3/3.7 and Corollary 3.4 explain the finite reduction and planar equality; the necessary versions are also reproved in G. Neither a uniform Hessian theorem nor any external quantitative stability theorem is a premise of P.

## 2. Countable Gaussian scores and equality

Let (H) be a separable real Hilbert space with isonormal process (X(h)). This correctly avoids the nonexistent infinite-dimensional identity-covariance (H)-valued Gaussian. For (\sum_i|v_i|^2<\infty), Tonelli gives

\[
\mathbb E\sum_iX(v_i)^2=\sum_i|v_i|^2<\infty.
\]

Thus the score sequence is almost surely in (\ell^2), and positive finite maxima increase to an integrable supremum. G applies to each finite span, with a zero vector appended, giving (4.1) by monotone convergence. There is no ambient-dimension constant in this passage.

For any Gaussian event (A), including an event depending on infinitely many coordinates, the functional (h\mapsto\mathbb E[1_AX(h)]) is bounded by (\|1_A\|_2|h|). Riesz representation defines (z(A)\in H); the first-chaos moment map is a contraction from (L^2) to (H). For a countable partition, test any finitely supported array (h_i). Pointwise its assigned score, with zero on untested labels, is at most the positive maximum of the tested scores. G therefore bounds its pairing by (B(\sum|h_i|^2)^{1/2}). Taking the finite-array dual supremum proves

\[
\sum_i|z(A_i)|^2\le B^2.
\]

This proves the required partition inequality on the infinite product directly. It does not assume countable-dimensional compactness of measurable partitions.

For a norm-one equality list, the positive maximum is attained because scores tend to zero. The least-index winner is measurable. Let (A_0) be the all-nonpositive event; pad its vector coordinate by (v_0=0). The assigned-score sum is integrable: its absolute value is bounded pointwise by the score (\ell^2) norm, whose (L^2) norm is one. Consequently

\[
B=\sum_{i\ge0}\langle v_i,z_i\rangle\le\|(z_i)\|_{\ell^2(H)}\le B.
\]

Hilbert-space equality gives (z_i=Bv_i) at every index, including (z_0=0). If (A_0) had positive probability, any fixed nonzero score would be strictly negative almost everywhere on it (its zero level is null), contradicting (\langle z_0,v_j\rangle=0). Duplicated nonzero vectors would give an empty later winner cell, also contradicting (z_i=Bv_i\ne0). Countably many distinct-score tie hyperplanes have null union. All active winner cells have positive probability.

Strong summation is justified without an absolute-summability assertion: the first-chaos moments of indicators of increasing finite unions converge to the moment of 1, because those indicators converge in (L^2). Hence (\sum_i z_i=0) strongly. Merging any two cells is a legitimate countable partition and changes the objective by (2\langle z_i,z_j\rangle). The extended sharp bound forces every off-diagonal product to be nonpositive. This validates all the countable identities used later, including when some products vanish.

## 3. Infinite support cannot be an optimizing limit

Fix any three positive-radius competitors. Square summability supplies other nonzero indices with (t=|z_i|/B\to0), none equal to those three. For the author's coefficients

\[
a_j=-\langle z_i,z_j\rangle/|z_i|^2,
\quad w_j=z_j/B+a_jt e_i,
\quad T=X(e_i),\quad Y_j=X(w_j),
\]

the preceding nonpositive products imply (a_j\ge0). Strong summation, paired with the fixed vector (z_i), gives the convergent nonnegative series (\sum_{j\ne i}a_j=1). Thus each (a_j\le1). This is the precise justification for the probability-simplex coefficient budget; no unjustified interchange of an infinite vector sum is needed.

The residuals are orthogonal to (e_i), so every finite family of (Y_j)'s is jointly independent of (T). Direct multiplication gives

\[
H_{jk}=\langle z_j,z_k\rangle/B^2-a_ja_kt^2,
\qquad h_j=r_j^2-a_j^2t^2.
\]

Off-diagonal residual covariances are nonpositive. On (A_i), (T>0) almost surely and (Y_j\le(1+a_j)tT). The first-chaos definition, not conditional independence of (A_i), gives

\[
\mathbb E1_{A_i}T=Bt,
\qquad \mathbb E1_{A_i}Y_j=\langle z_i,w_j\rangle=0.
\]

For a nonsingular residual pair, after dividing by ((1+a_j)t,(1+a_k)t), its density is bounded by (t^2(1+a_j)(1+a_k)/(2\pi D_{jk})). Dropping the indicator after taking a positive part is valid even though (A_i) depends on every competitor. The integral at (T=s\ge0) is over the bounded triangle (u,v\le s, u+v\ge-s), with value (27s^3/6). Since (\mathbb ET_+^3=2/\sqrt{2\pi}), cancellation of (B=3/(2\sqrt{2\pi})) gives exactly

\[
D_{jk}\le (3/\pi)t(1+a_j)(1+a_k).
\]

If a pair is singular its determinant is zero and the same inequality is automatic. The proof never uses a density for that pair.

For the fixed three competitors set (c=\min r_j^2>0). For (t^2<c), all (h_j\ge c-t^2>0). The normalized (3\times3) covariance matrix is positive semidefinite. Its value on ((1,1,1)) gives (\sum|\rho_{jk}|\le3/2), and (\rho_{jk}\in[-1,0]) implies (\sum\rho_{jk}^2\le3/2). Therefore

\[
\sum D_{jk}^2\ge\tfrac32(c-t^2)^2.
\]

The coefficient upper bound (\sum(1+a_j)^2(1+a_k)^2\le88/9<10) uses only nonnegativity and the sum at most one of these three coefficients. It follows by the expansion in elementary symmetric polynomials displayed in G and in the author diagnostics. The resulting right bound (10(3/\pi)^2t^2\to0) contradicts the positive limiting left bound. This excludes **every** infinite-support equality list obtained by the compactification, not just a finite-simplex approximation with a smallest radius. It also covers zero products and singular residual pairs.

## 4. Finite equality and the strictness audit

The sharp global finite inequality already makes any equality partition a global optimizer. Its score property follows from the nonnegative gap whose integral is zero, exactly as in G. This remains true after any equality-preserving merge. Remove null labels; a positive-measure zero-moment label cannot survive, because it would have to win with zero score on the already-excluded all-nonpositive event.

Merge pairs with zero inner product until all active products are strictly negative. This stops after finitely many steps; merging cannot turn two nonzero orthogonal moments into zero. For the terminal list, the Gram-Laplacian identity proves rank (m-1) and independence of every proper subset. All geometric and translation directions in G are therefore available. Global minimality among all optimizers is unnecessary once these properties have been established; G only used that minimality to obtain the strictly negative products.

Here is the complete endpoint check for changing G's hypothesis (C>B^2) to (C=B^2) in the (m\ge5) branch.

1. **Extremal reduction:** the source uses strict excess to conclude (m\ge5) from the three-dimensional inequality. In the candidate, (m\ge5) is an explicit case split, so this particular contradiction is not reused at equality. The centroids, score cells and rank arguments require only global optimality and strictly negative products.
2. **Halfspace rearrangement:** (\sqrt C>B) gives (r_i<2/3) in the source. Equality only gives (r_i\le2/3), which is precisely the endpoint included in `sc:bounds`, the ten scalar intervals, and (L\le8/9). The quadratic ratios retain non-strict lower bounds with strict numerical margins (>.8843837>.884) and (>.9311326>.929).
3. **Deleting/translating one score:** the lower loss (C(1-\sqrt{1-\alpha r_i^2})), derivative (-1/\alpha), Ehrhard tangent, and upper loss require exact optimality and full rank, not strict excess. In `sc:loss-constraint`, substituting (C=B^2) leaves its displayed lower bound valid. The test probability inequalities are strict on the complete closed upper endpoint (r=2/3). Thus (P_i\ge .415r_i+.15r_i^2) remains valid.
4. **Two-competitor integral:** (\mathbb E1_KT=\sqrt C,t>Bt) becomes equality. The needed conclusion is the displayed non-strict determinant bound. The subsequent two determinant constraints were already stated non-strictly and remain unchanged.
5. **Elimination:** after the scalar bounds and determinant constraints, this file has no further use of strict (C>B^2). It derives (\sqrt c>.23), (t>.066), (r_j\le.42) for (j\ge4), (t\le t_0<.12), and (c>2.6t), from independently strict rational margins. In particular the final gap (1.5(2.6-.12)^2-10(3/\pi)^2>.10667806) stays strict. Hence a negative-pairwise (m\ge5) equality list is impossible.

I independently enclosed the scalar quantiles, normal/cap minima, all ten probability intervals, all small-minimum intervals, both five-cell/more-cell budgets and final endpoint margins using rational arithmetic with Taylor remainders and integer-square-root enclosures. The 66 successful certificates reinforce this endpoint audit; their role is finite constants, not a replacement for the analytic proof.

For (m\le4), the score partition factors through dimension at most three. The precise equality input is HJN's explicit author-version Remark 1.4. I also checked why the proof supports the interface. Its full-rank four-cell reduction yields nondegenerate spherical triangles; geometric identities and stationarity require optimality, not strict objective excess. Weakening the objective threshold in Corollary 3.11 only changes its edge lower bound to non-strict, already included in the closed search restrictions (67). The later exclusion gaps stay strict. Lemma 4.1 excludes two neighborhoods by a value strictly smaller than the propeller's. The remaining finite-cover alternatives exclude geometry, exclude stationarity, or use the strict value certificate (77). Thus the numerical-proof interface excludes an equality tetrahedral maximizer too. This review does **not** claim to have rerun HJN's many-hour computer proof; that established primary input and its exact byte version are explicit.

There is no inference that minimal active cardinality automatically classifies every equality partition. The author's backwards step is necessary and correct: if any zero-product merges occurred, the last merge before a three-cell propeller started with four active cells. Their moments sum to zero, so their score partition factors through a space of dimension at most three, regardless of whether their products were strictly negative. HJN uniqueness then excludes that four-active-cell equality partition. With no earlier merge possible, the original equality list itself is a propeller.

An additional direct check of this backwards step is available. Suppose (a,b) merge to one planar propeller moment (p), with the other two moments (c,d) unchanged. The original score property on the two unchanged cylindrical sectors forces (a,b\in L=\operatorname{span}(p,c,d)): a nonzero perpendicular component would violate a score inequality on a positive-measure set. Choose (p=(r,0)), (c=(-r/2,\sqrt3r/2)), (d=(-r/2,-\sqrt3r/2)). Those same score inequalities on the two closed sectors give, for each (v=a,b), (v_x\ge-r/2) and (v_x+\sqrt3|v_y|\le r). Writing (a=(x,y), b=(r-x,-y)) yields (0\le x\le r), (3y^2\le\min(x^2,(r-x)^2)\le x(r-x)). Orthogonality would require (y^2=x(r-x)), forcing one of (a,b) to be zero. This confirms the degeneracy interface; it is not needed to repair the cited HJN uniqueness premise.

Finally, equality Cauchy–Schwarz gave (z_i=Bv_i). The active vectors in a norm-one equality list therefore form an equilateral centered triple of individual norm (1/\sqrt3), with all other vectors zero. This is the classification needed in the next section.

## 5. Uniform compactness and the positive global gap

Sort finite norm-one lists by decreasing vector norm and pad by zeros. Then (Q_{ii}\le1/i) and (|Q_{ij}|\le1/\sqrt{ij}). Diagonal extraction gives an entrywise positive-semidefinite countable limit (Q), of trace at most one. Its standard Gram realization uses a separable Hilbert space; it introduces no infinite-dimensional Gaussian vector.

For any such sorted list, a union bound on Gaussian upper tails, followed by integration, gives

\[
\mathbb E\sup_{i>M}X(v_i)_+
\le a+\sum_{i>M}\frac{e^{-ia^2/2}}{ia}
\le a+\frac{e^{-(M+1)a^2/2}}{(M+1)a(1-e^{-a^2/2})}.
\]

Every inequality is uniform in list length, dimension and correlations. No independence of the tail variables is used. The stated choice (a=\sqrt{4\log(M+1)/(M+1)}) tends to zero and makes the second term tend to zero. The identical bound holds for the limit Gram matrix. For a fixed finite head, covariance-square-root coupling gives convergence in (L^1) of its positive maximum, including singular covariance. Head convergence and the uniform tail bound prove convergence of full expected maxima.

If the original deficits tend to zero, the limit maximum is (B). The countable inequality bounds it by (B\sqrt{\operatorname{tr}Q}). Thus the trace is exactly one: there is no escaping squared-norm mass in this optimizing limit. Sections 2–4 then identify (Q) as an equilateral triple and zeros, with those three diagonal entries first by sorting.

The apparently tail-dependent quantity (E) has the head formula

\[
E=1-\sum_{i\le3}|v_i-\mu|^2,
\qquad \mu=(v_1+v_2+v_3)/3.
\]

It is therefore continuous in the head Gram entries for normalized finite lists. The two singular values (\alpha,\beta) are continuous functions of the centered (3\times3) head Gram matrix. At every possible equality limit, (E=0,\beta=1/\sqrt2). Equal-norm reorderings do not change this conclusion. A sequence in the union (E\ge E_0\) or (\beta\le1/(2\sqrt2)) with deficit tending to zero is impossible; alternatively extract a subsequence in one of the two closed branches. This proves the author's **single** (\eta>0) in (3.1). It is not finite-(k) compactness with a hidden (k)-dependent constant, and no rate is inferred from compactness.

## 6. Local score stability, including arbitrary correlations

In the local region (E<E_0=(B/1600)^2), (\beta>1/(2\sqrt2)), the centered head has a genuine two-dimensional span (L). A reference norm-one equilateral triple has singular values (1/\sqrt2,1/\sqrt2) and inradius (1/(2\sqrt3)). Applying the head's linear map gives its support function at least (hR), (h=1/(4\sqrt3)), (R=|g_L|). This verifies (6.1). Rank-zero and rank-one heads lie in the global-gap branch instead.

For every extra vector and for the additional zero competitor, the (L)-projection after subtracting (\mu) has norm at most (\tau+|\mu|\le2\sqrt E\le h/2). Define

\[
Z=\Big(\sum_{j>3}X(v_j^\perp)^2\Big)^{1/2}+|X(\mu^\perp)|.
\]

The joint orthogonal Gaussian variables can be arbitrarily correlated with each other. They are independent of the entire planar Gaussian projection, hence of (R). Pointwise, each extra score minus the head maximum is bounded above by (Z-(h/2)R); taking the positive part proves (6.2), even when the uncentered three-score maximum is negative. The zero competitor is specifically included and paid by the common-mean term. This is a frequent possible error, but not one in the report.

For any centered finite Gaussian vector (G) with covariance trace (q^2),

\[
\mathbb E|G|^4=(\operatorname{tr}\Sigma)^2+2\operatorname{tr}\Sigma^2\le3q^4,
\quad \mathbb E|G|^3\le3^{3/4}q^3.
\]

Using (q\le\tau), (\mathbb E|X(\mu^\perp)|^3\le2\sqrt{2/\pi}|\mu|^3), and ((a+b)^3\le4(a^3+b^3)), both coefficients are less than 12. Further, (\tau^3+|\mu|^3\le(\tau^2+|\mu|^2)^{3/2}\le E^{3/2}). This proves the claimed (\mathbb EZ^3\le12E^{3/2}) without a rank or label factor.

The planar radial density is (re^{-r^2/2}). Conditional on (Z=z), independence gives

\[
\mathbb E_R(z-cR)_+\le z^3/(6c^2),
\quad c=h/2,
\quad 1/(6c^2)=32.
\]

Subtracting the common mean costs no expectation. Hence the activation is at most (384E^{3/2}\le400E^{3/2}), exactly (6.4). In particular arbitrarily many highly correlated tiny labels and a coherent common shift cannot generate an unpaid order-(E) gain.

I independently checked the triangle branch. The support-function perimeter formula gives (M_3(u)=\sum\ell_i/(2\sqrt{2\pi})). With (S^2=\alpha^2+\beta^2=1-E), (\sum\ell_i^2=3S^2), and (\ell_i\le\sqrt2S), the squared-edge identity is

\[
\sum_{i<j}(\ell_i^2-\ell_j^2)^2=\tfrac92(\alpha^2-\beta^2)^2.
\]

Divide first by ((\ell_i+\ell_j)^2\le8S^2), and then by (3S+\sum\ell_i\le6S). This gives the constant (3/(32S^3)) before multiplication by (1/(2\sqrt{2\pi})). Using ((\alpha+\beta)^2\ge S^2), (S\le1), yields (6.7). Together with (1-\sqrt{1-E}\ge E/2) and (400\sqrt E\le B/4), it proves

\[
e(v)\ge(B/4)E+\frac3{64\sqrt{2\pi}}(\alpha-\beta)^2.
\]

Polar alignment in the same ambient space, using the first three labels, has exact distance

\[
\|v-t\|^2=2-\sqrt2(\alpha+\beta).
\]

The head's common mean and the remaining labels have already been included in its normalization. Put (q=(\alpha-\beta)^2/S^2\in[0,1]); then (\sqrt2(\alpha+\beta)=2S\sqrt{1-q/2}). The inequalities (1-S\le E), (1-\sqrt{1-x}\le x), and local (S\ge1/2) prove (6.9). Thus (c_0=3/(128\sqrt{2\pi})) works. Outside the local region, the squared distance between unit arrays is at most 4, so (c_V=\min(c_0,\eta/4)>0) gives the full all-list estimate. All constants retain dimension and cell-count independence.

## 7. Partition calibration and sharp exponent

For (F>0), let (v=z/\sqrt F). The assigned-score comparison yields (M(v)\ge\sqrt F), so (e(v)\le B-\sqrt F). For finite (d,k), a closest propeller array (t\in\mathcal T) exists: there are finitely many triples of labels and a compact space of planar orthonormal frames. No extra label needs to be introduced to attain this distance. Since both arrays have norm one,

\[
J=B-\langle t,z\rangle
=B-\sqrt F+\frac{\sqrt F}{2}\|v-t\|^2
\le\left(B^{-1}+(2c_V)^{-1}\right)\Delta.
\]

The equality in the middle is exact. Its squared distance prevents a second square-root loss.

The propeller has three active score differences of variance one. If its winner-to-other-label margin is at most (s), either a pair of active scores lies in an absolute slab of width (s), or an inactive zero label is within (s) of the maximum. The three slabs have total probability at most (3\sqrt{2/\pi}s). The second event requires (R\le2\sqrt3s), of probability at most (6s^2). All inactive labels have the same score zero, so this bound has no (k) factor. Ties of active winners are null. When (k=3) the extra term is harmless.

For mismatch probability (\epsilon), the assigned-score loss is at least the margin on every mismatch. Taking (s=\epsilon/18\le1) gives (J\ge\epsilon^2/36\ge d_P(A)^2/36). Thus the author's

\[
c_P=\left[36\left(B^{-1}+(2c_V)^{-1}\right)\right]^{-1}
\]

is valid. When (F=0), (\Delta=B^2), (d_P\le1), and (c_P\le B/36<B^2), covering the normalization exception. Empty cells, positive-measure zero-moment cells of a nonoptimal partition, highly fragmented cells and arbitrary small masses need no further regularity or endpoint hypotheses.

For the three planar openings (2\pi/3+t,2\pi/3-t,2\pi/3), the sector moment formula gives (\Delta=(1-\cos t)/(4\pi)). Every aligned propeller assigns mass (1/3) to the oversized cell's label, so disagreement is at least its excess (t/(2\pi)), for every rotation or relabelling. The displayed unrotated alignment attains that bound. Therefore (d_P=t/(2\pi)) exactly and (\Delta/d_P^2\to\pi/2). This proves the claimed sharp exponent, not optimality of the tiny universal constant above.

## 8. Primary comparisons and the two secondary screens

The explicit predecessor is [Heilman 2014, Lemma 2.8](https://www.stevenheilman.org/~heilman/papers/SSC.pdf). I read its whole proof with Lemmas 2.5–2.7 and its closing scope discussion. For three cells, its metric satisfies (d_2^2=2d_P), and its (d_2\le6\epsilon^{1/8}) yields (d_P\le18\Delta^{1/4}) by letting (\epsilon\downarrow\Delta) when (\Delta<1/100); larger deficits are covered trivially by (d_P\le1). Its proof uses a three-pair misassignment argument and triangle stationarity. It is genuine direct quantitative prior art, but neither its stated conclusion nor that finite-three proof establishes the changing-support compactification used here.

[Heilman 2306.03312v3](https://arxiv.org/abs/2306.03312v3), Theorem 1.5, Lemmas 3.3/4.1, circular rearrangement Lemma 6.1 and equations (53)/(65) were inspected at the actual proof level. They retain angular/radial three-cell penalties; positive-correlation optimality requires equal masses, while the negative-correlation branch does not. The displayed stability penalties are planar after the relevant reduction, not a theorem controlling every arbitrary-dimensional partition by a rotation distance at changing label count. The report correctly credits these operations and does not use their numerical coefficients as a premise. A new significance reviewer should still assess operation-level reduction, rather than equating this proof PASS with novelty.

No exact all-(k,d) theorem duplicate was identified in this bounded proof-oriented search. Searches also returned single-set Borell stability, Gaussian surface-area stability, and unrelated engineering papers. Their titles/snippets are not evidence for or against P. This audit is not an exhaustive literature survey and assigns no substantiality verdict.

The Mahler screen is correctly rejected as a technical deduction under the pinned equality classification. Kim's [arXiv:1212.2544v1 Main theorem](https://arxiv.org/abs/1212.2544v1) is explicitly a linear remainder in distance to the entire Hanner class, not merely strict local minimality; its final proof retains the linear term against quadratic errors. John's normalization provides a compact fixed-dimensional class and removes eccentricity. Away from the local Hanner neighborhood, the pinned equality classification yields a positive deficit; bounded Banach–Mazur distance globalizes the estimate. Nothing in this reasoning gives a dimension-uniform constant or transfers functional equality through an auxiliary-dimension limit. I checked the actual pinned introduction and Kim's statement/final proof; a full re-audit of Kim's proof was unnecessary and is not claimed.

The scalar Lieb–Thirring splitting counterexample also passes. The pinned equality introduction and the complete explicit profile/factorization section give the one-bound-state (w_a), its sole eigenvalue (-a^2), and (\int w_a^p=a^{2\gamma}/C_\gamma). Two translated truncated ground states with growing disjoint supports supply two Rayleigh quotients (-a^2+o(1)). Positivity of the other well cannot harm the upper Rayleigh bound. The pinned global inequality sandwiches the spectral moment; (t_L^2W_L(t_Lx)) preserves its ratio to the (L^p) integral and makes that integral exactly one. For any candidate center (b), one of the two well centers is at least (L/t_L) from (b); its fixed-radius interval therefore sees vanishing (L^p) mass from the normalized equality profile of fixed scale. Reverse triangle inequality followed by (R\to\infty) proves the displayed (2^{-1/p}) lower distance bound, uniformly over (b). This is an actual obstruction already at (m=1), not failure of an auxiliary estimate.

[Frank–Gontier–Lewin v2, Theorem 1](https://arxiv.org/abs/2109.05984v2) is the appropriate bubble framework. Its stronger translation-compactness parameter range is above (3/2) in dimension one, and does not contradict this screen. The source's matrix auxiliary remainder and fixed-physical-rank tail inequality have also been checked at their actual interfaces. These secondary conclusions do not enter P's dependency graph and are not separate substantial nominations.

## 9. Adversarial checks, evidence and reproduction

The new analytic checks above specifically address infinite-product measurability, integral exchange, null/duplicate score cells, strong centroid summation, singular residual pairs, arbitrary tail correlation, sorted-norm ties, rank collapse, the common mean, the artificial zero competitor, all inactive labels, zero total moment and optimal sector alignment.

Independent exact diagnostics verify 66 rational-interval margins from the endpoint proof. They also test 2,070 rational positive-semidefinite three-correlation matrices, including 13 singular cases, and 1,771 points of the nonnegative coefficient simplex. Enumeration is a check of delicate algebra, not the proof of either universal inequality.

The independent activation stress tests include a single orthogonal extra score, 256 perfectly correlated scores, 256 oppositely signed correlated scores, and a pure common-mean shift with no extra label. They test multiple energy allocations down to (10^{-12}). The rank-one perpendicular model has the independent exact reduction

\[
\mathbb E(aZ-cR)_+=\frac{a-c\arctan(a/c)}{\sqrt{2\pi}},
\]

for standard (Z\in\mathbb R), independent planar Gaussian radius (R), and (a,c>0). It follows by spherical coordinates in three dimensions. This exhibits the cubic small-(a) term directly, including the zero-competitor/common-mean case. The remaining angular integral was evaluated in 30 **NONCERTIFIED** floating quadrature rows; the largest observed activation divided by (E^{3/2}) was below 0.66, far below 400. Another 7,560 **NONCERTIFIED** pointwise cases target planar radii of order (\sqrt E), including nonzero planar projections, common means, perfect correlations and zero radius. None substitutes for the universal analytic estimate.

Both original reproduction commands passed through the review wrapper, with the original verifier's sole output write intercepted. It reproduces 91 sealed artifacts, 26 primary responses (including retained 404/403 payloads excluded from proof), 18 exact author diagnostics and 16 noncertified author quadrature rows. All 93 monitored author files remained byte-identical. The full 9,340-file corpus, 141,349,121 bytes, was actually read and checked against the complete 13,223-entry/749-manuscript tree. The author's full search reconstruction is reproduced, and this review's additional full-corpus search is separately retained. Mechanical search coverage is not semantic reading of all manuscripts.

Seven fresh primary HTTP responses succeeded and are byte-identical to the corresponding author responses. These comprise HJN's author PDF, current record and v2 PDF; Khot–Naor's author PDF; Heilman's 2014 author PDF; and the current record and v3 PDF for 2306.03312. Complete requests, headers, response bytes, versions and hashes are retained. HJN author pages 3/28, Heilman 2014 page 10, and Heilman v3 page 5 were separately rendered and visually inspected. HJN's established computer computation was not rerun or claimed as a new certificate. The earlier failed primary payloads remain bound by the unchanged author evidence and are not imported as theorem inputs.

The seal binds this review, scripts, frozen briefs/objections, exact diagnostic record, source contracts, actual read-passage hashes, fresh primary responses, search records and evidence manifests. The verifier checks it without resealing or fetching replacements. Frozen shared-ledger snapshots are immutable review artifacts; later changes to live `TEN-FINDINGS.md` or the iteration README are reported as mutable drift, separately from proof-dependency drift. The original author verifier already observes the expected parent-integration ledger drift. No source drift was found.

From `/home/mj-kang/Documents/Dev/math/openai-proof-research` run:

```sh
python -B frontier/experiments/i38_propeller_stability_r2/diagnostics.py
python -B frontier/experiments/i38_propeller_stability_r2/reproduce_author.py
python -B frontier/experiments/i38_propeller_stability_r2/verify.py
```

The final command combines seal/dependency verification, complete corpus checks and searches, exact/stress diagnostic reproduction, and unchanged author execution with captured writes. Generated output remains in this review's experiment directory. Evidence-integrity PASS is distinct from the mathematical judgment made in Sections 2–7.

**Disposition for integration: original Theorem P PASS without repairs; no sixth acceptance, no significance certification, and no author changes.**
