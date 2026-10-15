# D1 research outcome: unresolved at the original scope

Date: 2026-10-14. This is discovery work, not an independent proof or contribution gate. No new result is proposed for acceptance or counting.

The target is unchanged: for **every** word ε∈{−1,+1}⁵,

\[
\liminf_{X\to\infty} X^{-1}\#\{n\le X:(\lambda(n+1),\ldots,\lambda(n+5))=\varepsilon\}>0.
\tag{D1}
\]

I did not prove or refute D1. In particular, I did not obtain an unrestricted exclusion of all zero-probability faces of the three-parameter law. The useful outcome is an explicit, fully checked Sawin-type infinite model on one remaining face, including **all fixed nonproportional affine pairs**, together with an exact statement of the missing arithmetic bridge. This model is supporting evidence about the listed limiting axioms; it is neither an arithmetic counterexample nor a substitute target.

## Inputs and their scope

Theorems in OpenAI math at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted true as instructed. Source007 `thm:q-affine` says that for fixed positive integer a₁,a₂ and nonnegative integer b₁,b₂ with a₁b₂−a₂b₁≠0,

\[
\sum_{n\le X}\lambda(a_1n+b_1)\lambda(a_2n+b_2)
 =O_{a_1,a_2,b_1,b_2}(X/\log^cX),\qquad X\ge3,
\tag{1}
\]

with an absolute c>0. The constants may depend on all four coefficients. No uniformity for coefficients growing with X is stated. Fixed negative intercepts are harmless after removing a fixed initial interval. Replacing n by qn+r supplies every fixed residue restriction as well. The full theorem statement and its retained affine transfer proof were read; no upstream truth audit was performed.

For logarithmic windows with X→∞ and 2≤ω≤X, ω→∞, the published odd-correlation and reflection inputs supply the standard five-letter expansion below. The unequal-slope version is legitimate: [Tao–Teräväinen, *The structure of logarithmically averaged correlations…*, Appendix A, Theorem A.1(ii),(iii)](https://arxiv.org/html/1708.02610v2#A1.ThmtheoremA.1) covers fixed affine slopes. For an odd number of Liouville factors the multiplicative product is λ, which does not weakly pretend to a Dirichlet character; the odd affine moment is zero. The even-product case supplies reflection and periodic/isotypic structure in the intercept-dilation parameter. All coefficients are fixed before the limit. This does **not** say four-point correlations vanish.

[Tao–Teräväinen, *Value patterns…*, Theorem 1.14 and complete Section 7](https://arxiv.org/html/1904.05096v2) give ≥24 words of positive upper density and twelve specified words of positive lower density. Their footnote 14 explicitly distinguishes the quantifiers. Their equation (7.4) is the starting law here, not a new result.

## Exact remaining face-exclusion problem

Use a subsequential logarithmic-window limit, writing X_j for the five consecutive signs and

\[
a=\mathbb E X_1X_2X_3X_4=\mathbb E X_2X_3X_4X_5,
\quad b=\mathbb E X_1X_2X_3X_5=\mathbb E X_1X_3X_4X_5,
\quad c=\mathbb E X_1X_2X_4X_5.
\]

Odd moments, all pairs, stationarity and reflection give exactly

\[
32p_\varepsilon=1+P\big((\varepsilon_1+\varepsilon_5)a+
 (\varepsilon_2+\varepsilon_4)b+\varepsilon_3c\big),
\qquad P=\prod_{i=1}^5\varepsilon_i.
\tag{2}
\]

There are only nine distinct coefficient triples of (a,b,c):

\[
(0,0,1),\quad(\pm2,\pm2,1),\quad(\pm2,0,-1),\quad(0,\pm2,-1).
\]

Indeed, if both endpoint pairs agree, P=ε₃; if precisely one pair disagrees, P=−ε₃; if both disagree, the a,b coefficients vanish and Pε₃=1. Thus the exact minimum among the 32 probabilities is

\[
\min_\varepsilon 32p_\varepsilon
 =\min\{1+c-2|a|-2|b|,\ 1-c-2|a|,\ 1-c-2|b|\}.
\tag{3}
\]

The additional coefficient (0,0,1) is redundant for this minimum. Equivalently, positivity requires strictness at all eight affine face inequalities: four from 1+c±2a±2b≥0 and two each from 1−c±2a≥0 and 1−c±2b≥0.

**Unpaid arithmetic statement:** every *genuinely Liouville-attainable*, arbitrarily slowly growing logarithmic-window cluster law has all three expressions in (3) strictly positive. Uniformity need not be postulated separately if this is proved for every such cluster law: compactness then supplies a common positive margin, as explained below. It is not enough to prove |a|<1/2, to exclude (a,b,c)=(1/2,0,0), or to select 24 or 28 words depending on the limit.

## Infinite boundary model with full affine pair cancellation

This is a rational-coordinate realization of the degree-one construction of [Sawin, Theorem 3.1 and Remark 3.5](https://arxiv.org/html/1809.03280v1). The specialization and exact five-word calculation are supporting checks, credited to that construction rather than claimed as new mathematical substance.

Let 𝕋₂=ℝ/2ℤ, let C=Hom(ℚ,𝕋₂), where ℚ is discrete, and give C its compact Haar probability. Since ℚ is countable, C is compact metrizable. For every nonzero rational r, evaluation χ↦χ(r) is a surjective continuous homomorphism and pushes Haar to Haar on 𝕋₂. Surjectivity also follows directly by restricting real linear maps t↦ut modulo 2.

Take independent Haar coordinates

\[
\mathcal X=C\times\mathbb T_2\times\widehat{\mathbb Z},\qquad x=(\chi,\beta,z).
\]

Let s(t)=(−1)^⌊t⌋ on 𝕋₂, choosing boundary values arbitrarily, and put F(x)=s(β), M(x)=z. Set e_d=(1−λ(d))/2∈{0,1}. In particular (−1)^e_d=λ(d), and e_decomposition is additive modulo 2: e_m+e_n≡e_mn. Define

\[
T(\chi,\beta,z)=(\chi,\beta+\chi(1),z+1),
\]
\[
I_d(\chi,\beta,z)=(\chi\circ[d],\beta+e_d,z/d)
\quad\text{on }z\in d\widehat{\mathbb Z},
\tag{4}
\]

where [d](r)=dr. Every map is measurable. The excluded phase boundaries form null sets; only countably many rational forms and integer transformations are used.

These maps meet Sawin Definition 1.1, with λ the actual Liouville function appearing only as the prescribed multiplicative signs in (4):

* M(Tx)=M(x)+1 and dM(I_dx)=M(x).
* T I_d=I_d Tᵈ, since (χ∘[d])(1)=dχ(1).
* I_m I_n=I_mn on its domain, by e_m+e_n≡e_mn modulo 2.
* F(I_dx)=λ(d)F(x).
* T preserves product Haar. The map χ↦χ∘[d] is a Haar-preserving automorphism, because multiplication by d is an automorphism of ℚ. Division z↦z/d pushes Haar restricted to dℤ̂, of total mass 1/d, to (1/d) times Haar. The β translation preserves Haar. Thus (I_d)_*(μ|_{M∈dℤ̂})=μ/d exactly.

The rational coordinate also permits simultaneous multiplication maps, without an unproved extension step:

\[
D_a(\chi,\beta,z)=(\chi\circ[1/a],\beta+e_a,az).
\]

They satisfy I_aD_a=id, D_aI_a=id on M∈aℤ̂, D_aTᵇ=T^{ab}D_a, and D_aD_c=D_ac. With A_{a,b}=TᵇD_a, this gives the affine semigroup law

\[
A_{a,b}A_{c,d}=A_{ac,ad+b},\quad M(A_{a,b}x)=aM(x)+b,
\quad F(A_{a,b}x)=\lambda(a)s(\beta+\chi(b/a)).
\tag{5}
\]

It follows in particular that F(A_{da,db}x)=λ(d)F(A_{a,b}x), the exact content identity for arbitrary d. Moreover (A_{a,b})_*μ is normalized Haar on the event M≡b mod a, with the first two coordinates still independent Haar. Thus finite residue decompositions and division domains are compatible with the construction.

For two forms with nonzero determinant, r=b/a and t=d/c differ. Conditional on χ, U=β+χ(t) is uniform, independent of χ. The difference V=χ(r−t) is also uniform. Hence U and V are independent Haar, and U,U+V are independent Haar. Formula (5) gives

\[
\mathbb E F(A_{a,b}x)F(A_{c,d}x)=0\qquad(ad-bc\ne0).
\tag{6}
\]

This holds conditional on **every** fixed residue of z, by independence of z. This is cancellation for all cross-slope affine pairs, not merely lag covariance.

The transformation β↦β+1 flips every affine observable, so every odd affine moment vanishes, also conditional on fixed z residues. The map χ↦−χ preserves Haar and reverses all intercepts. Replacing χ by χ∘[d] for d≥1 shows that any fixed affine correlation is unchanged when all its intercepts are multiplied by d. Its nonzero-dilation correlation function is therefore constant, compatible with the even isotopy/periodic-approximation input. There is no assertion about a zero dilation, which is not an index in that input. Stationarity follows either from T preserving μ or directly from (5).

For every fixed h≠0, E F(x)F(Tʰx)=0 even conditional on z residues. Consequently the model has Sawin's 1-Fourier uniformity, including congruence conditions on h and M: averaging h=1,…,H in any fixed congruence progression still has zero integrand. No ergodicity follows; χ is a nonconstant T-invariant coordinate.

The consecutive process has the simple law

\[
(F(T^jx))_{j\in\mathbb Z}=(s(\beta+j\alpha))_{j\in\mathbb Z},
\qquad \alpha=\chi(1),
\]

where α,β are independent uniform variables in [0,2). Its four moments in (2) are

\[
(a,b,c)=(1/3,0,1/3).
\tag{7}
\]

It has 28 positive five-word probabilities, and misses exactly

\[
---+-,\qquad -+---,\qquad +-+++,\qquad +++-+.
\tag{8}
\]

The remaining probabilities are 1/16 for four words, 1/24 for twelve, and 1/48 for twelve. All sixteen length-four words have positive probability (minimum 1/24). Substitution into (3) gives 2/3,0,2/3: the middle face is saturated although |a|=1/3<1/2. This shows why merely making the old adjacent-four bound strict does not finish D1.

Here is a finite exact integration proof of (7)–(8), independent of any Monte Carlo. In the (α,β) square, partition by the lines β+jα=k for j=0,…,4 and integer k. Critical α values are k/d, 1≤d≤4, 0≤k≤2d. Between consecutive critical values l,r, all line intersections with a vertical slice are in fixed order, every word is constant on each open cell, and each cell width is affine in α. Its exact probability is therefore (r−l) times its width at α=(l+r)/2 divided by 4. The rational computation in `exact_checks.py` implements precisely this formula, listing all critical stripes and probabilities in `exact-results.json`. Alternatively inserting (7) into (2) reproduces the entire 32-word law. Null boundaries contribute no mass.

**Boundary of this evidence.** There is no completely multiplicative integer sequence constructed here whose finite-cutoff averages obey (1); in particular this is not a counterexample to D1 for λ. The model captures the listed limiting identities, including every affine pair, every odd affine moment, full division maps, residue compatibility and reflection. It does not encode the quantitative rates of actual finite-cutoff Liouville averages, nor every additional known analytic property of actual Liouville systems. I have not proved that no quantitative argument using (1) can rule out this model as an attainable limit. A proof that only passes (1) to fixed-form limiting moments and then uses the listed axioms, however, still admits (7).

## Quantifiers: the full bridge really gives lower natural density

Let B be one of the 32 pattern sets and A(X)=#(B∩[1,X]). Write

\[
W_B(X,\omega)=\frac1{\log\omega}\sum_{X/\omega\le n\le X}\frac{1_B(n)}n.
\]

Replacing log ω by the actual harmonic mass changes this by o(1) whenever ω→∞, uniformly in 2≤ω≤X. The following elementary equivalence pays the required quantifiers, but does not establish the missing face exclusion:

\[
\liminf A(X)/X>0
\quad\Longleftrightarrow\quad
\text{all growing-window cluster probabilities of B are positive}.
\tag{9}
\]

For the forward direction, if A(t)≥d't−C for all t≥1 and d'>0, partial summation gives W_B(X,ω)≥d'−O_C(1/log ω), uniformly in the window. The boundary term is bounded below by −1 and the integral of C/t² is bounded, which proves the claim even when X/ω stays bounded.

Conversely, if liminf A(X)/X=0, take X_l→∞ with δ_l=A(X_l)/X_l→0. When δ_l>0 choose ω_l=min(δ_l^{-1/2},X_l^{1/2}); if δ_l=0 use ω_l=X_l^{1/2}. Then ω_l→∞ and X_l/ω_l≥√X_l. Every term in the window has weight at most ω_l/X_l, so

\[
0\le W_B(X_l,\omega_l)\le\frac{\delta_l\omega_l}{\log\omega_l}
\le\frac{\sqrt{\delta_l}}{\log\omega_l}\longrightarrow0,
\]

with the zero case immediate. Thus a zero cluster probability exists. This proves (9), including the arbitrary slow-growth requirement, rather than a positive-upper-density implication.

For a compact formulation, consider empirical **harmonically normalized** window laws on the countable collection of affine signs together with z∈ℤ̂. Their ambient probability-measure space is compact metrizable. Let K be the intersection over integers M of the closures of the laws with X≥M and M≤ω≤X. A diagonal choice realizes every element of K by X_l,ω_l→∞. Pattern cylinders have continuous probabilities. Consequently, if each of the three expressions in (3) is positive at **every genuine element of K**, its minimum over this compact set is positive. By (9) this proves all of D1. The broad class of models satisfying the listed axioms is larger than K; the solenoid construction is not proved to belong to K. Confusing those two sets would be an invalid refutation of D1.

For clarity, (1) does give genuinely uniform pair control on windows for fixed coefficients. Set c'=min(c,1/2). After extending the bound over a fixed small initial range, summation by parts yields

\[
\sup_{2\le\omega\le X}
\left|\frac1{\log\omega}\sum_{X/\omega\le n\le X}
\frac{\lambda(a_1n+b_1)\lambda(a_2n+b_2)}n\right|
=O_{\rm forms}((\log X)^{-c'}).
\tag{10}
\]

To verify: if u=X/ω≥√X, use |S(t)|/t≪forms(log X)^{-c'} throughout [u,X] in the endpoint terms and the partial-summation integral. If u<√X then log ω≥(log X)/2; the full integral ∫₃ˣdt/(t(log t)^{c'}) is O((log X)^{1−c'}), and both endpoints and the fixed initial range are smaller after division by log ω. This also handles integer endpoint changes. The ordinary rate has not been discarded or weakened to same-slope covariance. For any fixed finite collection of forms the constants can be maximized; a diagonal choice allows sufficiently slowly growing complexity. Neither fact is the missing higher-order face-exclusion argument.

## Failed routes and novelty assessment

1. **Adjacent-four strictness alone:** (7) is a counterexample inside the stated axiom class. The old (1/2,0,0) 24-word model and the elementary adjacent-gapped parity-product bound remain credited technical observations, not new results.
2. **Dilation or odd affine moments alone:** all positive integer multiplication/division maps, all affine odd moments, exact content identities and nonproportional affine pair cancellation coexist in (4)–(8). A propagation argument needs an additional actual-arithmetic input.
3. **Saturation propagation:** setting a probability to zero gives a forbidden cylinder event, not an almost-sure deterministic four-product relation. The face 1−c−2a=0 admits (7), so a derivation of such a deterministic relation from that face and just the listed inputs is false.
4. **Ergodicity:** not supplied by pair cancellation. This model has white lag spectrum but a nontrivial invariant χ. Assuming ergodicity of a genuine Liouville system is unpaid.
5. **Entropy and local Fourier/Gowers uniformity:** the primary short-interval results read have scale restrictions. They cannot be applied at an arbitrary slowly growing window/mesoscopic scale by changing the order of limits. A separate quantitative rigidity argument might exploit them; none is proved here. Excluding this particular polynomial-complexity model would still leave every other point on every face to handle.
6. **Numerical LP:** `affine_lp.py --A 3 --K 4` checks a finite 17-variable affine grid with content identifications, all cross-slope pairs, sign symmetry, joint stationarity and reflection. Six of ten sign/reversal word orbits remain floating feasible; four are reported infeasible, corresponding to the already specified twelve words of TT2019. There are no exact feasibility or infeasibility certificates and no positivity theorem inferred. This is a relaxation, with neither an infinite extension nor all division/residue constraints. The analytic infinite model above supplies only its separately proved face, not certificates for the other five feasible cases.

The bounded primary-literature comparison and actual read extents are in `reading-and-failures.md`. The degree-one model mechanism is already Sawin's; the finite exact law and rational-coordinate presentation do not warrant a substantiality claim. The compactness/window bridge is a standard quantifier reduction. No new full-scope D1 theorem, disproof, or countable minor substitute is claimed. The outstanding research requirement remains the strict positivity in (3) for the entire genuine attainable set K, proved using additional actual Liouville information with the stated growing-window quantifiers.
