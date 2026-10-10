# Independent audit of i02-crossfield, round 2

**Verdict (2026-10-08): the specified mathematical deductions pass, with the scope and citation qualifications below. No substantial new theorem is certified.** Proposition R is correct for nonzero rank-one perturbations. Equations (7.1)–(7.4) are correct necessary conditions. They do not solve the proposed rank-two problem. The exact transversal threshold computation is already explicitly in the cited Shangguan paper, not just suggested by its example.

This review accepts the pinned OpenAI theorems at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` as premises. It does not audit their proofs. I read AGENTS.md, sources/upstream.json, frontier/iterations/README.md, the original report, the actual theorem sources, the full dyadic weights and intertwiner definitions, and Tcaciuc 1805.03277v2. Retrieved source records and tree-verified hashes are in [the audit manifest](../sources/i02_operator_r2/audit_upstream_manifest.json) and [the operator manifest](../sources/i02_operator_r2/upstream_manifest.json). This is an independent review of the preceding researcher's arguments; no further agents were spawned.

## 1. Proposition R: verified

Assume `||Q^n|| <= A exp(-c n²)` for all n≥0, A≥1, c>0, on an infinite-dimensional complex Hilbert space. Take nonzero u and nonzero bounded complex-linear φ. The spectral-radius formula gives σ(Q)={0}. The norm-convergent series

`g(z)=sum[n≥0] φ(Q^n u) z^(n+1)`

is entire. Completing the square in `-cn²+n log R` proves

`M_g(R) <= C R exp((log R)²/(4c))` for R≥2.

The constant in the shifted Gaussian sum is independent of the center: divide into intervals at successive distances from that center and bound the resulting convergent Gaussian series. Thus this is a uniform global bound, not a fibrewise estimate.

If `g=0`, the closed cyclic subspace of u is nonzero and is contained in the proper closed kernel of φ. It is invariant under Q and Q+uφ. Otherwise g takes the value 1. Indeed, if `1-g=exp b` with entire b and b(0)=0, its real part has disk supremum `O((log R)²)`. The Carathéodory coefficient estimate, with the subtraction `Re b(0)=0`, gives

`|b^(j)(0)| <= 2 j! R^(-j) max[|z|≤R] Re b(z) -> 0`

for every positive integer j. Hence b=0, a contradiction. A root g(z₀)=1 has z₀≠0. With λ=1/z₀ and y=(λI-Q)^(-1)u, φ(y)=1 and `(Q+uφ)y=λy`. This eigenline is proper because H is infinite-dimensional.

All boundary cases in the report are handled correctly. In particular, the proof cannot set φ=0 to prove the ISP for Q. For the accepted S the choice A=1, c=5/2 follows from `floor((n+1)²/4)≥n²/4`, including n=0. There is no compactness assumption. The alternatives are exclusive here: when all moments vanish, the rank-one resolvent formula excludes nonzero eigenvalues of the perturbation.

**Prior art:** [Tcaciuc, v2](https://arxiv.org/abs/1805.03277v2), Lemma 2.1, Theorem 2.3 and Proposition 2.4, supply the scalar resolvent and moment mechanism; Theorem 3.3 allows exceptional scalar parameters. The Gaussian growth argument removes the exceptional omitted value for this subclass. Neither that elementary addition nor this review establishes novelty or the requested significance. Tcaciuc does not state a theorem ruling out every rank-two perturbation of the present S.

## 2. Thresholds and sunflower exclusions: verified; explicit prior-art duplication

The actual accepted threshold theorem has constant `25·512^4` and budget 1/2; the discrete-convexity theorem has the integer `2^75`. Their quoted domains and quantifiers agree with the manuscripts. Neither theorem identifies an expectation threshold with a median containment threshold.

For k blocks of size m, k,m≥1, the minimum fractional **and** integral covering cost at every p∈[0,1] is exactly

`min{1,(mp)^k}`.

To prove this, discard sets contained in no minimal transversal; covering all minimal transversals still covers the increasing family. Averaging the fractional covering inequalities over uniform transversals gives `sum g(B)m^(-|B|)≥1`. If mp≤1, multiply by the lower bound `(mp)^|B|≥(mp)^k`; if mp≥1 use `(mp)^|B|≥1`. The full-transversal cover and the single empty-set cover attain the respective bounds. Allowing fractional coefficients in [0,∞) rather than [0,1] causes no discrepancy: truncate each coefficient at 1 without destroying a cover.

Consequently the report's three formulas (3.1), including `q=q_f=2^(-1/k)/m`, are exact. At p=0 the convention is p⁰=1. For m=k→∞ the logarithmic ratio follows by writing `1-exp(-t/k)~t/k`, with `t=log(1/(1-2^(-1/k)))=log k+O(1)`. This verifies both the coefficient and the claimed equivalence, not just the order of magnitude.

The spread statement is correct for every subset B, including those that are not partial transversals (containment probability then zero). At m≥r one can select r pairwise disjoint transversals, so this family cannot refute a proposed theorem restricted to r-sunflower-free systems. At m=r−1, the per-block selections in any r-sunflower must either all coincide or be pairwise different. Pairwise different is impossible; coincidence in every block forces repeated members. Thus the `(r−1)^k` family is r-sunflower-free when members must be distinct.

For k≥2, every edge splits into two nonempty proper subsets, both edge-free by uniformity. Therefore `F ∩ E_2(D)=∅`; repetitions give the same conclusion for every L≥2. This says nothing about a different application of discrete convexity.

**Novelty qualification:** [Shangguan, v1](https://arxiv.org/abs/2609.30263v1), Section 4, subsection “The transversal example,” explicitly proves the same exact threshold identity and m=k asymptotic. The bounded-VC sunflower conclusion is Corollary 5.1, obtained using Theorem 1.3 and Corollary 1.4; citing only Theorems 1.1 and 1.3 as if they directly state it is an imprecise locator. The report already disclaims a sunflower advance; that disclaimer is necessary. [Park–Pham, v2](https://arxiv.org/abs/2203.17207v2) retains the logarithmic random-threshold loss.

## 3. Slope lift and shadows: verified with an explicit compact-interval convention

Choose the slope interval I compact and nondegenerate and the v-ball compact with nonempty interior. Choose δ>0 with `δ sqrt(1+|v|²+s²)≤1` throughout the slope patch. The witness parameter set is

`A={(a,v,s)∈K×B×I: a+t(v,s,1)∈K for all 0≤t≤δ}`.

It is closed in a compact set (it suffices to impose the condition at rational t), hence compact. Its continuous image under `(a,v,s,t)↦(a+t(v,s,1),s)` is the claimed Z. Every slope has a witness. Taking all witnesses, rather than an arbitrary selection, repairs any possible selection-measurability issue. If “interval” were read as open, the original compactness sentence needs the harmless replacement by a closed subinterval.

Each slice Z_s has a Lipschitz projection in R⁴ containing segments in a direction set of Hausdorff dimension 3. The accepted `cor:general-directions-four` gives dimension at least 4 for the projection, hence for the slice. The Hausdorff slicing inequality for the compact Z over a one-dimensional interval yields dim_H Z≥5. The standard interval product upper bound gives `dim_H(K×I)≤dim_H K+1`. Thus the argument gives precisely 4, without a gain. It does not use the generally false product upper bound `dim_H(A×B)≤dim_H A+dim_H B` for arbitrary B.

For each four-plane E⊂R⁵ and y∈E with |y|≤1, choose a unit normal ν and `x=y+sqrt(1-|y|²)ν`. Then x∈S⁴ and its projection is y. This proves the shadow counterexample for every four-plane, not merely generic ones. S⁴ has dimension 4 and no nondegenerate segment, so it refutes only the shadow lemma. A bush through a point refutes a pointwise label bound, without refuting any averaged estimate.

## 4. Equations (7.1)–(7.4): verified; exact logical strength

For U:C²→H and W:H→C² with rank(UW)=2, both U and W have rank 2. Put `A(z)=(I-zS)^(-1)` and `R=zWAU`. Entries of R have logarithmic-square maximum-modulus growth. The determinant does too, since it is a sum of products of at most two such entries. With D(0)=1, the zero-free entire-logarithm argument proves `D≡1` if D has no zero.

If `(I-R(z₀))c=0`, c≠0, put `y=z₀ A(z₀)Uc`. Then Wy=c so y≠0, and `(S+UW)y=z₀^(-1)y`. This verifies the factors of z and the reciprocal eigenvalue. The finite-rank resolvent identity also shows that D≡1 makes S+UW quasinilpotent, not merely free of nonzero eigenvalues.

For a 2×2 matrix, `det(I-R)=1-tr R+det R`. Expanding the absolutely convergent entire series `R=sum[n≥0]z^(n+1)M_n` gives exactly (7.2), with all ordered pairs a,b≥0, a+b=j−2. In particular the first equations are

`tr M_0=0`, `tr M_1=det M_0`,

`tr M_2=(M_0)11(M_1)22+(M_1)11(M_0)22-(M_0)12(M_1)21-(M_1)12(M_0)21`.

There is no pointwise nilpotence implication and no vanishing-moment shortcut.

The controllable closure in (7.3) contains ran U, is S-invariant, and is invariant under UW. Failure gives a nonzero proper invariant subspace. The unobservable subspace in (7.4) is S-invariant and killed by UW; it is proper because W≠0. Failure therefore also gives a nonzero proper invariant subspace. No sufficiency claim follows.

The strong closure of analytic polynomials in one operator is indeed commutative: first commute a limit with each polynomial, then with each second limit, using multiplication by a fixed bounded operator. This does not permit analytic recovery of the noncommutative multiplier/intertwiner algebra. The small-perturbation Riesz-projection argument also passes; its strict norm bound is essential.

## 5. Reproduction and disposition

[checks.py](../experiments/i02_operator_r2/checks.py) copies the original finite script into the authorized support directory, runs it there, and compares its JSON with the original output. All 12 rational probability checks, 4 binary-product sunflower checks and 29 determinant evaluations reproduce exactly. Additional independent exhaustive integral-cover minimizations pass at 16 rational parameters. The new operator log checks are recorded separately in the same output. These computations establish finite identities only. In particular, truncated dyadic fibres and finite controllability matrices do not decide (7.3) or (7.4).

No material false universal deduction was found in the specified portions. The significant qualification is novelty: the exact transversal calculation is already prior art, Proposition R is a classical resolvent argument with a growth observation, and Section 7 remains a research question. The subsequent investigation and its unresolved gap are in [i02-operator-r2.md](../iterations/i02-operator-r2.md).
