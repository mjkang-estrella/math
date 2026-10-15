# Sharp local correlations, and the unpaid Liouville five-pattern bridge

2026-10-14. **Author-level complete supporting theorem; main arithmetic target unresolved. No new substantial acceptance is requested.**

## 1. A complete structural theorem

Let `(X_n)_(n∈Z)` be a strictly stationary process with values in `{−1,+1}`. Suppose

`E X_0 X_h = 0` for every nonzero integer h.

Unbiasedness is not needed for the upper bound. For every integer r≥2,

`|E X_0 X_1 X_r X_(r+1)| ≤ 1−1/r`.                         (1)

For every such r and every σ∈{−1,+1}, there is a strictly stationary, unbiased, pairwise-independent process attaining the value `σ(1−1/r)`. Every joint moment of an odd number of coordinates, including any repeated-coordinate formulation after cancellation, vanishes. No ergodicity, mixing, complete multiplicativity, or Liouville-model dilation axiom is asserted for these extremizers.

### Upper bound

Write `Y_j=X_j X_(j+1) X_(j+r) X_(j+r+1)`. Pointwise cancellation gives

`∏_(j=0)^(r−1) Y_j = X_0 X_(2r)`.                         (2)

For any signs `z_0,...,z_(r−1)`,

`Σ z_j ≤ r−1+∏ z_j`.                                      (3)

Indeed, if k of them equal −1, (3) becomes `r−2k≤r−1+(−1)^k`; equality holds for k=0 or 1, and the other cases follow directly. Apply (3) to `z_j=sY_j`, for each sign s. Stationarity and the hypothesis at distance 2r give

`r s E Y_0 ≤ r−1+s^r E X_0 X_(2r)=r−1`.

Taking s to match the sign of `E Y_0` proves (1). This argument is finite, and needs no limiting interchange.

### Sharpness construction

Fix r and σ. Take mutually independent unbiased signs

- `A_0,...,A_(r−2)`;
- `(C_k)_(k∈Z)`;
- Z;

and an independent uniform phase R in `{0,...,r−1}`. For every integer n write `n+R=rk+j`, `0≤j<r`, and set

`D_n = σ^k A_j` if `j<r−1`, and `D_n=C_k` if `j=r−1`.

Set `X_0=Z`, and determine all positive and negative coordinates by `X_(n+1)=X_n D_n`. This defines a bilateral process uniquely.

The increment law is stationary: increasing the phase by one handles a unit shift until it wraps; at a wrap, reindex the iid C sequence and replace every A_j by σ A_j. These operations preserve their full joint law, independence, and the uniform phase. Conditional on the entire increment sequence, `X_0` is an independent uniform sign. Replacing it under a unit shift by `X_1=X_0D_0` preserves that same conditional uniform law. Hence the X process is strictly stationary.

For i<j,

`X_i X_j=∏_(n=i)^(j−1) D_n`.

If the interval encounters a separator residue `r−1`, at least one independent C_k occurs exactly once, so this expectation is zero. If it encounters no separator, it lies between two successive separator locations, has length at most r−1, and involves distinct A_j's each exactly once, so again its expectation is zero. Each X_i is unbiased because of Z. Thus every distinct coordinate pair has its uniform law on `{−1,+1}²`. An odd joint moment contains an odd power of Z conditional on D, so vanishes.

Finally,

`X_0 X_1 X_r X_(r+1)=D_0D_r`.

With probability `(r−1)/r`, both increments use the same A_j in successive blocks, giving `D_0D_r=σ`. With the remaining probability `1/r`, they are independent successive separator signs, whose product has mean zero. This gives exactly `σ(1−1/r)` and proves sharpness.

The hidden A variables remain global. Replacing this construction by an ergodic or multiplicative model is a separate task. In particular, sharpness in the class just stated does not establish optimality of (1) for Liouville.

## 2. An ordinary Liouville consequence, with its novelty boundary

Assume the pinned source-007 theorem `thm:q-affine`. There is an absolute c>0 such that, for every fixed integer r≥2,

`|Σ_(1≤n≤N) λ(n)λ(n+1)λ(n+r)λ(n+r+1)|`

`≤ (1−1/r)N + O_r(N/(log N)^c + 1)`.                      (4)

Proof: sum the pointwise inequality used above over n, and use the exact telescope (2). Replacing a shift j of the bounded sequence Y by its unshifted sum costs at most 2j; summing j=0,...,r−1 costs at most r(r−1). After division by r, this is at most r−1. The remaining pair sum is `Σ λ(n)λ(n+2r)`, bounded by `thm:q-affine`; its coefficient is 1/r. Apply the two signs s. The bound is for every N, with r fixed before the limit. It makes no claim for r growing with N.

This is a technical corollary, not a new solution of four-point Chowla. The logarithmic counterparts of the adjacent-four estimate and qualitative gapped-four estimate already appear in Tao–Teräväinen (2019), Lemmas 7.2–7.3. Their parity-product mechanism is explicitly credited. Neither an explicit constant nor the substitution of ordinary binary cancellation alone justifies a substantiality claim.

## 3. An exact five-word obstruction to the tempting shortcut

Here is a particularly transparent stationary law realizing the `r=2` upper endpoint. Let B be a global unbiased sign, let `(U_k)_(k∈Z)` be iid unbiased signs, and choose an independent uniform phase in `{0,1}`. Before applying the random phase, put

`X_(2k)=U_k`, `X_(2k+1)=B U_k`.

The law is shift-stationary after randomizing the phase. The shift by two reindexes U. Every single coordinate is unbiased. Two coordinates in the same block have product B with mean zero; in different blocks some U appears once, so their product has mean zero. Every odd moment vanishes because at least one block has an odd number of selected coordinates. Reflection preserves the law by reversing/reindexing the iid blocks; reversing each pair can be absorbed into `U'_k=B U_k`, which are again iid unbiased and independent of B.

For `ε=(ε_1,...,ε_5)`, direct Fourier expansion or finite enumeration gives

`P((X_0,...,X_4)=ε)`

`= (1/32)[1+(ε_1ε_2ε_3ε_4)/2+(ε_2ε_3ε_4ε_5)/2]`.           (5)

There are eight zero probabilities, sixteen probabilities 1/32, and eight probabilities 1/16. Thus exactly 24 five-word patterns occur. All sixteen four-word patterns have positive probability, since their probabilities are `(1±1/2)/16`.

The eight missing five-word patterns, writing signs without commas, are

`---+-`, `--+--`, `-+---`, `-+++-`, `+---+`, `+-+++`, `++-++`, `+++-+`.

In Tao–Teräväinen's equation (7.4), its Fourier parameters are `(a,b,c)=(1/2,0,0)`. It saturates the old a-bound while satisfying the stronger c-bound from (1), stationarity, reflection symmetry, pairwise independence at every lag, and all odd-order correlation vanishings.

**Exact scope of the obstruction:** those stated properties do not imply all 32 five-word probabilities are positive. This is not a completely multiplicative sequence, a counterexample to Chowla, or a counterexample to the desired Liouville positivity theorem. No assertion is made that it satisfies all affine multiplicative-function correlations or the full axioms of Sawin's Liouville-like models.

## 4. The missing arithmetic operation

For actual Liouville logarithmic window laws, classical odd-order logarithmic Chowla, reflection/isotopy, and source 007's binary input give the three-parameter expansion

`32 p_ε = 1 + (∏ ε_i)[(ε_1+ε_5)a+(ε_2+ε_4)b+ε_3c]`.        (6)

The classical bounds `|a|,|b|≤1/2`, together with the sharpened `|c|≤2/3`, still admit the exact boundary point in (5). To prove the selected D1 target, one must exclude every zero-probability facet for genuine multiplicative window limits, with enough compactness/uniformity for a positive lower bound. The supporting theorem does not perform this exclusion.

Uniform positivity over all slowly growing logarithmic windows would imply positive lower natural density: if along X_l the natural pattern count is δ_l X_l with δ_l→0, choose a window factor ω_l→∞ sufficiently slowly that δ_l ω_l/log ω_l→0 and ω_l≤X_l. The weighted pattern count in `[X_l/ω_l,X_l]`, normalized by log ω_l, is at most `δ_l ω_l/log ω_l`, contradicting that uniform positivity. This elementary conversion does not itself prove positivity of a single arithmetic window law.

Exploratory `search_dilation.py` adds necessary finite constraints to the zero-facet model: finite-block stationarity, sign and reversal symmetry, zero pair correlations, the saturated adjacent-four expectation 1/2, and the necessary domination

`law(X_0,X_2,...,X_(2m−2)) ≥ (1/2) law(−X_0,...,−X_(m−1))`.

This domination follows from the even/odd decomposition and λ(2n)=−λ(n), and is only one necessary consequence of multiplicativity. HiGHS found floating-point feasible relaxations at m=6,8,10 (full block lengths 11,15,19). The largest equality residual was below `1.3e−14`. **This is a numerical diagnostic, not an exact certificate, an inverse-limit construction, or a mathematical impossibility theorem.** It rejects the hope of a contradiction from just those small finite relaxations.

## 4.1. Analytic proof of the restricted-host obstruction

For D3, take high-degree vertices A={0,2,4} of degree three and low-degree vertices B={1,3,5} of degree one, in the host K_6 minus {01,23,45}. Let a, b and c count edges inside A, inside B, and across the partition. Degree sums give `2a+c=9` and `2b+c=3`, hence `a−b=3`. Since a≤3 and b≥0, necessarily a=3, b=0 and c=3. Thus A induces a triangle, B is independent, and the cross edges form a perfect matching avoiding its three diagonal forbidden pairs. There are exactly two such matchings: the two derangements of three objects. Their symmetric difference has six edges. A four-edge switch cannot pass between them, and no third realization exists. Both states are therefore isolated. A six-edge alternating-cycle move does connect these two particular states; no all-n connectivity or mixing conclusion follows from that observation.

## 5. Validation and Lean scope

`python exact_checks.py` uses only the Python standard library and exact integers/Fractions. It checks 10,912 pointwise configurations for r=2,...,6, the two sharp constructions for r=2,...,8 including all distinct coordinate-pair moments in the sampled interval, every odd moment supported on its first five coordinates, the exact distribution (5), and a mutation that removes fresh separator randomness. It also reproduces D3's two isolated six-vertex realizations. These checks support the general proofs; they do not establish their universal quantifiers.

`Support.lean` compiles and checks only the finite r=3 telescoping identity and signed pointwise inequality on seven Boolean signs, after translating them to integers. Its successful compilation and printed axiom dependencies are recorded in `lean-validation.txt`. It does not formalize expectations, probability-space construction, stationarity, arithmetic cancellation, limiting density, source-007's theorem, or any novelty assertion. There is no axiom restating a new conclusion and no `sorry`.

The exploratory LP requires NumPy/SciPy, unlike the exact checks. Its solver output is isolated in `lp-results.txt`. The generated virtual environment is ignored; no dependency on it is needed for `exact_checks.py` or the proof.

## 6. Independent review tasks and disposition

1. Proof reviewer: check all-negative-index definitions in the sharpness construction, phase-wrap invariance for σ=−1, independence of the shifted initial sign conditional on D, exact all-lag pairwise independence, and the boundary error in (4). Separately inspect the finite five-word formula and the exact scope of its obstruction.
2. Contribution reviewer: compare the complete sharp stationary-process extremum with pairwise-independent stationary-process constructions, algebraic subshifts/coding theory, and the parity-product operations in Tao–Teräväinen Section 7. An absence of matching search titles is not evidence of substantiality. The authors' probable-technical classification is part of the handoff.
3. Arithmetic reviewer/researcher: develop or refute an actual multiplicative rigidity mechanism excluding boundary facets of (6), including every needed dilation and window quantifier. Do not silently replace this with the supporting white-spectrum theorem.
4. Formal reviewer: reproduce `Support.lean` in the parent's pinned environment and inspect its printed dependencies. A finite local supporting lemma is not a formalization of D1 or of the full stationary-process theorem.

No independent proof or novelty gate has run. Nothing here is paper-ready as a new frontier solution, and no Zenodo/MathDB upload, new accepted count, or priority claim is proposed.
