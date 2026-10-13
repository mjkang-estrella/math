# I229 — independent contribution gate for forced infinity regularity

**Final verdict: DOES NOT CLEAR the original brief's stringent independent-contribution gate.** Theorem R is a meaningful enlargement of the solution class and is not the theorem stated in any of the primary comparisons below. Nevertheless, relative to the **full stipulated pinned proof package**, its submitted proof is a technical bounded-forcing extension of that package. The two nominated additions do not supply a sufficiently independent, nonroutine bridge. Theorem S adds a useful restricted stability statement, but its barrier and interpolation are technical once R is available.

This is a contribution decision, not an I228 proof decision. I read the completed I224 argument, including its payment of the anisotropic forcing residual; I have not presumed that an earlier missing estimate remains missing. I have neither read I228 nor certified its outcome. No acceptance-count change is recommended. No worldwide priority assertion follows from the literature retrievals.

## 1. Exact object being judged

For each integer d≥3, R asserts the existence of constants a_d∈(0,1/3] and A_d<∞, uniform over **every** bounded u∈C(B1) solving −Δ∞^N u=f for **every** f∈C(B1)∩L∞(B1), such that u∈C^{1,a_d}(B1/2) and

    ||Du||∞ + [Du]a_d ≤ A_d (osc_B1 u + ||f||∞).

The displayed norms are on B1/2. Neither a modulus of continuity of f, a derivative of f, its sign, semiconcavity of u, nor a lower bound on |Du| is assumed. The result quantifies over existing solutions and does not assert existence or uniqueness for arbitrary sign-changing data. On B_(2r)(z), the corresponding right side for the gradient estimate is C(osc u/r+r||f||∞), with r^{a_d} on its seminorm term.

S restricts to 0<m≤1, 0<ε≤min(1,m²), an infinity-harmonic v∈C(cl B1) with 0≤v≤1 and inf_B1|Dv|≥m, and any existing u∈C(cl B1) with the same boundary trace and continuous forcing ||f||∞≤ε. It asserts actual continuous interior gradients and

    ||u−v||∞,B1 ≤ ε/m²,
    ||Du−Dv||∞,B1/2 ≤ C_d (ε/m²)^{a_d/(1+a_d)}.

Only v has the nonvanishing-gradient assumption, over the whole open ball. This is not a boundary-gradient estimate, a p-to-infinity theorem, or a stability result through critical points of v.

The normalized convention is essential: at an upper test with p≠0, −X[p]/|p|²≤f; at p=0, −λmax(X)≤f. Lower tests use ≥ and λmin. Multiplying the nonzero-gradient equation by |p|² does not preserve this full critical-gradient convention. In particular, Lindgren's unnormalized theorem cannot simply be relabeled as R.

## 2. Exact overlap with the stipulated source

The pinned [main statement](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/01-introduction.tex), `thm:main`, concerns exact Δ∞u=0, d≥3, and a dimension-dependent nonexplicit exponent. It does not assert R. Its lower operations, however, contain almost the entire submitted mechanism:

* [02-flatness.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/02-flatness.tex): linear lift; cone slopes and fixed-center affine blow-ups; theorem of sums; the three-point penalty, its localization, bounded contact gradients, and its negative Hessian divergence.
* [03-reduction.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/03-reduction.tex): slow-scale transfer to uniform family flatness, worst bad-parameter modulus, factor-two running maxima, all-nearby-center/all-fixed-scale fits, cylinder comparison, anisotropic normalization, compactness, passage of every required shear fit, nonaffinity, and summable slope extraction.

The exact Liouville contract in `thm:liouville` is an entire continuous solution of D²V[(D_xV,1)]=0 on R^m×R, m≥1, with one C0 and affine fits at every center and every R>0 on |l|≤R, |h−pl|≤R. The time coefficient q is unrestricted: q=a−|p|²/2. The theorem is not an inhomogeneous Liouville theorem. The candidate does not claim that it is: Section 3.6 attempts to produce precisely this homogeneous limit with C0=256.

`lem:cylinder-comparison` is explicitly equation-independent. Its inputs are fits for the same function, common parameter θ², comparable radii or the specified overlapping centers, and positive uniform upper/lower bounds for slope norms. The geometry and compactness portion of `prop:nonaffine-limit` then consumes those fits. Reusing it does not require solving a new geometric or Liouville problem. The source's PDE verification must still be replaced, rather than treating the whole proposition as a black box for forced functions.

The complete family-377 path list contains one manuscript; the matching README, main file, bibliography and sections 01–03 were read. No forced companion statement was found in that bounded same-family check. This is not a semantic search of every other manuscript.

## 3. The genuinely relevant changes, assessed as submitted

### 3.1 Preliminary forcing and flatness steps

The candidate uses the closed inequalities X[p]≥−F|p|² at upper tests and X[p]≤F|p|² at lower tests for the lifted function. The affine graph test and the vertical test at horizontal gradient zero are the source lift calculation with an error bound retained. Its cone calculation inserts quadratic curvature F and gives L_r^±≤L_R^±+FR. Linear blow-ups eliminate this O(rF) error. These are useful checks, but almost-monotone slopes and affine blow-ups for bounded inhomogeneities already have close primary precedent in Lindgren; quadratic comparisons for the normalized equation are explicit in Lu–Wang.

### 3.2 Three-point extension

The important submitted observation is that the **same** source penalty still yields

    A[σ] ≥ −C(F0,L,δ),
    A[σ] = −3B a²/(8√r) + O(1) → −∞.

The lower bound accounts for all three jets, including the factor 2 for −2W. No derivative of f is used. This is stronger than assuming C¹ bounds on u, and I do not dismiss it as final interpolation. But the source already supplies the entire penalty, r→0, h=O(r²), bounded test gradients, a≥δ/4, and the divergent negative term. Replacing its lower bound zero by a fixed negative constant leaves the contradiction unchanged. No new penalty, coercive direction, compactness topology, or cancellation is introduced. Under the stipulated lower operations, this is the standard robustness check for bounded lower-order jet errors.

### 3.3 Scale selection and the limiting equation

The completed proof explicitly asks its existing factor-two running maximum to exceed i:

    b(s_i)/s_i^{γ_i} ≥ i,   0<γ_i≤1/2,
    λ_i > b(s_i)/4,   r_i≤s_i D(z_i).

Consequently

    r_i/λ_i ≤ 4D(z_i)s_i/b(s_i) ≤ 3s_i^{1−γ_i}/i → 0.

This is an actual payment of the forcing residual, not a missing estimate. But failure of every power bound already gives an unbounded running maximum near zero. Requiring it to exceed i is free within the source selection; it is not a new estimate on solutions. The nearby fit bound remains the source's 8λ_i(2M)^{γ_i}<32λ_i for each fixed M.

Under the source's anisotropic change of variables the error is

    r_i/(c_i λ_i) · {λ_i|D_xφ|²+(1+λ_i φ_t)²},   1/2≤c_i≤L+1.

Thus it vanishes on compact jet sets. The remainder of the argument uses the unchanged source fit passage, same shear, same C0=256, same nonaffinity contradiction, and same exponent conversion a_d=γ/(2+γ). The candidate has correctly identified the place where naive isotropic perturbation would be inadequate; nevertheless its repair uses only slack already present in the stipulated running-maximum construction.

Taken together, these changes establish a plausible **robustness corollary of the source proof**, conditional on the separate proof gate. Calling the resulting theorem important does not make these modifications a new independent method. Under a looser standard accepting useful new corollaries, R would merit recording; under the original express exclusion of standard transfers, I would not nominate it as the tenth substantial finding.

## 4. Primary literature comparison and limits

**Lindgren (Proc. AMS 142 (2014), 277–288).** The accessible [manuscript transcription](https://doczz.net/doc/7566335/on-the-regularity-of-solutions-of-the) states Δ∞u=f with the unnormalized cubic-in-amplitude operator. Theorem 1 gives linear subsequential blow-ups for bounded continuous f; Theorem 2 assumes f∈C¹∩L∞ and gives uniqueness of the linear blow-up/differentiability, in arbitrary dimension. Its Section 2.1 raises dimension by adjoining linear and |t|^{4/3} variables to arrange slope and sign assumptions; Section 3 uses almost-monotone slopes and homogeneous blow-up limits. It does not state uniform Hölder gradient bounds. The author-page PDF link and AMS retrievals failed, so the retained evidence is an explicitly identified transcription, not an authenticated published PDF. Its malformed Definition 1 is not used to resolve viscosity conventions. This limits the bibliographic certainty, not the independent source-overlap calculation above.

**Crasta–Fragalà (arXiv:1506.05305v1).** [Definition 1 and introduction](https://arxiv.org/html/1506.05305v1) use the normalized critical-gradient convention stated above. Their main problem has source +1, zero boundary trace, and a bounded convex domain in R^N. Power concavity supplies local semiconcavity; [Section 4](https://arxiv.org/html/1506.05305v1#S4) supplies C¹. Theorem 16 separately requires local semiconcavity. Its displayed general operator notation and the proof's Δ∞^+ notation are not perfectly aligned; neither reading removes semiconcavity or supplies R's uniform Hölder estimate. Thus R's arbitrary interior solutions and arbitrary continuous sign-changing forcing are real differences.

**Lu–Wang (Comm. PDE 33 (2008), 1788–1817).** The [author-hosted article](https://www2.math.uconn.edu/~guozhenlu/papers/cpde_lu_wang_published.pdf), Theorems 1.7/2.2/2.4, provides normalized polar-quadratic comparison with continuous f in arbitrary dimension. Theorem 5.3 concerns uniform value stability around forcing bounded away from zero with one sign. Theorems 1.9/5.4 allow forcing tending uniformly to zero (no sign required for that sequence) and give uniform convergence of values, with the specified Lipschitz boundary data for the zero-forcing limit result. No gradient rate is asserted there. S has stronger gradient information conditional on R, but different boundary/gradient hypotheses; it should not be described as directly containing their whole theorem.

**Perturbation after homogeneous regularity.** [Imbert–Silvestre, arXiv:1201.3739v1](https://arxiv.org/abs/1201.3739), Theorem 1, assumes |Du|^γ F(D²u)=f, γ≥0, **uniformly elliptic** F with F(0)=0, and bounded f. Lemma 2's flatness improvement is uniform in every affine shift p; the proof identifies homogeneous limits. This is a primary example of the standard perturbative mechanism, not a theorem applicable to normalized infinity-Laplace. The latter's directional matrix has rank one: even at a nonzero gradient, there is no positive ellipticity constant in transverse directions. Replacing finite-p estimates by their p→∞ limit also lacks uniform constants. The full pinned anisotropic proof package, rather than this general theorem alone, is what makes I224's particular extension routine.

**Sobral–Teixeira–Urbano, October 9, 2026, arXiv:2610.13137v1.** [Theorems 1.1, 1.3, 1.4 and Section 3](https://arxiv.org/html/2610.13137v1) were checked. Theorem 1.1 concerns fixed p>2 and homogeneous p-harmonic functions; constants depend on p. Theorem 1.3 concerns homogeneous planar infinity-harmonic functions, every β<1/3. Section 3 expressly notes the one-direction large-shift obstruction and uses homogeneous C¹ compactness plus a separate quantitative near-affine result. Theorem 1.4 is a different nonlocal equation with its own differentiability/tail hypotheses. None automatically states R in d≥3 with forcing. The overlap is compactness, variable scales and slope reconstruction, not an identical forced theorem.

Therefore I do **not** assert that one of these external papers has already published R or S, or that homogeneous C¹,α regularity by itself entails R through an off-the-shelf uniformly elliptic theorem. The narrower conclusion is that the completed I224 argument is a routine extension **once the specified pinned lower operations are granted**. The alternatives “not explicitly in these papers” and “substantial independent contribution” are not equivalent.

## 5. S, proof separation, and record

For S, T_±'(s)≥1 and T_±''=∓2κ, κ=ε/m², give strict comparison barriers through Δ∞^N T(v)=T'(v)Δ∞^N v+T''(v)|Dv|². R then supplies common C¹,a_d bounds and the difference quotient gives 2κ/h+Ch^{a_d}. These are exactly the technical parts acknowledged by I224. The upper-exponent examples delimit stronger claims but do not provide a new positive regularity mechanism or establish optimality of the submitted exponent.

I checked the contribution-relevant use of the lower-operation hypotheses and the residual scaling, not the truth of any pinned theorem. I raise no alleged contradiction to the stipulated homogeneous source. My negative contribution verdict stands even if the separate proof gate passes; conversely it does not imply that proof gate passes. No I228 output or other active work was consulted.

A partial review was written before the final literature comparison. Exact input/output/source hashes, byte counts, and reading scopes are in `frontier/experiments/i229_forced_infinity_contribution/input-authentication.json`; the manifest's own hash is returned detached. No research code, numerical experiments, scans, tests, snapshots, seals, historical replay, shared edits, staging, commits, or publication were performed. Scripts were limited to retrieval, extraction, bounded source lookup, and hashing. An initial catalogue display was overly broad and truncated; only the family-377 catalogue passage was used, and no other review content was opened.
