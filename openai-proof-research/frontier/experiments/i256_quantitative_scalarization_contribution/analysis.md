# I256 — independent contribution analysis of quantitative scalarization

**Verdict: TECHNICAL.** This is the contribution/substantiality gate for the complete positive-deficit theorem Q1–Q4, conditional on the independent proof gate accepting its exact argument. It is a useful explicit quantitative extension, and the inspected primary sources do not already state its full coefficient recovery conclusion. Under the requested standard requiring a nonroutine advance beyond R016, however, it does not justify a separate substantial finding. This is neither a proof rejection nor a KNOWN verdict. No accepted count is changed.

Reviewed candidate: `frontier/experiments/i247_quantitative_complete_rigidity/analytic-attempt.md`, SHA256 `7d8b629513741abab53339c19bb05c9f611ecbd0af1b6ace3246dff8af0eae8b`, verified against the actual bytes. The original brief and final discovery report were read in full. I252's interrupted files and later review outputs were not read. Its supplied provisional hypotheses were reassessed against actual arguments, not adopted as findings.

## 1. Exact result assessed

For d≥2 and R,δ,g,ℓ>0, A∈M_d(C), K=W(A) with interior contained in R Dbar, assume dist(σ(A),∂K)≥δ and a regular analytic boundary arc Γ of length at least ℓ on which Re(conj(ν)A) has simple maximal eigenvalue with gap at least g. For arbitrary finite coefficient dimension m and arbitrary finite-degree P∈M_m(C)[z], normalized by max_K||P||=1, put γ=||P[A]||≥2−ε, 0≤ε≤1/2. The candidate sets

    K0=(3R)^(d−1)δ^(−d),
    C0=8(d−1)R K0[9πR²/(gℓ)+1/√6].

Every unit maximal singular pair x=vec X,y=vec Y has squared Schmidt tails t_X=1−||X||op² and t_Y=1−||Y||op² at most min(1,C0√ε). Its leading Schmidt products x0=ξ⊗u,y0=η⊗v have distances at most √(2C0)ε^(1/4), and p(z)=v*P(z)u has max_K|p|≤1 and

    ||p(A)||≥γ[1−t_X−t_Y−√(t_X t_Y)]≥2−ε−6C0√ε.

The same scalar-existence conclusion is asserted for an active reducing block B satisfying the geometric conditions and ||P[B]||=||P[A]||, with P normalized on the full W(A). That formulation does not assert Schmidt control for every maximal pair of the full direct sum: a pair can mix other active blocks. The statement concerns an exact maximal singular pair of each finite evaluation, not arbitrary approximately norming pairs.

There is no claim of disk proximity, optimal constants/exponents, whole-P rank-one approximation, scalar-style output block rigidity, or a uniform gap below two for all varying witnesses. These exclusions are essential. The four-dimensional Crabb chain is a known nonvacuity example, not an extra result.

## 2. What the sources actually supply

### R016, I242 and I246

R016's exact theorem already extracts a scalar compression from the specified complete polynomial witness, for every finite coefficient size and degree in base dimension at most four. More importantly for this review, I242's Lemma S already proves the conditional mechanism in arbitrary d whenever an interior spectrum and a simple support arc are supplied. It applies to every maximal singular pair. Its mechanism is the original mass-two positive field H, D=XX*−YY*, zero block slack H^(1/2)DH^(1/2)=0, and X*Y=0. Rank H=d−1 together with inertia forces rank X=rank Y=1.

I242 Section 7 explicitly states that for a fixed irreducible block, its residual equations and an arc with fixed nonzero support gaps control proximity of D to rank-(1,1) inertia data. It identifies the unresolved uniform difficulty as collapse of support gap, arc length, boundary spectral distance and reducing strata under the original weak normalization, followed by transport to full geometry. This passage is a qualitative indication, not an already-proved Q1–Q4 rate. It nevertheless fixes the already-known quantitative route. I247 imposes exactly the first three controls as hypotheses and does not solve the remaining geometry/degeneration problem.

The prior I246 award was for the new link from complete block equality to codimension-one supporting geometry and thus input scalarization. It explicitly denied credit to the inherited deficit identity, standard inertia, Herglotz/Fourier control, scalar rigidity and dimension/degree changes separately. Q1–Q4 reuses that same link. I246's verdict on E4 does not certify Q1–Q4; equally, its importance does not make every quantitative corollary a new substantial finding.

### The pinned direct and structural companions

I read all retained actual statements and relevant proofs, and independently matched their blocks to the pinned raw main.tex bytes and immutable tree blobs. Upstream truth is stipulated. The direct paper's `thm:domain` proof already uses unit maximal singular pairs, both ordered multiplication tests, reciprocal coefficient weights and the positive-block comparison at arbitrary finite degree and coefficient size. Its off-diagonal energy depends on X,Y and a resolvent field, not on a sum of polynomial coefficient magnitudes. Keeping the slack gives the residual used by both I242 and I247.

The structural companion's `thm:structural`, `thm:representation`, `prop:density`, equality fibers and `lem:comparison` were read at the statement/proof level. Its common mass-one density represents a similar matrix; it cannot be substituted for the original field whose rank is controlled by the numerical-range support. The fiber equalities permit matrix-valued isometric channels. Neither companion states Q2–Q4. Their all-degree/all-coefficient uniformity is a credited input to the recovery argument, not newly obtained functional-calculus uniformity.

### ACV v3

The relevant Sections 3, 5, 7, 9, 10 and 11 were read in full, including their proofs. Section 5's rectangular compression bounds coefficient support dimensions by d. Its variational Lemma 5.2 and Theorem 5.3 give orthogonal base Schmidt families for minimal exact extremals, with r+s≤d; they do not force both ranks one. Section 7 leaves the (2,2) configuration in dimension four.

Theorem 9.5 gives bounds on tuple products T_iT_jx from a pointwise column norm bound. Theorems 9.7–9.8 and Corollary 9.9 control iterates and a two-dimensional nilpotent approximation of a scalar matrix value f(A). They do not recover tensor factors of the input/output pair of an arbitrary specified matrix polynomial. Theorem 10.4 concerns scalar extremal representing measures and their Fourier coefficients. Section 11's all-dimensional scalar polynomial classification, d≤3 complete statements, and the later inverse-algebra criterion all remain within those respective contracts. [ACV v3](https://arxiv.org/html/2608.27346v3).

In particular, a matrix pointwise operator bound ||P(z)||≤1 does not supply the simultaneous scalar-entry column bound needed to import the tuple theorem with unit normalization. Applying a scalar theorem to I_m⊗A does not turn arbitrary matrix coefficients into scalar coefficients. The known weighted-chain example makes this failure concrete. Thus ACV is close motivation and supplies a stability pattern, but it is not an already-published proof of Q2–Q4.

### Jin v2

I read Sections 1–8 and Corollary 1 completely, and Section 9's stability statements, Lemma 11, Proposition 7 and complete proof of Theorem 3. Theorem 1 is scalar disk rigidity. Its rational-collapse, full-lemniscate and divisibility/contact proofs use exact identities, not a quantitative complete coefficient estimate. Theorem 3 is a scalar-domain near-equality result with a compactness modulus; it has no stated power law and does not recover coefficient Schmidt factors. The nonconstructive modulus is explicit in its own Section 9 conclusion. This is relevant prior art, but not the theorem under review. [Jin v2](https://www.preprints.org/manuscript/202609.0079/v2).

### The primary Poisson-kernel overlap

The bounded current search independently located *Degeneracy of the Operator-Valued Poisson Kernel Near the Numerical Range Boundary*. I read the actual v3 local offset assumptions, Proposition 7 and its full proof, and Proposition 8 and its full proof; the v2 page was also inspected before checking the current v3. The proof of Proposition 8 already establishes, at a nonspectral support point σ0 with top support multiplicity m and supporting spectral gap γ_H,

    λ_(m+1)^ascending(P0)≥γ_H/||σ0I−A||²,
    P0=Re(n(σ0I−A)^(−1)).

This is the local positive-spectrum estimate in Q8: I247's H is 2|q|P0, m=1 and ||σ0I−A||≤3R. It is a congruence/minmax bound, not new Poisson-kernel rigidity. Proposition 8 also controls the off-boundary bulk by resolvent perturbation. The paper has no conclusion about complete near-extremizers or X,Y. Its local estimate overlaps one supporting ingredient, not the whole recovery theorem. [Primary v3](https://www.preprints.org/manuscript/202602.0563/v3), Proposition 8, proof.

## 3. The increment, examined rather than inferred from a new formula

Write S for the inherited residual budget. The entire post-R016 quantitative passage can be localized as follows.

1. **Energy bookkeeping.** The determinant/singular-value estimate bounds ||(wI−A)^(−1)|| by K0, and convex exterior control gives |q|≤4R. Unit HS norms give a²≤16R²K0², so S≤64R²K0²ε. This is a useful explicit bound for nonnormal matrices, but elementary and independent of P for the same reason the old residual energy was. Colliding eigenvalues do not add a new mechanism.

2. **Arclength weighting.** Put b(t)=||H^(1/2)DH^(1/2)||HS. On the good arc, Q8 is ||Π_tDΠ_t||≤9R² b(t)/(2g|q(t)|). Since ∫_I b²dτ≤S and ∫_I |q|dτ≥ℓ/(2π), Cauchy–Schwarz gives ∫_I |q|²dτ≥ℓ²/(4π²), and weighted averaging gives inf_I b/|q|≤2π√S/ℓ. This really removes a lower bound on conformal speed or harmonic measure. It is the best technical refinement here. But it asks for exactly the rank-(d−1) arc already used by Lemma S and replaces a pointwise nuisance by elementary averaging. No propagation or unique continuation, new boundary theorem, or control of a collapsing support stratum is required.

3. **Quantitative inertia.** Interlacing gives λ2(D)≤η and λ_(d−1)(D)≥−η with η=9πR²√S/(gℓ). For κ=||X*Y||op≤√(S/6) and a2=λ2(XX*), the top-two-dimensional spectral subspace yields a2−κ²/a2≤η, hence a2≤η+κ; exchange X,Y. This is a genuine explicitly written replacement for exact orthogonal inertia. It keeps the overlap rather than silently setting it to zero. The proof is an elementary right-inverse/minmax perturbation of the existing rank argument. Its generic square-root scale is already dictated by the squared residual.

4. **Stationary-pair cancellation.** Choose leading Schmidt products with x0=ax+e, y0=by+f, e⊥x, f⊥y and ||e||²=t_X, ||f||²=t_Y. For any bounded operator T with Tx=γy and T*y=γx,

       y0*T x0=γab+f*T e.

   Both mixed terms vanish without a gap in the largest singular value. Consequently the loss is bounded by γ(t_X+t_Y+√(t_Xt_Y)). The improvement over a naive Lipschitz fourth-root loss is real. The cancellation is also the ordinary stationary identity for a bilinear singular-vector norm objective, valid independently of Crouzeix, conformal geometry, or tensor structure. It does not overcome a new obstruction to scalarization once the Schmidt tails are controlled.

The combination supplies a new explicit technical statement; this review does not say that each standard inequality automatically makes a theorem routine. The reason for the judgment is stronger: the complete-certificate-to-boundary-rank bridge, its every-pair quantifier, its coefficient compression, its uniform energy structure, and its applicability to a simple-support arc are all present before I247. The present hypotheses provide the precise coercivity and energy controls needed to perturb that bridge. The remaining argument is those four direct estimates, without a second structural idea, a new rigidity class not covered conditionally by Lemma S, or a paid degeneration/geometry step.

## 4. Uniformity is meaningful but does not by itself clear this gate

For fixed d,R,δ,g,ℓ, Q2 tends to rank-one factor recovery and Q4 tends to scalar ratio two along sequences with arbitrarily growing m, degree and coefficient norms. This is stronger than a compactness modulus at fixed coefficient size and degree. The estimate is informative for ε sufficiently small relative to C0^(−2). Large explicit constants alone are not a contribution objection.

Nevertheless, m-independence follows directly from ||X||HS=||Y||HS=1 and a base resolvent operator bound. Degree and coefficient magnitudes disappear before the new estimates begin, in the inherited complete residual. The leading Schmidt compression has bounded base rank already by finite-dimensional tensor algebra. Carrying this inherited uniformity through elementary minmax and stationarity is worthwhile, but does not create a second nonroutine complete functional-calculus theorem. The all-dimensional simple-arc scope also already appears in I242's conditional Lemma S. Neither changing zero to a positive explicit deficit nor improving a deliberately naive replacement bound is sufficient, on its own, under the stated standard.

The every-maximal-pair assertion deserves credit as a stronger recovery formulation than scalar existence. It still uses the same arbitrary pair allowed by the direct proof and by Lemma S, with no new selection or singular-subspace argument. The lack of a top singular-value gap is handled by exact stationarity, not a new spectral perturbation theorem.

## 5. Counterexamples and limits

The stadium family keeps R and interior spectral distance controlled while g collapses and some maximal pairs keep Schmidt tails 1/2 as the ratio tends to two. It correctly distinguishes every-pair recovery from existence of some scalar compression. It does not prove an optimal g-dependence, show the exponent is sharp for a fixed nondegenerate class, or resolve scalar-existence recovery through degeneracy. It explains the hypothesis, but is an elementary obstruction accompanying this technical extension.

The weighted-chain example prevents scalar-output nilpotent rigidity for P[A]. Unused channels prevent whole-P approximation. Disk-contained inactive blocks prevent classification of all of A from a good active block. These attacks are compatible with the proposed conclusion and help prevent false claims; they do not add an independently substantial result.

Disk rigidity is excluded throughout this gate. I do **not** classify the scalarization theorem as TECHNICAL just because the original geometric target was not finished. The verdict concerns the scalarization increment itself. Conversely, a contribution pass for scalarization could never be represented as a quantitative disk theorem. Applying ACV after Q4 would concern p(A), while inversion to A can fail at critical or merged spectral values. The degree-three equality example itself rules out casually requiring p'(0)≠0.

## 6. Final disposition and what would change it

- **TECHNICAL:** an explicit, potentially useful positive-deficit corollary of the accepted structural mechanism, with meaningful uniform recovery and careful constants.
- **Not KNOWN:** no inspected primary statement already gives this full specified-witness coefficient/Schmidt theorem. The Poisson-kernel overlap is partial.
- **Not SUBSTANTIAL:** relative to R016 and I242, the remaining advance under the imposed nondegeneracy is perturbative bookkeeping, averaging, minmax and generic stationarity, rather than a distinct nonroutine structural theorem.
- **Not UNRESOLVED at this gate:** the bounded contribution comparison supports a decision. Worldwide priority is unproved, but that absence is not the reason for downgrading it. Proof correctness is separately undecided by this review.

No local proof repair is requested here; that would exceed the contribution gate. Renaming, tightening constants, or appending a compactness modulus would not address the contribution objection. A later independent candidate could earn a different assessment by resolving an actual remaining structural barrier—for example, recovery of a near-norming scalar channel through allowed support-gap degenerations, a justified sharp rate with substantive necessity on a fixed class, or an explicit geometric rigidity theorem without an inverse-polynomial shortcut. These are directions for reassessment, not asserted sufficient repairs and not new results proved here. No repair or author rebuttal has been made in this round.

Preserve Q1–Q4 as technical progress, subject to its separate proof gate. Do not add an accepted finding or alter the supplied ten-of-twenty count.
