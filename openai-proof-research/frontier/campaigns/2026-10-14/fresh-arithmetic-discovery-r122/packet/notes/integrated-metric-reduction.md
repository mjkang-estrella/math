# Anticanonical metrics: the strongest integrated reduction

PREFREEZE / no nominee. These are derivation and comparison notes, not a frozen new theorem, an independent correctness/contribution grade, or an author-proof submission. The pinned source statements AND their operative constructions are stipulated true. The point of the calculation is to determine what they already pay when composed with the actual singular-metric primary interfaces. No new substantial result is claimed.

## 1. Working scope and credited inputs

The explored question kept W integral projective over C, Q-factorial, (W,D) klt with D an effective rational divisor, P=−(K_W+D) nef and Q-Cartier, and χ(W~,O_W~)≠0 on a smooth projective resolution. The only prospective change from the bounded-metric source was to assume that ρ*P has a semipositive singular metric with zero Lelong numbers everywhere, instead of locally bounded weights. The sought conclusion remained a nonzero section of mP for some positive integer m with mP Cartier. Dimension, boundary, Euler, Q-factoriality and the actual line bundle were not weakened or replaced by numerical effectivity. This was a working question, never a frozen theorem.

Use the following short source names, all at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb:

- Bounded: Bounded anticanonical metrics on klt pairs and torus quotients. Full criterion.tex was read, not just its theorem.
- Indices: Invariant anticanonical indices and conversion of twisted differentials. Full conversion.tex and differentials.tex were read. This is the ordinary fixed-error comparison; no equivariant result is proposed.
- Controlled: Integrable metrics and effectivity with controlled boundary. Full approximation.tex, effectivity.tex and conversion.tex were read. In particular its controlled-boundary theorem, its single-Iitaka and all-dominated constructions, its actual rank-one hull and the exceptional-support return are operative inputs.

Primary interfaces actually read include DPS hard Lefschetz with multiplier ideals (statement and §2.4 proof), LMPTX's cotangent-subsheaf and determinant/nonvanishing proof chain, PT's singular direct-image extension with its codimension-one semistable proof, Fujino's full Kollár–Nadel proof, and DK's singularity-exponent definitions and Skoda/Hölder properties. Further source/primary reading and its limits are in READING.md.

The first attempt concentrated on Bounded's essential-supremum construction. The later Controlled reading was BEFORE this integrated note and changed the conclusion: a failure of that particular limit does not leave a nonvanishing operation unpaid.

## 2. Zero Lelong numbers already pay the cohomological beginning

Use weights φ with squared norm exp(−φ). DK §1.4(8), with its factor-of-two convention translated, gives

    ν_x(φ)=0 for every x  ⇒  exp(−tφ) is locally integrable for every t>0.

Thus every positive tensor power has trivial multiplier ideal. The converse boundedness assertion is false and is not used.

This all-power integrability survives the fixed higher resolutions needed for the algebraic construction. One can see it without imposing a new uniform condition on all fibers. For a modification μ:S→W~ between smooth spaces, work off the exceptional image, where μ is an isomorphism. The pushforward of a smooth volume on S has density w on W~. In local coordinates,

    ∫ w^(1+ε) dV = ∫ |Jac μ|^(−2ε) dV_S

up to smooth positive factors and a finite sum of charts. For sufficiently small ε>0 the right side is finite (small-exponent integrability of a nonzero holomorphic function). Hölder then combines w∈L^(1+ε) with exp(−tφ)∈L^q for every finite q to show exp(−tφ∘μ) integrable upstairs. Properness permits a finite covering on compact sets. This is a fixed-modification calculation; no exponent uniform over an unbounded family of modifications is asserted.

Choose r0 making r0P Cartier. The polynomial

    χ(W~, K_W~ + tρ*(r0P))

is nonzero at t=0 by Serre duality and the supplied Euler hypothesis. It is nonzero for arbitrarily large positive integers. Fix a nonzero cohomological degree on a subsequence and apply DPS hard Lefschetz, using the trivial multiplier ideals. This gives twisted differential forms at unbounded positive exponents. If the differential degree is zero there is already a section of a positive multiple of P.

Otherwise the generic-span determinant argument and LMPTX Theorem4.1 give

    N_i ≥ 0,   N_i ~_Q M + m_i P,   m_i → ∞,   −M pseudoeffective.

This is exactly Bounded's determinant lemma, including its treatment of a numerically trivial P. Unboundedness of the sums of basis exponents, saturation in a reflexive cotangent tensor and effective Weil divisors are all already supplied. We do not promote this to a new operation.

## 3. The algebraic base does not need an infinite metric limit

Use Bounded's maximal dominated fibration and normal equidimensional intermediate model:

    S → S0 → W,     f:S→Y,     f0:S0→Y,
    dπ*P − f*A pseudoeffective,

with S,Y smooth projective, Y connected, f having connected fibers and A ample. The base field is relatively algebraically closed in C(W). On S0 every vertical prime dominates a base prime. Divisors on the final smooth S mapping into base codimension at least two are exceptional over S0 and therefore over W. The final smooth morphism is NOT asserted equidimensional.

The source pencil exclusion uses Q-factorial pushforward of numerical classes and the negativity lemma. It applies to systems bounded above by a multiple of π*P plus a π-exceptional divisor, after any fixed base twist. In particular ratios from the three-index interpolation lie in C(Y).

Set R=(N_2−N_1)/(m_2−m_1) ~_Q P. The interpolation supplies rational principal divisors Q_i on Y with the ACTUAL divisor identities

    π0*N_i = π0*N_1 + (m_i−m_1)(π0*R+f0*Q_i).

The horizontal part of π0*R is effective because the left side is effective at unbounded exponents. For each base prime G define

    M_Y(G) = min_{F→G} coeff_F(π0*R) / mult_F(f0*G).

There is a fixed effective rational divisor J on Y, of finite support, with

    M_Y + Q_i + J/(m_i−m_1) ≥ 0.

Indeed one may take J(G)=max_{F→G} coeff_F(π0*N_1)/mult_F(f0*G), enlarging by zero when necessary. The inequality follows coefficient by coefficient from the displayed actual identity. Since Q_i is rational principal, the numerical classes of these effective divisors converge to [M_Y]. Hence M_Y is pseudoeffective.

This is Controlled conversion.tex's fixed-error/vertical-minimum argument. It supplies pseudoeffectivity directly; no metric on M_Y, no nefness theorem for M_Y, and no limit of high moments are required. Clearing denominators also gives the familiar regular section with

    rπ*P = f*V + H,   V=rM_Y,   H≥0,

and an H-zero component above each base prime. If Y is a point the horizontal calculation already yields a section. If the base has full dimension, domination makes P big and the positive-multiple conclusion is already paid. The nontrivial discussion is 0<dimY<dimW.

## 4. The rounded zero adjoint gives the needed donor metric

On the selected log resolution put

    R_discr = K_S − π*(K_W+D),
    E = ceil(R_discr),     Ξ = ceil(R_discr)−R_discr.

Because D is effective and the pair is klt, E is effective integral and π-exceptional; Ξ is effective SNC with coefficients in [0,1). The exact adjoint identity is

    K_S + π*P + Ξ = E.

The source maximality argument gives rank f_*O_S(E)=1, including exponent zero. A second generic section, extended after a base twist, would give a pencil nonconstant on the general fiber and contradict maximality. This is not merely a claim of rank one at positive exponents.

Domination gives a semipositive metric ψ on π*P with curvature at least d^(−1)f*ω_A. Let φ be the pulled-back zero-Lelong metric weight. Choose a sufficiently small τ>0 and put

    Φ = (1−τ)φ + τψ + φ_Ξ

on the INTEGRAL line B0=π*P+Ξ=E−K_S.

Here is the required all-point integrability calculation. Choose p>1 with p c_j<1 for every coefficient c_j of Ξ. Choose q,r>1 with 1/p+1/q+1/r=1. The factors exp(−pφ_Ξ) and exp(−q(1−τ)φ) are integrable, respectively by the SNC coefficient margin and all-power integrability. For sufficiently small τ, exp(−rτψ) is integrable by Skoda. Hölder proves exp(−Φ) integrable. A finite covering of S gives one τ. Therefore

    I(Φ)=O_S,   Θ_Φ ≥ (τ/d) f*ω_A.

This is the bounded source's small-mixture lemma with its bounded-factor shortcut replaced by the already-read Skoda/Hölder operation. It is not a new singularity theorem. It needs neither a common base-change open for all exponents nor integrability on every special fiber.

Let (f_*O_S(E))**=O_Y(C), where the canonical section of E gives C≥0 integral. At a base prime G with C(G)>0, division of that section by a local equation of G is permitted in the rank-one sheaf at its generic point. Consequently every prime F dominating G has positive coefficient in E, and hence is π-exceptional. Components over higher base codimension are also π-exceptional by the intermediate model. Thus EVERY component of f*C is π-exceptional, not just the component achieving a minimum. This is Controlled's actual hull/support argument, with Bounded's rounded E; it does not use E=K_{S/W} or smoothness of W.

Apply PT Theorem3.3.5 to B0 with Φ. Since I(Φ)=O_S on the total space, the natural multiplier-ideal direct-image inclusion is an equality; this is stronger than the theorem's generic-isomorphism premise. On the rank-one hull the resulting line is

    (f_*(K_{S/Y}+B0))** = −K_Y+C.

Subtracting the local potential (τ/d)f*ω_A before applying positivity shows that the descended metric g has curvature at least (τ/d)ω_A. PT extends it across base divisors, and psh extension handles codimension two. Positivity is obtained on this actual rank-one direct image, not by treating an arbitrary subline as positively curved.

Its distinguished section has finite norm: multiply a local base canonical frame into the adjoint section and use the ordinary total-space norm of the holomorphic section s_E of K_S+B0. The ideal I(Φ)=O_S gives its integrability. Properness and Fubini give finite local mass after pushforward, so

    |s_C|²_g ∈ L1_loc(Y),   equivalently I(g) ⊇ O_Y(−C).

Unweighted frame integrability and boundedness of g are NOT asserted. The source Controlled theorem needs exactly this weighted inclusion.

## 5. The strongest source already supplies the endgame

Controlled's theorem now applies to the pseudoeffective rational divisor M_Y. Its actual proof was read: Nadel and very ample regularity generate multiplier-ideal systems; weighted point extension bounds the fixed divisor; subtracting the boundary and Jacobian produces a signed divisor with all coefficients strictly below one; a reserved ample class absorbs a small rational multiple of M_Y; the resulting effective big klt boundary satisfies the BCHM nonvanishing interface; finite rational linear inequalities recover rational linear equivalence. The negative part pushes forward only on C.

The output is

    M_Y + C0 ~_Q G ≥ 0,   C0 ≥0,   Supp(C0) ⊂ Supp(C).

Pull back the rational principal correction G−M_Y−C0 and add it to π*R. Horizontal coefficients are nonnegative. At a divisor over a base prime outside Supp(C0), vertical minima and G≥0 give nonnegative coefficients. Any remaining negative coefficients occur in π-exceptional divisors, either above C0 or above base codimension at least two. Birational pushforward to normal W is therefore effective and rationally linearly equivalent to P. Clearing denominators supplies a section of a positive Cartier multiple of the specified P.

This comparison closes the apparent zero-Lelong route through source constructions and the classical analytic interfaces. It does NOT require the unfinished stronger finite-exponent nefness argument below. It also shows why a failed bounded-metric limit cannot legitimately be reported as the missing nonvanishing operation.

## 6. What happened to the initial finite-exponent route

Before reading Controlled's full conversion proof I considered F_a=f_*O(E+aH). Rank one and an H-zero component over each base prime bound its allowed base poles by a fixed divisor B, independent of a. Thus one can compare the positive finite-level metrics to lines aV+B−K_Y. This already suggests pseudoeffectivity of V after division by a; the algebraic affine-minimum argument in §3 is simpler and avoids these analytic extension details.

A stronger calculation would use weighted Fubini integrability to bound all Lelong numbers of the finite-level metrics independently of a, take a fixed root, then combine Nadel and Castelnuovo–Mumford to make mV plus a fixed ample correction globally generated. That would prove V nef and would make the Fujino/Euler ending available with smooth almost-positive base metrics separately at every twist. It is not needed for §5 and was not completed as a standalone all-point metric statement. Its incomplete multiplier-order/regularity details are retained as feasibility work, not nominated as a new theorem or represented as an unpaid condition for the actual nonvanishing composition.

For the naive limit, one local diagnostic is φ(z)=−sqrt(−log|z|) for 0<|z|<e^(−1), extended by −∞ at zero. It is subharmonic (the radial function of log|z| is increasing and convex) and has Lelong number zero. Every exp(−aφ) is locally integrable, while exp(−φ) has infinite essential supremum. On a disk with finite volume measure, the normalized L^a norms tend to infinity. This only diagnoses the infinite-moment inference. It is not an anticanonical counterexample, a compact-fiber model with the full source hypotheses, or an impossibility theorem.

## 7. Outcome, unpaid work and immutable older scopes

No substantial author-proof nominee was found and no theorem was frozen. The putative strengthening examined here is accounted for by the explicit source/classical composition above. Merely replacing bounded weights by all-power integrable weights, while carrying the already-existing controlled-boundary proof through discrepancy rounding, has not isolated a further nonroutine operation to submit. This is the author's decision not to nominate, not an independent TECHNICAL/SUBSTANTIAL verdict or a worldwide-priority assertion.

There is no newly claimed unpaid nonvanishing bridge inside §§2–5. In particular neither L∞ noncollapse, a nef metric on V, a uniform family of multiplier ideals at all twists, exceptional correction support, nor weighted effectivity-to-section return is left unpaid there. The unused stronger finite-exponent nefness mechanism remains only a partial calculation.

Starting with mere nefness would additionally require a way to obtain the all-power integrable positive metric (or another mechanism replacing its cohomological and mixture roles). This round neither constructs that metric nor asserts that it is impossible; that broader question was not frozen, developed as a replacement theorem, or nominated. Likewise no Euler-free singular statement, equivariant singular statement, lc-boundary replacement, finite-degree complement, exact all-valuation endgame or zero-CM/general-section result is nominated.

Original r6 reading.md, a completed authored receipt, confirms its exact-orders/controlled-cone direction, but its actual checkpoint body was excluded by the explicit checkpoint-alias rule. It remains uncleared; no inference from summaries substitutes for reading its scope. The arithmetic r121 originals were read solely as the required completed exceptions and their proper-curve support question was left unchanged. All supplied older scopes, including T360S147, H138/T185R144, H73, QSF, relative CI/infinite Tor, I226/I205, T025O54, G4, effective Kurosh, all-prime LPP, coprime-square, SHGH/W136 and Frankl, remain immutable. Parent alone integrates, reviews and counts.
