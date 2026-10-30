# I345 contribution review, round 1

2026-10-14. Independent contribution and novelty review of the unrestricted p-uniform gradient theorem. This is not a proof acceptance, not a count increment, and not a worldwide-priority certificate. The conditional proof PASS in `campaigns/2026-10-14/p-gradient-proof/review.md` is not used as a novelty finding.

## Verdict

**SUBSTANTIAL.**

The statement (T) below is a single frontier theorem. It is not identified with any primary theorem read here, and no standard reduction assembled from those theorems preserves every p at least 3, every dimension n at least 2, critical points, and one exponent and one constant independent of p. The new content is the bridge in the section "Unpaid bridge". Kotschwar–Ni, Uhlenbeck and the other fixed-p theories, Savin, the pinned infinity estimate, the source cylinder geometry, I236, Peng–Zhang–Zhou, Bungert, Lee–Lee, and Sobral–Teixeira–Urbano stay antecedents or neighboring theorems.

Acceptance still waits on the proof gate's documentation repairs R1–R7 and on parent integration. This file does not accept the candidate. The large-p inhomogeneous transfer is one corollary of (T) and is not a second result. MathDB 405360 remains unsolved.

## Statement under review

Primary text: `frontier/experiments/i345_lifted_p_gradient_research/analysis.md`, SHA-256 `f88c4ad3f983eb405912679864c7b8d5e64e933eb486f6cf1c49a8e9deabaa25`, Section 1. The same statement is in `frontier/iterations/i345-lifted-p-gradient-research.md`.

For each integer n at least 2 there exist α_n in (0, 1/3] and a finite C_n such that every finite p at least 3 and every bounded weak solution u in W^{1,p}_loc(B_1) of

    ∫ |Du|^{p-2} Du · Dφ = 0

has its continuous representative in C^{1, α_n}(B_{1/2}) and

    ||Du||_∞(B_{1/2}) + [Du]_{α_n; B_{1/2}} ≤ C_n osc_{B_1} u.          (T)

No sign, critical-point, level-set, gradient-modulus, or boundary hypothesis is imposed. The exponent is nonexplicit. The range is exactly p at least 3. Pinned infinity-harmonic inputs are stipulated at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` and are not re-audited.

## What a technical reduction had to preserve

A technical verdict would require an explicit deduction of (T) from older theorems such that all of the following survive:

- every finite p at least 3, with one α_n and one C_n;
- every dimension n at least 2, including critical points of Du;
- a quantitative Hölder bound, not merely convergence of one sequence of gradients.

Each route below drops at least one of these. The closest machines are recorded first.

### 1. Sobral–Teixeira–Urbano, run jointly in p

Sobral–Teixeira–Urbano, arXiv:2610.13137v1 (9 October 2026), Theorem 1.1, states: if every p-harmonic function on every ball is locally C^{1, γ}, then for every β in (0, γ) there is C = C(n, p, γ, β) such that

    ||Du||_∞(B_{1/2}) + [Du]_{β; B_{1/2}} ≤ C ||u||_∞(B_{3/4}).

The constant depends on p. Corollary 1.2 in the plane likewise has C = C(p, β) for each β below the Iwaniec–Manfredi exponent. Section 2.2 obtains compactness from the Pucci class with ellipticity constants 1 and p−1, hence a Krylov–Safonov exponent σ(n, p). Lemma 2.2's second alternative, |q| → ∞ at fixed p, is the smooth linear equation with matrix I + (p−2) e ⊗ e.

That theorem does not yield (T). A joint family over all p at least 3 fails at three places.

- The hypothesis γ is per equation. Classical interior theory supplies some α(n, p) > 0. Peng–Zhang–Zhou, arXiv:2310.08093v4, pages 4–5 of the local extract, record that those C^{1, α} theorems depend on the value of p and are not uniform for all large p. Theorem 1.1 does not create a common γ.
- The compact set and the finite flatness cover in their Lemma 2.3 depend on p through the ellipticity ratio p−1. Kotschwar–Ni does give a Lipschitz bound uniform for p at least 3, so value equicontinuity can be restored, but the flatness radii still come from a p-dependent cover.
- The double limit p → ∞ and |shift| → ∞ is outside Lemma 2.2. The matrix I + (p−2) e ⊗ e has ellipticity ratio tending to infinity, so the limit is not that smooth linear equation. The formal limit is a directional degeneracy. Savin's small-perturbation theorem needs a fixed ellipticity ratio and does not apply to that un-rescaled limit.

In the plane the qualitative half is older and still insufficient. Iwaniec–Manfredi give the sharp exponent

    α_IM(p) = (1/6) ( p/(p−1) + √(1 + 14/(p−1) + 1/(p−1)^2) ),

which decreases to 1/3 and is strictly above 1/3 for every finite p. Every planar p-harmonic function is therefore locally of class C^{1, 1/3}. The quantitative Baernstein–Kovalev / Araújo–Teixeira–Urbano exponent quoted by Sobral–Teixeira–Urbano and by Lee–Lee tends to 0 as p → ∞ (about 0.574 at p = 3, about 0.014 at p = 100). Sobral–Teixeira–Urbano convert the qualitative Iwaniec–Manfredi theorem into a bound whose constant still depends on p. They do not claim, and their shifted compactness does not give, a constant independent of p.

### 2. Value compactness plus the pinned infinity estimate

Pinned `thm:main` gives, for each d at least 3, α_d in (0, 1/3] and C_d with the same shape of estimate for bounded infinity-harmonic functions. `lem:linear-lift` preserves the infinity equation under U(y, b) = u(y) + b.

If p_j → ∞ and the values of normalized p_j-harmonic functions converge uniformly, the limit is infinity-harmonic, and `thm:main` controls the limit gradient after the dimension-(n+1) lift. Uniform convergence of values does not control [Du_p]_α. The finite-difference bound in analysis Section 10,

    ||Du_p − Dv|| ≤ C ||u_p − v||^{α/(1+α)},

uses the uniform Taylor remainder already proved for the approximants. It cannot be quoted to prove that remainder.

The same obstruction blocks a "qualitative flatness implies a power" shortcut. Analysis Section 2.3 does prove a common o(r) Euclidean modulus, using Kotschwar–Ni, Uhlenbeck on bounded p, and the pinned theorem on the infinity blow-up. An o(r) modulus is the input to cylinder selection. It is not a Hölder gradient bound. The infinity manuscript's own introduction, lines 136–138, makes the same distinction for the infinity equation: compactness of solutions alone does not give a common rate for their derivatives.

### 3. The infinity manuscript, copied verbatim

The pinned proof adjoins a linear coordinate because that operation preserves the infinity equation, then uses a three-point estimate to produce uniform small-scale flatness, then runs cylinder selection and a Liouville theorem for F[v] = D²v[(∇_x v, 1)] = 0. The manuscript contains no p-Laplace theorem. A search of its section files finds no p-harmonic argument.

For a finite p the same adjunction does not preserve p-harmonicity. Analysis Section 3 derives the different equation

    L(DU, H) = H[DU] + ε |Π DU|^2 tr(Π H) = 0,    ε = 1/(p−2).

The three-point estimate is not applied to L. After cylinder blow-up the effective viscosity ν = ε A / λ may stay finite or tend to infinity. The source Liouville theorem covers only the equation with ν = 0. Copying the infinity proof therefore loses the finite-viscosity branch and the infinite-viscosity branch, which are exactly the branches that carry original critical and near-critical slopes.

### 4. Savin applied to the normalized p-Laplace

Savin, CPDE 32 (2007), Theorem 1.3, gives interior C^{2, α} control for sufficiently small solutions of an elliptic equation that is uniformly elliptic and C² near the zero jet. The normalized p-Laplace has ellipticity ratio p−1. The smallness threshold and the estimate depend on that ratio. They are not uniform as p → ∞, so the theorem does not by itself give (T). The use of Savin inside I345 is on a different, lifted and rescaled family whose ellipticity stays bounded at every endpoint, including ε = 0. That family is part of the bridge, not a quotation of Theorem 1.3 on the original operator.

### 5. Peng–Zhang–Zhou

Local extract `frontier/sources/i230_p_harmonic_gradient/peng-zhang-zhou-pages-1-8.txt`, from arXiv:2310.08093v4. The introduction on its pages 4–5 states the natural idea of C¹ estimates for p-harmonic functions uniform in all large p, records that the known C^{1, α} theory depends on p, and poses Question 1.1A for potentials with the same Dirichlet data: whether u_p converges to u in C¹(Ω).

Theorem 1.1 answers that question for a convex ring Ω = Ω_0 \ Ω_1: the infinity-harmonic potential is C¹ with nonvanishing gradient, and the p-potentials converge to it in C¹(Ω). Lewis's structure theory, cited there as Lemma 3.1, gives smoothness, nonvanishing, and quasiconcave superlevel sets for those potentials. The theorem is local uniform convergence of one sequence of gradients. It does not give a Hölder exponent, a constant independent of the potential, or an estimate for an arbitrary bounded weak solution. A solution with an interior critical point is outside the theorem. The published PLMS abstract (2025, e70062) identifies the same convex-ring C¹ approximation theorem. The published PDF was not opened.

I230's quasiconcave rate is the project's quantitative refinement of this normal-and-slope information. The parent disposition `i230-p-gradient-parent-disposition.md` already keeps it technical and leaves the unrestricted target open. Using (T) to revisit convex rings does not create a new theorem beyond Peng–Zhang–Zhou plus a finite-difference consequence.

### 6. I241's selected high-viscosity estimate

`i241-p-gradient-parent-disposition.md`: a cylinder estimate from Savin closes one branch after a nonzero bounded base slope, uniform qualitative flatness, and a larger available cylinder have been granted. I241 does not produce those hypotheses for arbitrary approximants. I345 pays the missing flatness, the critical-safe lift, the projection onto finite viscosity, and the unequal-parameter transfer onto the Savin scale. Quoting I241 does not yield (T).

### 7. Bungert's value rates

Bungert, arXiv:2302.08462v2, Theorem 1: if u_p and u_∞ solve Dirichlet problems and limsup [u_p]_{C^{0, α_p}} = H is finite for some α_p in [1 − d/p, 1], then the values converge at a rate of order ((d−1)/(p−1))^{α_p/(2α_p+2)}. A positive essential infimum of |Du_∞| improves the exponent. The conclusion is a value norm. Remarks 2.4–2.5, as read through the arXiv HTML and the project's earlier extract, tie H to boundary extensions. An interior gradient Hölder bound for every weak solution is not a hypothesis this theorem supplies, and the theorem does not conclude one.

Once (T) is known, Bungert's value rate plus a finite-difference inequality gives an interior gradient rate for those Dirichlet solutions. Analysis Section 10 already records the analogous consequence for value-convergent sequences. Either form is one corollary.

### 8. Fixed-p theory, compact intervals, and Lee–Lee near 2

Uhlenbeck, Acta Math. 138 (1977), as used in analysis Section 2.2, and the DiBenedetto–Tolksdorf–Lieberman theory give, on each compact p-interval [3, P], some θ(n, P) > 0 and a constant depending on P. The constant and the exponent may change with P. This is the bounded-p branch of the argument. It is not (T).

Lee–Lee, arXiv:2609.09966v1, Theorem 1.3: for each c in (0, 1/2) there is ε_{d,c} > 0 such that if p is in (2, 2+ε_{d,c}), then p-harmonic functions satisfy a C^{1, β} estimate with

    β = 1/(p−1) + c(p−2)

and a constant depending on d, p, and c. Theorem 1.2 is the inhomogeneous conjecture in that same neighborhood of 2. Both statements leave all sufficiently large p untouched.

## Unpaid bridge

The following steps are the part of the argument that the sources above do not contain. They are one bridge, and they are the content to which this substantiality verdict attaches.

1. **Critical-safe constrained lift.** For U(y, b) = u(y) + b and ε = 1/(p−2), every viscosity test of an actual weak p-solution, including a test with vanishing original gradient, satisfies L(DU, H) = 0. The Schur reduction in analysis Section 3 covers H_bb = 0 and g = 0. The lift is not p-harmonic. On rescaled tests the coefficient C_i is nonnegative because of the exact constraint q · ξ = 1/c. Replacing C_i by max(C_i, 0), and later B by max(B, 0), produces a globally degenerate-elliptic operator that agrees with L on every real upper or lower test, so viscosity stability applies off the constraint. One quadratic contact then gives A_i ≥ −C λ_i, hence liminf ν_i ≥ 0, without a pointwise gradient bound.

2. **Exact projection onto a fitted isotropic equation.** If the effective viscosity ν stays finite, the limit is F_{ν, a}. When a ≠ 0 the transport identity makes V linear along a, both the rank-one term and the trace reduce to G_ν on the orthogonal variables, and the sheared fits project with the same C_0. The source Liouville theorem (ν = 0) and I236 (ν > 0) then give affinity. Original near-critical slopes are this finite-ν branch. I236 itself remains the technical finite-τ theorem already judged in I240: for each fixed τ in (0, ∞), FIT plus G_τ forces affinity. I345 does not make I236 a new substantial theorem. The new step is the projection that puts every finite-ν blow-up, including a ≠ 0, inside that hypothesis.

3. **One Savin family for every large-p and small-flatness endpoint.** When ν → ∞ the argument renormalizes by e = ε A ≤ 1 on an ellipsoid adapted to the coarse cylinder. The operators F_{ε, A, e, ξ, d}, including the amplitude d in [0, 1] and the endpoints ε, A, e, d equal to 0, are linear in the Hessian, vanish at the zero jet, and are uniformly elliptic on a common ball |q| ≤ 1/8, with the zero-jet form bounded by (b_0²/3)|·|² ≤ Q ≤ 2|·|² as in the parent ellipticity note. Savin's Proposition 4.1, read through the existing pages 14–18 extraction and the proof review, varies the operator under a common C² bound and produces one smallness threshold. The amplitude rescaling Z = W/d turns that absolute threshold into ||D²W|| ≤ C ||W||, hence the cylinder error C e r²/H in (7.6). Neither the family nor the proportional Hessian bound is in Savin's statement for a single operator, and neither is the unlifted cylinder estimate of I241.

4. **Unequal-parameter norm transfer onto that cylinder.** The source `lem:cylinder-comparison` compares slopes at one fitting parameter. The Savin scale is H = ν² r with coarse parameter η = κ λ and κ = 64 (4ν²)^γ. The first comparison, from a Λλ-fit to an η-fit, is not an instance of that lemma. The common-axis argument gives ||P| − |Q|| ≤ C κ² λ, and the later equal-η chain adds O(η(1+log ν)). Relative to A = ν λ / ε the error tends to 0, so the coarse slope keeps A' comparable to A and e' comparable to ν λ. A vector error O(κ √λ) does not. This comparison is what lets (7.6) contradict the selected bad scale.

After these four steps, the source running-maximum and the source gradient extraction are equation-free and give α = γ/(2+γ) ≤ 1/3. Those two source blocks are reused geometry. They are not a second discovery.

## What this verdict does not award

- The uniform Lipschitz bound is Kotschwar–Ni, Theorem 1.1, on the positive function u − inf u + osc u, for p at least 3 and zero curvature.
- Compact-p C^{1, θ} and fixed-p entire affinity are Uhlenbeck (5.4) and (6.1), or any equivalent primary source with constants uniform on p in [3, P].
- The infinity estimate, the infinity linear lift, bad-scale selection, equal-parameter cylinder comparison, geometric compactness, and Campanato extraction are the pinned manuscript.
- Finite positive τ affinity under FIT is I236, technical by I240.
- Savin's small-perturbation theorem is Savin's.
- C¹ convergence of convex-ring potentials is Peng–Zhang–Zhou, Theorem 1.1.
- Planar qualitative sharpness up to α_IM(p), and p-dependent quantitative bounds below that exponent, are Iwaniec–Manfredi and Sobral–Teixeira–Urbano.
- Improved homogeneous exponents for p sufficiently close to 2 are Lee–Lee, Theorem 1.3.
- Value rates under a value-Hölder hypothesis are Bungert, Theorem 1.
- The gradient rate for a value-convergent sequence in analysis Section 10 is a finite-difference corollary of (T).

## MathDB 405360 and submission scope

Retrieved in this review from the MathDB remix payload for <https://mathdb.com/p/405360/the-c-p-regularity-conjecture> (HTTP date 2026-10-15T02:25Z, release `a8cde5143b42b7c8bf86c60cd3de5fcbd3803c13`; edited_at 2026-10-13). The statement is:

For every dimension n at least 2 and every p > 2, if u in W^{1,p}_loc(Ω) is a weak solution of −div(|∇u|^{p−2} ∇u) = f with f locally bounded, then u is locally C^{1, 1/(p−1)}.

The page classifies the problem as a named conjecture, status `claimed_progress`, with no posted solution. Its progress summary records the planar case and a near-2 partial result, and it leaves the full conjecture open. The homogeneous estimate (T) is not this problem.

Lee–Lee, Theorem A, quoted from Araújo–Teixeira–Urbano, IMRN 2018, Theorem 2: if every bounded p-harmonic function on B_1 obeys a C^{1, α_0} estimate for some α_0 in (1/(p−1), 1), with constant C_0, then bounded-forcing solutions are locally C^{1, 1/(p−1)}, with a constant depending only on d, p, α_0, and C_0. The publisher PDF of that 2018 article was not opened. The quotation in Lee–Lee is the interface used here.

If (T) is proved, fix α_n and any P_n > max(3, 1 + 1/α_n). Since α_n ≤ 1/3, one has 1 + 1/α_n ≥ 4, so the threshold is at least 4. For each fixed p ≥ P_n the inequality α_n > 1/(p−1) pays Theorem A. Bounded-forcing solutions then have the sharp local exponent 1/(p−1) in that range. The constant from Theorem A depends on p. This is one conditional corollary. It is not a second acceptance, and it leaves MathDB 405360 open on 2 < p < P_n, including the whole interval where Lee–Lee's ε_d stops and P_n has not started.

A MathDB submission of (T) as a solution of problem 405360 would misstate the problem. The matching public claim is the homogeneous theorem (T), with the large-p inhomogeneous statement labelled as a partial corollary and with the p-dependent constant left visible. No submission is made here.

## Relation to the proof gate

The proof review's verdict is conditional PASS, with the unequal-parameter repair accepted and with R1–R7 required before a manuscript. Those repairs are provenance and self-containedness: a compact-p citation with uniform constants, an explicit Savin family-uniform lemma, a full citation or inclusion of I236, a stated selection lemma, a quantified small-solution lemma, hash binding, and the restriction p at least 3. They do not change the literature comparison in this file.

This review did not re-decide U1–U4. If the compact-p interface, Savin's pages 5–13, the weak/viscosity equivalence, or the I239 audit failed to support the interfaces the argument cites, then (T) would not be established. Substantiality applies to the proved statement. It does not fill a proof gap.

## Limits

No worldwide priority is claimed. The searches were bounded: the papers named by the parent, the October 2026 qualitative-to-quantitative paper, the pinned infinity manuscript, the local Peng–Zhang–Zhou extracts, and targeted queries for a p-uniform interior gradient Hölder theorem. Absence from that search is not a proof that no other paper exists. Details and unread ranges are in `sources.md`.
