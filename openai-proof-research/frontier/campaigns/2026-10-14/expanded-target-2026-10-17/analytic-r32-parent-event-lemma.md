# Author-side event conditioning calculation for family 263

Status: parent derivation, 2026-10-17. This is assistance to the active r32 author, not an independent review or a complete candidate. No accepted-count change.

Let q be the sector Schrödinger form, with kinetic coefficient c>0 and lower spectral bound E_n. Let ψ be a normalized form-domain vector with q[ψ]≤E_n+δ. Use the source observation law and an event A of probability p>0. Write a(x)=P(A|x). The source score-gradient calculation, which does not use the eigenstate assumption, applies to both A and its complement:

    |∇a| ≤ C ℓ^(-1) a log^(5/2)(e/a),
    |∇a| ≤ C ℓ^(-1) (1−a) log^(5/2)(e/(1−a)).

The source square-root regularization argument shows that f=√a and g=√(1−a) are bounded Lipschitz multipliers preserving the sector form domain and fermionic antisymmetry. Their gradients vanish almost everywhere on their respective zero sets. Since f²+g²=1, the form IMS identity gives

    q[fψ]+q[gψ] = q[ψ]+c∫(|∇f|²+|∇g|²)|ψ|².

For 0<a≤1/2, the gradient integrand equals |∇a|²/(4a(1−a)) and is at most Cℓ^(-2)a log^5(e/a). For 1/2≤a<1, use the complementary score bound: the integrand is at most Cℓ^(-2)(1−a)log^5(e/(1−a)), hence at most Cℓ^(-2), and therefore at most C'ℓ^(-2)a log^5(e/a). The same inequality holds almost everywhere on the endpoint level sets.

Under the raw law conditioned on A,

    P(a<exp(−u) | A) ≤ min(1, exp(−u)/p).

Integrating this tail yields E[a log^5(e/a)]≤Cp log^5(e/p). This uses the source tail argument rather than an unjustified global concavity claim. Consequently the full IMS error is at most Cℓ^(-2)p log^5(e/p).

Since ||gψ||²=1−p, lower bounding its form energy by E_n(1−p) gives

    q[fψ/√p]−E_n ≤ δ/p+Cℓ^(-2)log^5(e/p).

For p=1 the same conclusion follows directly (a=1 almost surely under the raw law and the integrated error vanishes). The localized raw law is exactly the law conditioned on A. Thus the eigenstate event estimate extends with an additional δ/p loss, while the localization cost retains logarithmic probability dependence. This does not by itself prove the proposed asymptotic density or radius theorem.

## Source reading and remaining contracts

The parent read the pinned foundation manuscript `Uniform-excess-charge-for-Coulomb-molecules-and-the-outer-radius-of-neutral-atoms-September-24-2026`, retained in r32/private/263: `15-interfaces.tex` in full; `04-screening.tex` lines 675–790; and `05-observations.tex` lines 115–455. Source truths are stipulated; this is not an upstream audit.

`a:prop:screen-local` explicitly applies to every normalized finite-sector δ-state and permits the absent-cut case, with constants independent of state, charge, particle count and offset. Here δ is measured above the source global E. Applying it to a neutral near-ground state requires adding the source bounded neutral-sector offset E_Z−E to the excess above E_Z.

The fine comparison `a:cor:screen-refined` has the stronger restriction δ≤a^(-7+.02). An arbitrary slowly vanishing δa^7 does not imply that restriction. The candidate must derive an adaptive version from the underlying comparison inequalities, rather than invoke the fixed-power corollary. The observation transfer lemma is conditional on its four explicit patch hypotheses; the candidate must establish each for its adaptive parameters. “No symmetry” in a prospective scope must distinguish absence of spatial symmetry from the fermionic antisymmetry required by these source Hamiltonians.

The agent reports an adaptive-width route with bad-band exponent .9885>6/7; the parent has not yet read a complete argument or accepted that estimate. The argument above was sent to the author agent before being recorded here.

## Tunable source-free patch calculation

The parent additionally read `04-screening.tex` lines 1–116 and 300–395, and `10-atomic-comparison.tex` lines 75–245. In atomic distance geometry, write η=δ_tilt a^7≤1 and assume 0<a<1. Then m=a^(-3)+√(δ_tilt a)≤2a^(-3), and the source gives P≤C. Its sharper source-free patch bound implies

    a^7 E[D(σ−ρ)+L+∫W_-σ]
       ≤ C[η+√β+β^(-1)a^3+β^(-2)(a+a²)].

This is obtained by substituting b=βa into `a:eq:screen-patch`: respectively b^(-1)m has normalized size β^(-1)a^3, b^(-2)m^(4/3) has size β^(-2)a, and b^(-2)m has size β^(-2)a². The condition β≥a^.2 makes the source patch admissibility inequality hold, since β^(-2)/(am)≤a^.6≤1≤√P. It also bounds the latter error terms by quantities tending to zero. Taking β=max(a^.2,η^b), with any fixed b>0, keeps the patch error vanishing even for arbitrarily slow η→0; eventually β<1/100 as required.

The out kinetic bound is at most C a^(-7)[1+β^(-2)a²], hence O(a^(-7)). Since the cut is full out on B(y,4a), the source local kinetic inequality gives the requisite uniform raw L^(5/3) density estimate there. The transfer lemma's Coulomb term is the square root of the displayed normalized error multiplied by τ^(-1/2). Thus choosing parameters requires that normalized error be o(τ), in addition to the other transfer hypotheses. This elementary adaptive patch calculation is an application of the source estimates, not a stand-alone substantial result. The complete probability, spatial-net, multiscale barrier and initialization argument remains to be checked.
