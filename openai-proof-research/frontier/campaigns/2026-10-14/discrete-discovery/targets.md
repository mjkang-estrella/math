# Discrete/algebraic discovery — target screen, 2026-10-14

Research output only. **No substantial result is nominated or counted.** The selected arithmetic frontier is still unpaid. The complete supporting theorem in `candidate.md` has an author-level proof and exact finite checks, but no independent proof or contribution verdict. Worldwide novelty is unestablished.

The immutable input is OpenAI/math `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Read: project AGENTS, campaign brief, both acceptance tables and relevant ledger dispositions, upstream JSON, catalogue; then the actual theorem introductions listed in `upstream/manifest.json`. Sixteen prior acceptances R006–R022 are not recounted. Particularly relevant prior dispositions: I19/I77's weighted-switch obstructions, I248/I258 and I267/I268 rooted-packing technical disposition as summarized in TWENTY-FINDINGS, and I337/I338's bounded-corank HSP reduction. No hidden-subspace, amplification-hierarchy, rooted-packing, factor-count-residue, or coefficient-extraction variant is offered here.

## D1 — selected: exclude the boundary of the five-sign correlation polytope

**Arithmetic target.** For every ε in {−1,+1}^5,

`liminf_{X→∞} X^(-1) #{1≤n≤X : λ(n+j)=ε_(j+1), 0≤j≤4} > 0`.

This is a positivity theorem, not the predicted exact density 1/32 and not all orders of Chowla. The actual MathDB [Chowla sign-pattern record](https://mathdb.com/p/371795/chowla-s-sign-pattern-conjecture-for-consecutive-liouville-v) asks for equidistribution of all finite consecutive patterns. D1 would be only a length-five positivity advance toward that record.

**Why source 007 is insufficient.** Its `thm:q-affine` gives ordinary binary Liouville cancellation with a common positive logarithmic-saving exponent for each fixed nonproportional pair of affine forms. It does not assert vanishing odd ordinary correlations or any five-pattern density. The sole manuscript in catalogue family 007 has no separate companion claiming D1; the inspected introduction and affine-corollary statements do not supply it.

**Primary comparison.** Tao–Teräväinen (2019), Theorem 1.14, proves at least 24 length-five patterns have positive upper density, and twelve explicitly listed patterns have positive lower density. Section 7, equation (7.4), describes the three-parameter Fourier polytope. Lemmas 7.2–7.3 give the adjacent-block and gapped-four-correlation bounds. These are credited, not new findings. Sawin (2018), Definition 1.1 and Theorems 1.5–1.6/3.1–3.2, explains why Fourier uniformity and Liouville-like dilation axioms can have long-pattern obstructions; his stated d=1 arbitrary-pattern example concerns length 29, not a counterexample to D1.

**New bridge required.** Show that actual Liouville logarithmic window laws stay a positive distance from every zero-probability facet of the Section 7 polytope, using multiplicativity beyond the two-point and odd-symmetry constraints. The explicit 24-word process in `candidate.md` lies on a facet while satisfying stationarity, all pair correlations zero, every odd correlation zero, and reflection symmetry. Thus simply substituting ordinary binary Chowla in the old Fourier expansion cannot pay the bridge.

**Status.** Open in this research. No proof or counterexample to D1. An exploratory finite-dimensional relaxation incorporating a necessary factor-two dilation domination remains numerically feasible through words of length 19. This is not an infinite multiplicative model, an exact feasibility certificate, or a disproof of D1.

## D2 — sharp structural supporting theorem, completed but not nominated

For each integer r≥2, the exact supremum of

`|E X_0 X_1 X_r X_(r+1)|`

over strictly stationary, unbiased, pairwise-independent {−1,+1}-processes on Z is `1−1/r`. Both signs are attained by processes whose every odd joint moment vanishes. This combines a cancellation identity with an explicit increment construction. It yields a sharp barrier to any position-independent four-correlation gap based on white two-point spectrum alone. It is not merely a change of codimension in R021, and it does not solve a named open MathDB problem.

The proof and a source-007 ordinary Liouville corollary are complete at author level in `candidate.md`. However, the upper-bound mechanism is the quantitative form of the old parity-product argument in Tao–Teräväinen Lemma 7.3; repeated hidden signs and fresh separator bits are standard probabilistic ingredients. The full sharpness statement deserves a bounded primary-literature check before even a novelty claim. **Author disposition: supporting obstruction / probably technical; no substantial nomination.** It is not another result slot separate from D1.

## D3 — restricted-host dynamics: naive extension is false

The tempting statement “the source-131 lazy four-edge switch chain mixes polynomially for all degree vectors on K_n minus an arbitrary matching” is false. An exact six-vertex example has forbidden edges `{01,23,45}` and degree vector `(3,1,3,1,3,1)`. It has exactly two realizations, each with no valid four-edge switch. The full edge lists and exhaustive verification are in `exact-results.json` and `exact_checks.py`.

A corrected, nonroutine target is polynomial mixing for all feasible degree vectors on K_n minus a matching **with both four- and six-edge alternating-cycle moves**, under a fixed lazy uniform local proposal convention. No proof is offered. Irreducibility and a quantitative comparison remain distinct obligations. Source 131 is for the complete host; the source's own introduction separately credits its perfect-matching companion for approximate counting/sampling on arbitrary unweighted hosts, and explicitly disclaims host-restricted switch-chain mixing. The near-complete-host alteration changes the move geometry and cannot be imported by conditioning a rare event.

Prior-primary comparisons: Greenhill–Sfragara (2018), introduction and directed discussion; Erdős et al. (2022), introduction and Section 6 on directed/bipartite forbidden-perfect-matching models. Those works already use or discuss three-edge moves in restricted models. This six-vertex obstruction is supporting research, not a novelty claim or a rejection of the corrected six-edge target. No precise matching MathDB problem page was established in the bounded search.
