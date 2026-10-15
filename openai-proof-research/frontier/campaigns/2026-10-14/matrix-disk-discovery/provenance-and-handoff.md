# Provenance, bounded comparison and handoff

The original assignment is the full arbitrary finite-dimensional attained matrix-polynomial question: can a nondisk W(A) admit M>0 and ||F[A]||=2M? The candidate in analysis.md proposes **impossibility in all finite dimensions**, with a complete analytical argument. It is unreviewed, is not accepted, and earns no new-result credit before the two independent gates. All writes are confined to this assigned directory. No agent was spawned, shared index changed, file staged or commit made.

## Actual mathematical dependencies and read extents

- [Pinned direct complete-Crouzeix manuscript](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/build/main.tex). Fresh whole-file retrieval retained as direct.tex. Read local source lines 160–460 (the entire exterior Faber theorem and proof, coefficient estimate and proof, original resolvent theorem and proof, analytic-domain theorem and proof, and outer-approximation statement). Labels used: lem:faber, prop:coefficients, lem:resolvent, thm:domain; eq:s, eq:coefficient-estimate, eq:kernel-fourier-action, eq:pairing, eq:ordered-products, eq:diagonal-functional, eq:weighted-dual, eq:diagonal-L2, eq:cross-L2. Its Markov kernel positivity and both unit marginals are actual source operations. The source's complete bound is stipulated true, not audited.
- [Pinned structural companion](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-complete-Crouzeix-theorem-September-23-2026/build/main.tex). Fresh whole-file retrieval retained as structural.tex. Read lines 92–147,316–375,831–966,977–1065: optimal metric and representation statements, similar-matrix density and proof, original versus similar bridge, ordered comparison and proof. It is used as a scope/provenance check, not as a replacement for the original field.
- [Jin, Rigidity at the Extremal Crouzeix Constant, v2](https://www.preprints.org/manuscript/202609.0079/v2). Read the actual web-rendered Lemma 8 and proof (displayed lines 451–470), Propositions 5 and 6 with full proofs (605–706), and Proposition 4 full-level regularity argument (556–595). Also read the same extents in the inherited attributed primary excerpt frontier/sources/i246_crouzeix_rigidity_contribution/jin-v2-sections1-8.txt; its hash is in inputs.json. The fresh raw urllib retrieval returned HTTP 403; **no fresh whole-HTML hash is claimed**. Web retrieval succeeded. The used external geometric theorem is Proposition 6; its tangent Hermitian determinant, degree difference, full level, noncriticality and strict-convexity hypotheses are all checked explicitly. Jin's scalar equality theorem is not applied to the complete witness.
- [ACV v3](https://arxiv.org/html/2608.27346v3). Opened actual versioned web page and read the attributed primary Section 11 excerpt in frontier/sources/i246_crouzeix_rigidity_contribution/acv-v3-s11.txt completely. Corollaries 11.4–11.5 transfer disk rigidity to the complete constant through dimension three. Proposition 11.1 and Theorem 11.2 classify scalar polynomial equality. These are comparison inputs, not steps that scalarize this candidate. The prior I292 full analysis was read for its detailed comparison of Section 5/7, realization and rational endpoint operations; that previous review is not presented as an independent review of the new candidate.
- Read AGENTS.md, sources/upstream.json, frontier/NEW-TEN-2026-10-14.md, R016, R019, complete I287 proof, complete I291/I292 review statements, complete I292 supporting analysis and I291 source index, and complete I245 analytic-check.md. Read the parent crouzeix-five/analysis.md. Their exact hashes appear in inputs.json. R016/I245 supplies only its dimension-independent exterior convergence and residual extraction, never its small-dimensional rank argument. R019 supplies a mutation/control example and is not recounted as a new result.

## Preliminary contribution screen, not the independent gate

The pinned direct manuscript already contains the convex Markov contraction and non-strict coefficient estimates. The proposed bridge retains its variance defect in the optimal diagonal dual test, forces all positive diagonal Faber moments to vanish by Fatou plus one curved arc, rationalizes the original cross channel, and extracts a fixed **determinant** polynomial whose rational inverse excludes all exterior level components. This permits Schmidt rank two and hence survives the accepted R019 obstruction. The inherited R016 argument instead forces rank one from a simple support eigenvalue and then applies scalar rigidity.

Jin's Proposition 6 supplies the final geometry and receives full credit. Constant modulus of a polynomial determinant on a convex oval alone is insufficient; the actual Hermitian tangent-detector hypothesis is paid using Re B and Im B. The proof does not promote a convex lemniscate to a disk by assertion. Its sublevel and full-level identities are stronger than boundary constant modulus and are proved using the rational exterior inverse.

Bounded web searches on 2026-10-14 included “matrix polynomial complete Crouzeix equality numerical range disk rigidity”, “complete Crouzeix disk rigidity”, “Crouzeix Jensen equality”, and “Crouzeix determinant rigidity”. They returned the credited Jin and ACV sources and general complete bounds, but no inspected primary statement already supplying this full bridge. Search absence is not evidence of priority. A separate primary-literature contribution review is required; no worldwide novelty conclusion is made here. Full original LSS was not sought, because it is only the already credited old R019 control matrix, not a dependency of the new theorem.

## Exact computation and scope

Run from repository root:

    python frontier/campaigns/2026-10-14/matrix-disk-discovery/check.py

The package-free Fraction-field checker works in Q(sqrt(2),sqrt(7),i). It passes 17 exact checks, including original R019 compressed resolvents, the constant-test factor 1/2, rational inverse, complex coefficient-basis changes, and deliberate adjoint-versus-transpose and missing-factor mutations. It finds the R019 determinant channel det F=-z^4. The separate two-point Markov calculation checks the variance normalization and detects a missing factor two. It does not prove the analytical outer limit, Fatou step, geometric criterion or full theorem.

No Lean theorem is claimed. The formalization coverage/plan in analysis.md is explicit; any eventual supporting algebra formalization must not be described as a full proof.

## Requested independent pressure points

1. Infinite optimal dual tests are used only after finite-polynomial inequalities and N->infinity at fixed j; verify the defect formula and its limit.
2. Triple-integral Fatou uses q_j,u_j a.e. subsequences, injectivity/uniform convergence of h_j, and positivity on the curved arc; verify the absence of a hidden uniform spectral gap assumption.
3. Check the exterior Hardy uniqueness and nonvanishing of the scalar trace r on and outside K.
4. Check the factor 1/2, entrywise conjugation, and **ordinary transpose** in the rational inverse Q=(1/2)S_E^-1 U*mathcal M^T V.
5. Check fixed coefficient ranges, equal ranks and rational identity JQ=I.
6. Check full lemniscate/noncriticality/strict convexity and the exact Jin Proposition 6 interface.
7. Check restoration from the active irreducible block to full W(A) by the determinant monomial.

No unpaid mathematical lemma is presently identified by the author. This is a claim about the completeness of the proposed argument, not a substitute for adversarial review. No manuscript or acceptance artifact should be prepared as an accepted result before those gates.
