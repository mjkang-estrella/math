# I331 — simultaneous strong approximation of a map and its inverse

Status: **blocked on the general target; validated partial results only.** No proposed accepted finding and no count change. Research performed 2026-10-13 under the repository AGENTS.md, with no delegation, git operations, publication, numerical scans, or shared-index edits.

The target remains: for every pair of bounded domains Ω,Λ⊂R³ and every homeomorphism f:Ω→Λ with f∈W¹,²(Ω) and h=f⁻¹∈W¹,²(Λ), find a **single sequence** of smooth onto diffeomorphisms g_j:Ω→Λ for which g_j→f and g_j⁻¹→h strongly in their respective global W¹,² spaces. No boundary regularity or lower Jacobian bound is assumed. Neither a proof nor a counterexample to this quantified assertion was obtained.

The parent’s rank-one obstruction is unavailable for these inputs: applying Csörnyei–Hencl–Malý, author-preprint Theorem 4.5, in both directions shows that Df=0 a.e. on {Jf=0}, and Dh=0 a.e. on {Jh=0}. This deduction uses the actual primary theorem, not planar criticality. Oliva’s spatial rank-one laminate example has integrability strictly below 2 and cannot fill this gap.

The analysis proves an inverse-energy identity without assuming global Lusin N, by decomposing the full-rank sets into bi-Lipschitz pieces and showing that exceptional images carry zero inverse derivative energy. It also gives an explicit smooth, exact-target sequence approaching the identity strongly forward while its inverse squared-gradient energy diverges. That sequence disproves automatic inverse control, **not** the existence assertion for the identity.

A labeled stronger-input partial is established: a fixed locally bi-Lipschitz bi-W¹,² homeomorphism admits simultaneous exact-target smoothing. The pinned finite-PL-library construction can pay for inverse constants before shrinking the exceptional regions; the source-cited PL smoothing theorem then finishes. This does not construct the initial symmetric replacement of an arbitrary target input.

The exact missing estimate is a sequence of onto locally bi-Lipschitz replacements H_j, strongly close to f forward, with H_j⁻¹→h in L² and

    limsup_j ∫Ω |cof DH_j|² / |det DH_j| ≤ ∫Λ |Dh|².

It would give strong inverse W¹,² convergence by Hilbert-space weak convergence and convergence of norms. The pinned radial cell collapse does not provide it: its outer-shell inverse energy grows like 1/δ as the shell’s radial slope δ tends to zero. Paired source/target budgets need a compatible **single** cell parametrization with this additional cost estimate, with constants fixed before the two energy tails. Separate applications of the one-sided theorem do not suffice.

Full proofs, dependency boundaries, and validation are in [analysis.md](../experiments/i331_bi_sobolev/analysis.md). Operational reading and failed routes are in [reading-and-failures.md](../experiments/i331_bi_sobolev/reading-and-failures.md); authenticated inputs are in [input-authentication.json](../experiments/i331_bi_sobolev/input-authentication.json); primary references are in [literature.md](../sources/i331_bi_sobolev/literature.md). These are research reductions and corrections, with no demonstrated new-to-literature theorem claim.
