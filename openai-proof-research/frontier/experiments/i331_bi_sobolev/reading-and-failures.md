# I331 — operational reading and failed routes

## Source discipline

Read openai-proof-research/AGENTS.md and sources/upstream.json; locate family 368 using sources/CONTENTS.md and the complete sources/preprints-tree.json. Raw upstream files were retrieved at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Input byte hashes and specific inspected sections are recorded separately. Bodies were read through tool output; no source-body copies, downloaded PDFs, scan output, or auxiliary files were retained. Long initial output was truncated, so decisive operational passages were retrieved again in bounded ranges. No live I325 or I329 bodies were opened.

## Pinned low-exponent construction

`01-introduction.tex`, `main:theorem`: bounded domains, 1≤p≤2, exact-target smooth diffeomorphisms, global strong forward W¹,p. The full introduction agrees with the supplied 16336-byte hash. It expressly distinguishes inverse smoothness from inverse Sobolev convergence. `10-conclusion.tex` agrees with the supplied 927-byte hash and composes `la:approximation` with `sm:smoothing`; there is no extra inverse estimate.

Operational passages inspected in `03-low-tools.tex`:

- `lt:disk`: boundary-fixing parametrization converts image area and boundary squared-speed into forward Dirichlet energy; the sharp form recovers a plane derivative. Its bi-Lipschitz constants may depend on each embedding.
- `lt:collapse`, lines 372–435: a radial profile expands a tiny central source region and compresses most source radii into a thin target collar. The central forward cost is O(α^(m−p)); the outer radial derivative tends to zero as δ→0. Section 4 of analysis computes the resulting inverse blow-up.
- `lt:trace-slicing`, lines 1068–1138: generic source curves and critical source surfaces have image area formulas. Critical surface validity uses CHM Theorem 1.3 after chart straightening. This is not a global volume N assertion.
- `lt:budget-transfer`, lines 1518–1596: the final squeeze is **in the target**, H₀=T∘G. Reciprocal compact closeness and inverse angular safety are retained, but the cost conclusions bound images of the chosen source traces. Its words about inverse safety do not assert inverse derivative energy bounds.
- `lt:budget-expectation`, lines 1598–1651: bounds sampled tie budgets by original tangential image mass. Applying it to h independently creates another budget construction, with no proof that its output is the inverse of H₀.

Operational passages inspected in `04-low-assembly.tex`:

- `la:approximation`, lines 8–18: onto locally bi-Lipschitz approximation, with only the forward integral specified.
- `la:inverse-bv` and `la:radial-blocks`, lines 84–240: reverse rays select conical stars and short initial traces using BV slicing, including the singular-variation density. This supplies geometry for forward surface costs, not squared inverse-gradient control.
- Lines 580–631: vertex contractions explicitly permit lack of a uniform inverse Lipschitz bound as contraction tends to zero.
- `la:cell-completion`, lines 1071–1144: faces are parametrized once to agree across cells; volume completion uses `lt:collapse` with p≤2<3. Its cost sums source boundary energies and image areas.
- Lines 1146–1350: choices first fix compact forward jets and constants; `la:ordinary-tail` and `la:outside-core-energy` control ∫|Df|^p and ∫|DH|^p outside source cores. `la:derivative-final` proves forward derivative closeness. A same-map inverse energy tail is absent.

`02-smoothing.tex`: inspected `sm:smoothing`, `sm:pl-smoothing`, and especially `sm:bilip-pl`, its coarse bounds, good tests, finite stored models, preserved interpolation, and bad-volume payment (lines 414–955). The finite PL embeddings have inverse derivative constants as well as forward constants. For a fixed locally bi-Lipschitz input these can be fixed before resolution, allowing the additional accounting proved in analysis Section 5. This observation does not make the constants uniform for the preceding arbitrary-input replacement.

## Companion check

The actual high-exponent introduction, `main:theorem`/`ha:approximation`, assumes p>2 and again specifies only forward convergence; it explicitly separates singular determinant penalties and inverse Sobolev convergence. The opening assembly and its inverse-related occurrences were checked. Its retained rank-deficient mechanisms do not supply the missing critical two-sided assertion. No conclusion from p>2 is transferred to the present p=2 input.

## Classical and contemporary primary reading

Pratelli: read Theorem A, the preliminary good-square interpolation interface, Section 3’s zero-Jacobian analysis and norm identity, and Section 4’s construction. Good squares supply local errors in both directions. The bad and uncovered squares are paid using the planar identity ∫|Du⁻¹|=∫|Du|, particularly equations (17)–(18), rather than an independent inverse extension construction. That mechanism has no spatial squared-gradient analogue with nonsingular density. Its higher-dimensional remark only kills cofactors under bi-W¹,¹; it does not kill all nonzero gradients.

Campbell–D’Onofrio–Vítek: read Theorem A and Section 3’s face/edge/vertex smoothing and final locally finite assembly. The inverse estimate uses bounds fixed on a finite PL configuration and the small measure of the modified region’s image; equations (3.18)–(3.19) and the final summable local error allocation are the relevant interface. Arbitrary-input approximation is outside its hypotheses.

Oliva: read Theorems 1–4 and their sharpness arguments, particularly the coarea/sliced-N proof of Theorem 2. For n=3 its Theorem 1 has m₁=m₂=1 and p,q<2. The endpoint is excluded from the construction. Theorem 3’s equality discussion is not an endpoint existence theorem. No attempt was made to promote weak-L² or all p<2 information to L².

The 2011 Di Gironimo–D’Onofrio–Sbordone–Schiattarella paper was read at its actual introduction and theorem statements. Its N-property criticality discussion is planar. It was not cited as a spatial theorem.

CHM: read actual Theorems 1.1–1.3, the sliced-N argument, coarea interface Theorem 4.4, Theorem 4.5 and its contradiction proof, and the end of Theorem 1.2’s proof. Using Theorem 4.5 in both directions, rather than a heuristic critical-integrability argument, conclusively removes the proposed rank-one obstruction. The source itself includes nowhere-differentiable examples; the transport proof therefore uses approximate/Lipschitz pieces, not assumed classical differentiability of the given map everywhere.

## Routes rejected or still missing

1. Two independent Ball–Evans sequences: neither sequence identifies its inverse with the other; rejected as solving a different problem.
2. Smooth inverse of each approximant: no norm convergence follows. Analysis (4) refutes even uniform inverse W¹,² boundedness from strong forward convergence.
3. Low-rank laminate counterexample: actual endpoint integrability is absent, and the target’s rank-one zero-Jacobian stratum is impossible by analysis (1).
4. Formal global change of variables: N can fail at this exponent. Analysis (3) instead treats exceptional images through inverse full-rank pieces and zero inverse derivatives.
5. Running both trace samplers: separate trace existence is easy, but a common squeeze and common cell parametrization preserving both measurements is unproved. Later target squeezing may magnify inverse source costs.
6. Symmetric locally bi-Lipschitz replacement: the last smoothing stage can be completed for a fixed such input. The initial replacement still lacks the inverse limsup energy estimate (10).
7. Rank-stratified repair: only full rank and rank zero remain a.e.; eliminating ranks one and two is useful but leaves coupled tail control and the possible positive-measure image of source-null sets.
8. Forward-W¹,²/inverse-W¹,¹ continuity: cofactors converge in L¹ under strong forward W¹,², but strict BV convergence alone does not imply strong gradient convergence. A general continuity theorem was not proved or used.

Validation was symbolic: verify matrix factors, the bump normalization and exact image, radial eigenvalues and energy integrals, both directions of the CHM hypotheses, Lipschitz-piece treatment of exceptional images, and the order of constants in the stronger-input smoothing proof. No experiment based on sampled numerical values was run. General-target status is blocked on (10), not completed by these partials.
