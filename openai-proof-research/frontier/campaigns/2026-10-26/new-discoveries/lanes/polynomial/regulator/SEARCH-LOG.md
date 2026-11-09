# Regulator-polynomial screening, 2026-10-26

Paused at parent's request for independent review of the strengthened taxicab theorem. New discoveries from this screening: **0**. No polynomial claim has been formalized or presented as proved.

## Primary definitions and current state

Read Battistoni, arXiv1912.08512v1/v2, especially v2 §4.1 equation (11), §4.2, Table 2, and Conjectures 1–4. Q is the product of |1−epsilon_i/epsilon_j| for ordered nonzero magnitudes, with prescribed real nodes and conjugate pairs; the changed-variable functions extend to a closed cube. Zero ratio parameters in that closure are legitimate, but a strict original-node witness would need a nonzero perturbation.

Read Battistoni–Molteni, *Generalized Pohst inequality and small regulators*, arXiv2211.16842v3, especially Theorems 1–2, §4 change of variables, and §8. The paper is now Math. Comp. 94(351) (2025),475–504, DOI10.1090/mcom/3954. Author index and later Raposo2025 references confirm that journal citation; “to appear2024” on the preprint is old metadata.

**344947 excluded as already proved.** The later paper's Theorem1 gives the sharp global degree-five bound16M=16.6965..., M=3^(15/2)/(4*7^(7/2)), stronger than the old restricted ordering. Its Section8 also already establishes sharp first-ordering bounds32 in degree6 and32M in degree7. These known special cases cannot receive novelty credit.

**344948 and344949 remain genuine larger targets in the inspected literature**, but no proof/counterexample was found here. The later paper keeps the global one-complex recurrence conjectural; its upper bounds for degree6–9 are34.89,65.81,80,233.1. Its exact source conventions must be retained rather than treating these bounds as sharp maxima.

The old printed odd maximizer pattern differs from the later paper's correct zero-separated n=7 point. No sign/pattern discrepancy is counted as a mathematical counterexample. Likewise, rounded decimal entries are not refuted by last-digit numerical changes.

## Computations

`search_one_complex.py` implements the actual source product with n−2 signed edge ratios and g=sin(theta). Every real/complex pair contributes1−2tg+t² and each real/real pair1−t, with the complex pair contributing2cos(theta). Independent reconstruction of the original complex nodes agrees numerically on random tests; analytic gradients were checked against central finite differences. The known sharp degree-five value is also checked.

Completed degree6–16, all orderings up to the source reversal symmetry,30 multistarts per ordering (58 orderings total). Mixture of interior and near-boundary starts; L-BFGS-B. Every best value agrees with the conjectured value to floating-point tolerance. Maximum apparent relative excess is about1e−15, ordinary roundoff. No robust counterexample. `search-results.json` contains exact settings and numerical outputs. This is neither a certified upper bound nor proof.

`search_two_complex.py` implements the actual conjugate-root product with positive radial edge ratios, separate angles for both pairs, and explicit real signs. It keeps the cos(theta_i±theta_j) interaction, avoiding an inconsistent independent-cosine relaxation. Random direct-node reconstruction and gradient tests pass; the sixth-roots-of-unity value216 is checked.

Completed degree8 with two complex pairs: all15 placements times8 real-sign cases after global-sign symmetry,15 multistarts each. Largest value found439.80465111040036. The old table lists7^(7/2)=907.4926997; finding a lower numerical value does **not** refute that maximum claim. Proving a strict global upper bound below907 would require new mathematics or a rigorous certificate. No such certificate was obtained. A degree7 calibration search reproduces the tabulated245.81928 value; consult the results JSON for the fully completed range.

Dependencies numpy/scipy are confined to this lane's `.pydeps/`. No external application was modified.

## Source inventory

- `sources/1912.08512v1.pdf`: SHA256`b9c814f8ed9572d3e7df81361f3db0cf1053a14a87a40465d0f32f374b38dc0a`.
- `sources/1912.08512v2.pdf`: SHA256`0549a2c17c6bfc1e7d797cc79092b0ddcc3ea33c969ce37b94cf93e1fc7ee976`.
- `sources/2211.16842.pdf` (v3): SHA256`aaec2b2c1d3e47e7255be7c0e3e82d983c4d0636d81e29e8aea00c407758a3ba`.

The original Table2 was rendered and visually checked (`sources/table.png`). Searchable text extractions are alongside the PDF research snapshots. These are not publication artifacts or redistribution authorization.
