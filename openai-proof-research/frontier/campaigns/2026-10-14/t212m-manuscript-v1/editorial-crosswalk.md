# Editorial and proof crosswalk

This is an author account, not an independent review. The reviewed r74 packet remains immutable.

- Contribution R1: proof-r1 PASS_FULL was adopted by the parent; D/S/P/W label correspondence is preserved in the exact adoption record. Manuscript and final-release gates are separate.
- R2: article Section 1 and abstract identify the entire paid finite-min4-second-moment class and the additional infinite class, with exact DH conjecture scope and conditional-source convention.
- R3: Section 1 restricts novelty to D/S/P/W and credits ADH Appendix C C.5/(26), Cox–Durrett/Kesten through Cerf–Théret, Boivin through AH/DH, and AH9.10 Case 1. Shape, cap equivalence, two-status kernels and source budgets receive no separate novelty claim. Original bodies of Cox–Durrett/Kesten/Boivin were not read.
- R4: Sections 4, 5 and 8 explicitly treat DH6.2/triple and AH6–10 as proof-level reuse under replaced hypotheses, not direct theorem invocation with finite energy missing. The detailed use-site crosswalk is part of the article and needs independent manuscript scrutiny.
- Contribution O1–O5: cap finite-energy counterexample, original uniform-shape obstruction, classical cap shape credit, vacuous unbounded-cap ceiling, and historical-only earlier attempts are all explicit.
- Proof O1–O6: every tangent functional is quantified; limiting reference stability descends to the prescribed pair; new label membership follows by AC; selector premises precede the second wall; wall threshold is uniformly 4Mm^3 with exact diagonal constants; AH4.6 uses cap boundary integrability directly, without S's optional appendix.
- Parent draft repairs: unchanged uncapped paths are asserted only under upward original modification; the empty finite-change set is immediate; all `sec:uses` references resolve to Section 8.

## Explicit generalized formulation for manuscript rechecking

Remark 4.2 extends the original D argument from threshold resampling to a kernel on a **fixed deterministic finite** original support with **bounded output marginal density**. Stability is asserted only on its upward event. The full original pair and, if necessary, upward-event indicator are retained throughout the limiting lift; their projected law is fixed at every approximation and hence unchanged in the limit. Tight localization, strict uncapping and density domination are the same proof ingredients. This generalized wording is not described as separately certified by proof-r1. The manuscript reviewer must recheck it and its uses in Sections 5 and 7.

Later sites/radii/finite regions are fixed before applying the kernel. There are countably many choices. No arbitrary state-dependent support, unbounded-density kernel, or cap conditional finite-energy claim is covered; a variable support requires the stated fixed-support/countable reduction. Parent author discussion endorsed making this explicit; that discussion is not independent verification.

## Scoped formal review supplement

The full formal review and limits were read and copied after drafting. PASS_SCOPED_T212M concerns deterministic support only. The original 14 support plus 17 controls are distinct from the reviewer's 60 constants in Independent.lean. Original Fin4 examples instantiate the segment lemma and all-walk segment consequence, not escape or the infinite-tail theorems. Reviewer supplements provide infinite-graph nonvacuity, a uniform metric-threshold consequence and explicit hypothesis-deletion controls; they are separate reviewer work, not additions to frozen v1. No review helper or third-party body is copied. Full FPP remains unformalized.
