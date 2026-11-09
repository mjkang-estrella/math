# claude-all-even-height-rigidity-r1: unresolved, zero nominations

**Target.** Kalmanovich–Nivasch, arXiv:2610.38864v1, Conjecture 2.1 (p.4). Every finite S ⊂ R³ that
affinely spans R³ has a direction ℓ with n_S(ℓ) odd. Theorem 3.3 (p.6) makes this equivalent to
height-rigidity of every planar all-even set; I verified that proof. Theorem 8.1 (p.20) covers all-even
sets with *some* direction having ≤ 6 occupied lines, with no bound on |A|. It forces any counterexample
to have ≥ 8 lines in every direction.

**Result.** There is no full proof and no counterexample, so no PROOF.md. The rigorous pieces below are
restricted or subsumed and receive no credit; details are in discovery.md.
* **Prop A** (two parallel hyperplanes give a singly-determined direction): already contained in the
  source's Prop 7.3 argument.
* **Prop B:** if S lies in two non-parallel planes and one plane's part avoids one side of their common
  line, then S has a singly-determined direction. Proof: elementary lexicographic extremes, or no zero
  divisors in F₂ of the bi-orderable group Aff⁺(R). The two-sided case has genuine zero divisors and is open.
* **Prop C:** for a product Q×H with c_g(H) odd (number of minimal-gap pairs in H), there is an odd
  direction (diameter plus parallelogram law). A line-all-even product would also need N_u(Q) even for
  every u.
* **Lemma D:** the source's Ak "centrally symmetric set plus one swap" mechanism cannot leave a plane on
  three layers. The proof is a finite-set contraction Y′/3 ⊂ Y′.
* **Observation E:** for lattice-convex sets the condition becomes bilinear (r_S(d) even for every
  primitive d). No examples found.

**Exact missing lemma.** Fibre parity rigidity (discovery.md §3). It is equivalent to the conjecture and
known only for ≤ 6 fibre lines. Leading-term methods close a case only when the extremal product is unique.
At every order they are blocked by affine lifts of planar all-even sets, and by trilinear terms once a fibre
line carries ≥ 3 columns.

**Support evidence (not proof).** Exhaustive F₂-quadratic enumeration of all subsets of 15 spherical
universes (up to 2²² subsets) finds only the source's coplanar cyclotomic sets; positive controls
P13/P15/P16 match the source's Table 1. Point-group orbits, products, lattice-convex samples and local
search found nothing. Local search fails even its planar control, so it carries no weight.

**Prior art.** Bounded arXiv API screen, 2026-10-30: no follow-up or resolution, and the source exists only
as v1. Registries, MathSciNet and zbMATH were not checked.

**Process.** Originals are unchanged: hashes before and after match (verification-receipt.json). No Lean,
manuscript, shared edits, git, MathDB, browser, external posts or child agents. Counts remain 9/39, next 40.
