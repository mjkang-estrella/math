# discovery.md — pi-graph-normalization-discovery (2026-10-26)

**Outcome: no countable discovery. Both assigned targets are resolved by prior art. Discovery count contribution: 0.**

## Targets assigned

- MathDB **349070** — Guigues Conjecture 8.1 (arXiv:2012.07764v1, Dec 2020): for a connected
  simple graph, x > 0, y = x ⊘ (A+I)x, yᵗ(A+I)y ≤ ‖y‖₁. Live record open, 0 solutions/comments/
  model_attempts/human_solves/formulations/replies at parent fetch and at my re-fetch
  (`sources/349070-live.json`, sha256 017a5396…4db0).
- The source's **general positive-orbit convergence question** (Conjecture 1.1; MathDB neighbor
  **349068**, also open with 0 activity).

## Result 1 — Conjecture 8.1 (349070): TRUE, elementary proof, credit 0

The parent's provisional identity was **verified** (not assumed): for symmetric nonnegative B,
z = Bx, y = x/z,

  1ᵗy − yᵗBy = (1/2) ∑_{ij} B_ij x_i x_j (1/z_i − 1/z_j)² ≥ 0,

a two-line symmetrization using only symmetry of B and z = Bx. This proves the conjecture for
every symmetric nonnegative B (connectedness not needed) and makes the source's Theorem 8.1
unconditional. Exact rational verification: 300 random B (max |lhs−rhs| = 0) + 200 random
connected graphs. Full derivation in `PROOF.md`.

**Credit 0**, two independent reasons: (a) classical Dirichlet-energy-type algebra, per the
parent's own provisional call and the counting standard; (b) decisive — the *same identity in
weighted form is Lemma 1 (Appendix F) of the author's successor preprint arXiv:2605.05330v1
(6 May 2026)*; I confirmed the two identities are algebraically identical (substitute x_i = y_i d_i).
The first resolution on record is therefore the author's own posted proof, not this lane.

## Result 2 — general convergence (349068 / Conjecture 1.1): resolved by posted prior art, credit 0

arXiv:2605.05330v1 (same author, "Graph Normalization: Fast Binarizing Dynamics for
Differentiable MWIS") proves Theorem 2: for every simple undirected graph, every γ > 0 and bias
v > 0, every normalizable x⁰, the WRGN iteration x_i/(x_i + γ∑_{j∈N(i)}(v_j/v_i)x_j) converges
componentwise to a normalizable fixed point (MM energy descent on the semi-algebraic energy
½yᵗ(I+γA)y − vᵗy + boundary-escape Proposition 1 + Attouch–Bolte–Svaiter KL theorem).
**The case γ = 1, v = 1 is exactly the original IGN map** N(x) = x ⊘ (A+I)x of the 2020 source,
so the general positive-orbit convergence conjecture is covered by a posted claimed-full proof.
Per the counting standard ("exclude already posted proofs"), **credit 0**; I did not re-prove it.
Caveat recorded honestly in `PROOF.md` §6: the only step I would re-examine is Proposition 1's
block argument; even if it needed repair, a repaired theorem would still be posted-prior-art
credit 0, and my screening found no counterexample.

Independent numerical corroboration: 200 graphs × 4 starts × 12 000 iterations, all projective
directions stabilized; one n = 10 slow case lingered on a fractional plateau ~8500 iterations then
snapped exactly onto a maximal-independent-set fixed point (stable through 200 000 iterations).
Energy decrease held at 1.8e-15 tolerance at every step. Files: `screen_convergence.py`,
`verify_checks.py`, `independent-checks.json`.

## Neighbor noted, not pursued

- MathDB **349069** (Conjecture 1.2, activated IGN → MIS for distinct weights): open, zero
  activity; **not** subsumed by the 2026 paper (Theorem 4 treats the modified WRGN map with
  γ > 1, not activation functions h ∘ N). Left open: existential "suitable activation" scope is
  ambiguous under the counting standard, and it is outside the assigned inequality/convergence
  targets. No claim; artifacts retained for the parent.
- MathDB 349068/349069/349070 were all created 2026-08-11 from the 2020 source; the 2026
  successor postdates none of the source claims but predates the MathDB records — the "no
  resolution reported" notes refer to the 2020 paper only, and Semantic Scholar lists no other
  citing work (only an unrelated 2021 IWPT paper).

## Ledger impact

No candidate, no count change, no packet. Both excluded-with-proof entries are documented here
and in `PROOF.md`/`progress.md`; proofs and checks retained uncounted. Suggested (parent's call):
349070 could move to ledger `excluded` with reason "elementary symmetrization identity; same
identity posted as Lemma 1 of author's successor arXiv:2605.05330v1 (May 2026)", and 349068 with
reason "claimed full proof posted in arXiv:2605.05330v1 Theorem 2 (γ=1,v=1 = IGN); author's own
successor". I did not edit the ledger.
