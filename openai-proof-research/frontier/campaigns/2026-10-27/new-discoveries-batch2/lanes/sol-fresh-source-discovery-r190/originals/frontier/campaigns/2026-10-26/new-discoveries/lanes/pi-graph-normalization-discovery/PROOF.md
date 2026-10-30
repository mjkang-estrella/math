# PROOF — Elementary resolution of Guigues Conjecture 8.1 (MathDB 349070), recorded at credit 0

Lane: `NEW/lanes/pi-graph-normalization-discovery` (2026-10-26). Solo, no children, no count change.

## 1. Exact source claim

Laurent Guigues, *Concerning Iterative Graph Normalization and Maximum Weight Independent
Sets*, arXiv:2012.07764v1 (14 Dec 2020; only version), Section 8.1, Conjecture 8.1, Eq. (19):

> If A is the adjacency matrix of a connected simple graph then for all x ∈ R+*ⁿ, where
> y = x ⊘ (A+I)x:  yᵗ(A+I)y ≤ ‖y‖₁.

The source states this is "our main conjecture upon which the general convergence of graph
normalization rests" and derives from it Theorem 8.1 (conditional strict increase and convergence
of ‖xᵏ‖₁). MathDB 349070 records exactly this statement, status open, zero solutions/comments/
model attempts/human solves/formulations/replies at parent fetch (2026-10-26 18:2x) and at my
independent re-fetch (snapshot `sources/349070-live.json`, sha256 017a5396…4db0).

## 2. Verification of the parent's provisional identity

Parent provisional identity, for symmetric nonnegative B, z = Bx:

  ∑_i x_i/z_i − ∑_{ij} B_ij x_i x_j/(z_i z_j) = (1/2) ∑_{ij} B_ij x_i x_j (1/z_i − 1/z_j)².   (∗)

**Verified correct.** Proof. Let y = x/z. Since z = Bx,

  ∑_i y_i = ∑_i y_i (Bx)_i/z_i = ∑_{ij} B_ij y_i x_j/z_i,
  yᵗBy      = ∑_{ij} B_ij y_i y_j  = ∑_{ij} B_ij y_i x_j/z_j   (using y_j = x_j/z_j).

Subtracting and using symmetry of B (averaging the expression with i, j swapped),

  ∑_i y_i − yᵗBy = (1/2) ∑_{ij} B_ij (y_i x_j + y_j x_i)(1/z_i − 1/z_j)
                 = (1/2) ∑_{ij} B_ij x_i x_j (1/z_i + 1/z_j)(1/z_i − 1/z_j)
                 = (1/2) ∑_{ij} B_ij x_i x_j (1/z_i − 1/z_j)².

Only symmetry of B and z = Bx are used; B_ij ≥ 0 makes the right side ≥ 0. Hence:

**Theorem.** For every symmetric nonnegative matrix B and every x > 0, with y = x ⊘ (Bx),
yᵗBy ≤ 1ᵗy. In particular Conjecture 8.1 holds (B = A + I is symmetric nonnegative), with the
source's hypotheses (connected simple graph) not even needed beyond symmetry/nonnegativity.

Instant checks: exact `Fraction` verification on 300 random symmetric nonnegative B of size ≤ 6
(`verify_checks.py`, `independent-checks.json`: `identity_exact.pass = true`, max |lhs−rhs| = 0);
exact check of the conjecture itself on 200 random connected simple graphs (`conjecture_graphs_exact.pass
= true`); 200 graphs × 4 starts × 12 000 iterations in floats show the quantity 1ᵗy − yᵗBy ≥ 0 to
float precision at every step.

Equality analysis: 1ᵗy = yᵗBy iff for every pair i, j with B_ij > 0 one has z_i = z_j; on each
connected component of the graph of B's support, z is constant, i.e. Bx = c·1 on each support
component. For connected G with B = A + I this means Bx = 1, the source's fixed-point equation (8).

## 3. Unconditional Theorem 8.1

With (∗) the source's Theorem 8.1 holds without its conditional hypothesis: for any connected
simple graph and x⁰ > 0, x^{k+1} = N(xᵏ), the sequence ‖xᵏ‖₁ is nondecreasing, strictly so unless
xᵏ is a fixed point, and converges (each coordinate of xᵏ for k ≥ 1 lies in (0, 1], so ‖xᵏ‖₁ ≤ n).
This reproduces the source's Eq. (27) argument, now unconditional.

## 4. Why this is credit 0 (mandatory exclusions)

1. **Classical algebra.** (∗) is a one-line weighted-symmetrization (Dirichlet-energy type)
   identity; per the parent's provisional assessment and the campaign counting standard
   ("exclude … equivalent corollaries"; "do not force a result or count a familiar inequality
   corollary"), its rediscovery is not a substantive new discovery.

2. **Posted prior art — the decisive exclusion.** The author's own successor preprint
   Laurent Guigues, *Graph Normalization: Fast Binarizing Dynamics for Differentiable MWIS*,
   arXiv:2605.05330v1 (6 May 2026), contains the same identity in full generality:
   Appendix F, Lemma 1 proves, for symmetric S with unit diagonal and any v > 0, d = Sz,
   y_i = v_i z_i/(Sz)_i:

     ∑_i v_i y_i − yᵗSy = ∑_{(i,j)∈E} S_ij y_i y_j (v_i d_j − v_j d_i)²/(v_i v_j d_i d_j) ≥ 0,

   which with v = 1, S = A + I, y = N(x) is exactly (∗) (algebraically identical: substituting
   x_i = y_i d_i turns the paper's summand into S_ij x_i x_j (d_j − d_i)²/(d_i d_j) =
   S_ij x_i x_j (1/d_i − 1/d_j)², summed over i < j). The paper also proves the weighted mass
   growth (Theorem 3), i.e. the unconditional Theorem 8.1.

3. Semantic Scholar lists only one citing work of arXiv:2012.07764 (an unrelated 2021 IWPT
   parsing paper); no third-party proof of Conjecture 8.1 exists, so the *first* resolution on
   record is the author's own 2026 successor — not this lane.

**Conclusion: MathDB 349070 is resolvable by an elementary classical identity that is already
posted (in weighted form) in arXiv:2605.05330v1 Lemma 1. Credit 0. The proof above is retained
for the record and was independently re-derived and machine-verified before the successor
overlap was confirmed term-by-term.**

## 5. The general convergence question (MathDB 349068) — also resolved by posted prior art

MathDB 349068 ("Conjecture that iterative graph normalization always converges", open, zero
activity; snapshot `sources/349068-live.json`) records source Conjecture 1.1. arXiv:2605.05330v1
states and proves:

- Definition 2: the GN map N_A(x) = x ⊘ (A+I)x — exactly the source's normalization; IGN is its
  iteration.
- Definition 3: the WRGN map N_{A,γ,v}(x)_i = x_i/(x_i + γ∑_{j∈N(i)} (v_j/v_i)x_j); the special
  case γ = 1, v = 1 is *exactly* the original IGN map.
- Theorem 1 (App. B/C): every WRGN step is an exact Majorization–Minimization step on the
  semi-algebraic energy Ẽ_{γ,v}(y) = ½ yᵗ(I + γA)y − vᵗy; strict decrease off fixed points;
  hence vanishing step sizes.
- Proposition 1 (App. D): the sequence cannot accumulate on non-normalizable points; hence it is
  eventually confined to a compact subset of the normalizable domain.
- Corollary 1: all accumulation points are normalizable fixed points.
- Theorem 2 (App. E): for every simple undirected graph, every γ > 0 and v ∈ Rⁿ₊₊ and every
  normalizable x⁰, the WRGN sequence converges (componentwise) to a normalizable fixed point,
  via the Attouch–Bolte–Svaiter Kurdyka–Łojasiewicz theorem (H1–H3 verified; the energy is
  semi-algebraic, hence KL).

Setting γ = 1, v = 1 gives the original IGN; therefore the source's general positive-orbit
convergence question (Conjecture 1.1, MathDB 349068) is **resolved by a posted proof by the
source author himself** (v1 preprint, 6 May 2026, three months before the MathDB records were
created on 2026-08-11; MathDB's "no resolution is reported" note refers to the 2020 source only).
Under the counting standard ("exclude already … posted proofs") this yields **credit 0** for the
general convergence question in this lane; I record it rather than re-proving it.

Independent numerical corroboration (not a proof): 200 random connected graphs (n ≤ 16) × 4
log-uniform starts × 12 000 iterations — every orbit's projective direction stabilized (drift
< 1e-5 except one n = 10 case with dev 0.15, which on inspection was a slow transient lingering
on a fractional plateau until k ≈ 8500 and then snapping exactly onto the binary fixed point
(1_S for a maximal independent set S = {5,7,8,9,10} in 1-indexed labels), remaining exact
thereafter through k = 200 000; `screen_convergence.py`, and the drift investigation transcript in
`progress.md`). Energy monotone decrease (2026 Thm 1) held at every step to 1.8e-15. No
counterexample to convergence was found; no counterexample is claimed.

## 6. Honest status of the 2026 proof

I read Appendices B–F of arXiv:2605.05330v1. The MM identity, dominance lemma
(2ab ≤ a²+b² symmetrization — same family as (∗)), KL properties and H1–H3 verification are
explicit. The one step I would write differently is Proposition 1's block argument (the choice of
L versus the step-size threshold K_L is ordered heuristically); I did not verify it line-by-line to
publication standard. This does not change the lane outcome: a complete claimed proof by the
source author is posted prior art, and any repair or re-proof of the same theorem would still be
credit 0. If the parent ever judges Theorem 2 of 2605.05330v1 void, the convergence question
reopens; my screening produced no counterexample and no independent proof, so no claim is made
either way.

## 7. Neighbor question left open (not pursued, recorded for the parent)

MathDB 349069 (source Conjecture 1.2: IGN with "a suitable non-linear activation" converges to a
maximal independent set for node-weighted graphs with all distinct weights; snapshot
`sources/349069-live.json`, open, zero activity). The 2026 successor does **not** address
activated maps: its Theorem 4 binarizes the *modified* WRGN dynamics (γ > 1), not h ∘ N. The
conjecture's "suitable" existential quantifier is also scope-ambiguous under the campaign's
counting standard. Recorded as an open neighbor; no claim.
