# MathDB 368807: a vertex of the ASEP polytope on 8 nodes adjacent to no tour

Status: candidate only. Root acceptance, independent fidelity and significance reviews, a paper and a root replay are still required. No credit is claimed.

## Source and exact statement

Source: E. Vercesi, J. Barta, L. M. Gambardella, S. Gualandi and M. Mastrolilli, *On the integrality Gap of Small Asymmetric Traveling Salesman Problems: A Polyhedral and Computational Approach*, arXiv:2506.10671. The arXiv abstract page fetched on 2026-11-02 lists only v1 (submitted 12 June 2025). The PDF receipt is `sources/368807-pdf-receipt.json` (sha256 `a4c72db9…`).

- Notation (p. 2): K_n = (V, A) with m = n(n-1) arcs, and δ(S) := {(i, j) : i ∈ S, j ∉ S}.
- Formulas (2)–(4) and (6): P_ASEP^n = {x ∈ R^m : Σ_i x_ij = 1 for all j; Σ_j x_ij = 1 for all i; Σ_{(i,j)∈δ(S)} x_ij ≥ 1 for all S ⊂ V with 2 ≤ |S| ≤ n-2; x ≥ 0}.
- Definition 3: N(x) is the set of all vertices adjacent to the vertex x. Lemma 7's proof spells out adjacency as sharing r(n)-1 linearly independent tight constraints, which is ordinary adjacency in the vertex–edge graph of the polytope.
- Conjecture 1 (p. 14): "For each x vertex, N(x) contains at least one tour." It rests on preliminary tests: the source enumerates n = 4, 5 and studies some neighbourhoods for n = 6, where it reports that full neighbourhoods are computationally infeasible.

The MathDB raw line is preserved in `raw/368807.jsonl`, with its hashes in `results.json`.

## The counterexample

Nodes are labelled 0,…,7. Here is x* = X/4, where X is the integer matrix below (row i, column j; the diagonal is zero):

```
 0 0 1 2 0 1 0 0
 0 0 1 0 0 0 1 2
 0 2 0 0 0 2 0 0
 2 0 0 0 0 0 0 2
 0 1 0 0 0 0 3 0
 0 1 0 0 3 0 0 0
 0 0 0 2 1 1 0 0
 2 0 2 0 0 0 0 0
```

So x*_{02} = 1/4, x*_{03} = 1/2, and so on. The support has 19 arcs. Every row and column sums to 4, so every degree constraint holds with value 1. Every cut S with 2 ≤ |S| ≤ 6 has 4·x*(δ(S)) ≥ 4. Exactly eight cuts are tight:

{0,3}, {4,6}, {0,3,7}, {4,5,6}, {0,1,2,3,7}, {1,2,4,5,6}, {0,1,2,3,5,7}, {1,2,4,5,6,7}.

**Theorem.** x* is a (fractional) vertex of P_ASEP^8, and no tour is adjacent to x*. Hence Conjecture 1 fails for n = 8.

### Proof

*x\* is a vertex.* The 45 tight inequalities (37 zero arcs and 8 tight cuts) together with the 16 degree equations have rank 56 = m. So x* is the unique solution of its tight system and is an extreme point. Lean (`ASEP.eq_xs`, `ASEP.xs_extreme`) argues directly instead of computing a rank. If x* is an interior point of a segment [y, w] in P_ASEP^8, then y and w vanish on the 37 zero arcs and are tight on the 8 tight cuts. Linear arithmetic on these 24 equations in the 19 support coordinates then forces y = w = x*.

*No tour is adjacent.* Let T be any of the 7! = 5040 tours, and let z = (x* + T)/2. Its tight set J is the set of constraints tight at both x* and T, i.e. the minimal face of [x*, T]. Each tour comes with an integer vector v that satisfies the following:

1. v_ij ≠ 0 only on arcs in supp(x*) ∪ T, and v_ii = 0.
2. Every row sum and column sum of v is 0.
3. Σ_{δ(S)} v = 0 for every one of the eight x*-tight cuts S that T crosses exactly once.
4. Σ|v| ≤ 64.
5. v is not parallel to x* - T, witnessed by an explicit 2×2 minor.

Every entry of x* is 0 or at least 1/4, and every cut value is 1 or at least 5/4. T is 0/1-valued and crosses each cut at least once (an integer count). Therefore each constraint not tight at z has slack at least 1/8 at z. Since |(1/512)·(any partial sum of v)| ≤ 1/8, both points z ± v/512 lie in P_ASEP^8. Now z is the midpoint of z - v/512 and z + v/512. If [x*, T] were a face (an extreme subset), it would contain z - v/512, so v would be parallel to x* - T. That contradicts condition 5. So [x*, T] is not a face, and x* and T are not adjacent. The argument also excludes exposed faces, since exposed sets are extreme.

The certificates were found with exact sympy nullspaces (`scripts/asep_cert.py`). Each one has been re-checked in Python (`scripts/asep_lean_data.py`) and checked again in the Lean kernel.

### Independent numerical confirmation (diagnostics, not the proof)

- `scripts/asep_exact_all.py` computes exact integer ranks of [A_eq; C_J] for all 5040 tours. The maximum common rank is 54 < 55, so the face of [x*, T] has dimension ≥ 2 every time. The vertex rank is 56.
- `scripts/asep_independent.js` is a separate BigInt implementation in Node that shares no code with the Python scripts. It regenerates every constraint and enumerates the tours itself, and it gives the same result: feasible, vertex rank 56, 0 adjacent tours, and the identical rank histogram {44:213, 45:590, …, 54:27}.
- Controls: the source's n = 4 half-integral vertex (Example 1) comes out adjacent to 5 of the 6 tours, as the source states. A sampled n = 5 population and the source's n = 6 observations also behave as expected (`outputs/asep/n4.json`, `n5*.json`, `n6*.json`).

### How it was found and search coverage

Sampled LP vertices with random costs gave minimum adjacent-tour counts of 5 at n = 4, 4 at n = 5 and 3 at n = 6. A simulated-annealing walk on the vertex graph then minimised the adjacent-tour count (`scripts/asep_walk.py`; exact pivots along 1-dimensional faces with rationalised vertices). At n = 7 the best of eight walks (2000–4000 steps each) reached 1 adjacent tour, never 0. At n = 8 the walks hit 0 quickly: seed 21 found a first example with denominator 5, and seeds 41/42 found 100 distinct zero-count vertices (denominators 4–11, supports 19–20, all but one with trivial stabiliser). We chose the denominator-4, support-19 vertex above. The n = 7 case is therefore **open** in this lane: no exhaustive enumeration was attempted, and the claim is only about n = 8 (and, through the conjecture's quantifier over all n, refutes the conjecture).

## Lean endpoint

Packet: `lean/ASEP*.lean` (21 modules).

Literal endpoints on the source's arc space ℝ^A, A = {(i,j) : i ≠ j} (`lean/ASEPArcs.lean`):

- `ASEP.arc_counterexample : xa ∈ extremePoints (arcPolytope 8) ∧ ∀ t, IsArcTour 8 t → ¬ ArcAdjacent 8 xa t`
- `ASEP.arc_neighborhood_tour_conjecture_false : ¬ ArcNeighborhoodTourConjecture`

Here `arcPolytope n` is source (2), (3), (4) with δ(S) = {(i,j) : i ∈ S, j ∉ S}, together with x ≥ 0. Adjacency means both points are extreme points, they are distinct, and the segment is an extreme subset. The transfer goes through the zero-diagonal embedding (`mem_arcPolytope_iff`, `xa_extreme`, `arc_segment_not_face`).

Matrix-form endpoints (`lean/ASEPMain.lean`):

- `ASEP.counterexample : IsVertex 8 xs ∧ xs 0 2 = 1/4 ∧ ∀ t, IsTour 8 t → ¬ Adjacent 8 xs t`
- `ASEP.neighborhood_tour_conjecture_false : ¬ NeighborhoodTourConjecture`, where the conjecture is ∀ n ≥ 4, ∀ vertex x, ∃ tour t adjacent to x
- `ASEP.segment_not_face`, `ASEP.segment_not_exposed`: for every tour t, the segment [x*, t] is neither an extreme subset nor an exposed subset of P_ASEP^8.

Definitions (`lean/ASEPDefs.lean`):

- `polytope n` is P_ASEP^n written as n×n real matrices with zero diagonal. This is the matrix form the source itself uses in Section 3 (x_ii = 0), together with constraints (2), (3), (4) for 2 ≤ |S| ≤ n-2 (Σ over i ∈ S, j ∉ S) and x ≥ 0.
- `IsVertex` is `Set.extremePoints ℝ`.
- `Adjacent n x y` means both are vertices, x ≠ y, and `IsExtreme ℝ (polytope n) (segment ℝ x y)` (the segment is a face).
- `IsTour n t` means t is the incidence matrix of i ↦ σ i for an n-cycle σ (`σ.IsCycle ∧ σ.support = univ`), i.e. a directed Hamiltonian cycle.

Proof structure:

- `ASEPSound.not_extreme_of_dir` is the generic real-analysis lemma above.
- `ASEPVertex` covers x* ∈ P, the gap facts and extremality.
- `ASEPCheck`/`ASEPData` hold a Boolean checker and 5040 base-128-encoded certificates.
- `ASEPCover` proves by kernel `decide` that the certificate cyclic orders are exactly `List.permutations' [1..7]`.
- `ASEPCerts0..11` run 48 kernel `decide` checks of `chk` over chunks of 105 certificates.
- `ASEPBridge` proves soundness of `chk`, and `ASEPMain` handles the n-cycle → cyclic order bridge, using `IsCycle.orderOf` and `IsCycle.pow_eq_one_iff`.

Replay: `scripts/asep_replay.py lean-replay-3` (current; `lean-replay-2` is the earlier 20-module replay and `lean-replay-1-failed-leanchecker-path` records a PATH setup failure of leanchecker only) builds a fresh copy of the sources with a sanitised environment and the pinned prebuilt dependencies (mathlib d13f23b7…, Lean 4.34.1), using `-DwarningAsError=true`. It then runs `leanchecker` on all 21 modules (all exit 0), scans for forbidden constructs (clean: no sorry/admit/axiom/unsafe/native_decide/ofReduceBool/implemented_by/extern), and audits axioms. All five endpoints depend only on `propext, Classical.choice, Quot.sound` (`lean-replay-3/result.json`). Each compile step ran under an RSS watchdog: peak 4.9 GB (the coverage module), and ≤ 2.8 GB for the others. The kernel `decide` checks are proved-sound Boolean checkers; there is no `native_decide`.

Trust limits: the replay uses the pinned prebuilt mathlib/batteries oleans; mathlib itself is not rebuilt. `leanchecker` was run per module without `--fresh`.

Fidelity points for reviewers:

1. The arc-indexed space ℝ^{n(n-1)} is covered literally in `ASEPArcs`. Internally the proofs use the source's own Section 3 matrix form.
2. Adjacency is formalised as "the segment is an extreme subset". For polytopes, this agrees with the source's rank-based adjacency, and it is implied by the exposed-face reading, which is also excluded.
3. The conjecture domain is formalised as n ≥ 4, since the source studies n ≥ 4. The n = 2 case would be a degenerate counterexample and is not used.

## Prior art and significance checks (bounded)

- The source has only arXiv v1. Its follow-up by the same group (arXiv:2511.05045, Sosso–Bernardelli–Gualandi, PDF read) does not mention Conjecture 1 or neighbourhoods.
- A web search found no refutation or discussion.
- Registry path screens show no ID or keyword match: Omega HEAD 9e88f6fb… (complete untruncated D5/Problems trees fetched 2026-11-02) and the OpenAI/math HEAD 4eaee875… preprint listing (unchanged; cached listing keyword screen for ASEP/subtour/TSP).
- Checks (1)–(3) from the task:
  - (1) The source's own results (orbit symmetries, Lemma 7) do not imply the negation.
  - (2) No cited construction gives such a vertex. The cited constructions concern integrality-gap families.
  - (3) No known generic adjacency failure covers P_ASEP. Vertices of relaxations that are non-adjacent to every integral vertex are not ruled out in general, and the source explicitly hoped Conjecture 1 would let "pivoting on an integer vertex" reach the full V-description.

  This is a bounded search, not novelty clearance.
- Significance caveat: the conjecture comes from preliminary tests in a computational OR paper, and the counterexample lies just beyond the tested sizes (n ≤ 6). Root should judge significance. The refutation does defeat the source's proposed strategy of obtaining the full V-description by pivoting from an integer vertex, because by Lemma 7 that strategy would need every orbit to be adjacent to a tour.
