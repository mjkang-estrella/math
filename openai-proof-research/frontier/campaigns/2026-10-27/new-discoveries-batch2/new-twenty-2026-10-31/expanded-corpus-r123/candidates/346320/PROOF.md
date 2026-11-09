# MathDB 346320: a 6-vertex counterexample to Conjecture 6.2 of Kobeaga, Merino and Lozano (strategy S1S2)

Status: candidate for root review. This lane does not self-accept. The Lean file
`lean/MathDB346320.lean` is an UNCOMPILED draft, because Lean is not run in this lane.

## Source and literal statement

- MathDB 346320, "Isomorphism conjecture for graphs obtained by fixed shrinking strategies".
  Raw line: corpus chunk `mathdb-normalized-chunk-0007.jsonl`. Hashes are in `../../extracted.json` and `../../raw/346320.jsonl`.
- Source: G. Kobeaga, M. Merino and J. A. Lozano, "On solving cycle problems with Branch-and-Cut:
  extending shrinking and exact subcycle elimination separation algorithms", arXiv:2004.14574.
  The published version is Annals of Operations Research 305 (2021) 107–136.
  All four arXiv versions (v1–v4) are cached in `../../sources/`. v4 is the post-peer-review
  version. Every version prints the conjecture identically, as Conjecture 6.2: v1 and v3 at lines
  1419–1420, v2 at lines 1417–1418, v4 at lines 1419–1420.

> **Conjecture 6.2.** Given a graph G, let (y, x) ∈ P_A^G be a vector and SRK ∈ {C1, C1C2, C1C2C3, S1, S1S2}
> be a fixed shrinking strategy, then the graphs obtained by applying SRK to (y, x) are isomorphic.

The authors motivate it as follows (v4, Section 6.5): "the number of vertices and edges in the
shrunk graph (the final result) is independent of the ordering of the considered rules and the
shrinkable sets".

## Definitions used, all exactly as in the source

- P_A^G (eq. (11)) is the set of (y, x) ∈ R^V × R^E satisfying four conditions:
  - (7a) the degree equations x(δ(v)) = 2y_v;
  - (7b) the logical constraints x_e ≤ y_v for v ∈ e;
  - (7e) the bounds 0 ≤ y_v ≤ 1;
  - (7f) the bounds x_e ≥ 0.
- Shrinking a set S into a new vertex s (eqs. (15), (16)) works as follows:
  - E[S] keeps the edges of E(V−S) and adds an edge [s, v] whenever x(S : v) > 0. This gives the support graph.
  - The new edge values are x[S]([s,v]) = x(S : v).
  - Other vertices keep their values, y[S](v) = y_v.
  - The new vertex gets y[S](s) = x(δ(S))/2.
- Rule S1 (Theorem 4.4): two vertices u, v with x[u,v] = y_u = y_v = c, provided some other
  vertex w satisfies y_w ≥ c, are shrunk.
- Rule S2 (Theorem 4.5): two vertices with x[u,v] > max{y_u, y_v} are shrunk.
- Strategy S1S2 is Algorithm S1S2 of Appendix A.1. It keeps a heap H, initially all vertices, and
  repeats three steps until H is empty:
  - select some u ∈ H and remove it;
  - for v ∈ N(u): if y_v = c := y_u and x[u,v] = c, apply S1 when a witness w exists;
    otherwise, if x[u,v] > y_u and x[u,v] > y_v, apply S2;
  - after a shrink, add the new vertex s and its neighbours to H (SHRINK/UPDATE and Section 6.2).
  The selection of u and the scanning order of N(u) are not specified. Conjecture 6.2 asserts that
  the final graph does not depend on these choices, that is, on "the ordering of the considered
  rules and the shrinkable sets".

## The counterexample

Take V = {0, 1, 2, 3, 4, 5}, G = K_6, and set y = (1/2, 1, 1, 1, 1, 1). The edge values are:

| edge | {0,4} | {0,5} | {1,2} | {1,3} | {2,3} | {2,5} | {3,4} | {4,5} |
|---|---|---|---|---|---|---|---|---|
| x | 1/2 | 1/2 | 1 | 1 | 1/2 | 1/2 | 1/2 | 1 |

All other edges have x = 0.

**(y, x) ∈ P_A.**
- Degree sums: vertex 0 gets 1/2 + 1/2 = 1 = 2y_0.
  Vertex 1 gets 1 + 1 = 2.
  Vertex 2 gets 1 + 1/2 + 1/2 = 2, and so does vertex 3.
  Vertex 4 gets 1/2 + 1/2 + 1 = 2, and so does vertex 5.
- Every edge value is at most the y-value of both its ends. The two edges at vertex 0 have value 1/2 = y_0.
- All values lie in [0, 1].

**Run A (ends with 3 vertices).**
1. S1 on {4,5}: x = y_4 = y_5 = 1, and the witness is w = 1 (y_1 = 1).
   The new vertex a = {4,5} has y_a = (1/2 + 1/2 + 1/2 + 1/2)/2 = 1.
   Its edges are a–0 = 1, a–2 = 1/2 and a–3 = 1/2.
2. S1 on {1,2}: x = y_1 = y_2 = 1, and the witness is w = 3.
   The new vertex b = {1,2} has edges b–3 = 1 + 1/2 = 3/2 and b–a = 1/2, so y_b = (3/2 + 1/2)/2 = 1.
3. S2 on {b,3}: 3/2 > max{1, 1}.
   The new vertex d = {1,2,3} has the single edge d–a = 1/2 + 1/2 = 1, so y_d = 1/2.

Final graph: vertices 0 (y = 1/2), a (y = 1) and d (y = 1/2), with edges 0–a = 1 and d–a = 1.
No rule applies:
- S1 needs equal end values, and both edges join a value-1/2 vertex to the value-1 vertex.
- S2 needs 1 > max{1/2, 1}, which is false.

**Run B (ends with 4 vertices).**
1. S1 on {1,2}: the witness is 3.
   The new vertex b has edges b–3 = 3/2 and b–5 = 1/2, and y_b = 1.
2. S2 on {b,3}: 3/2 > 1.
   The new vertex d = {1,2,3} has edges d–4 = 1/2 and d–5 = 1/2, and y_d = 1/2.

Final graph: vertices 0 (1/2), d (1/2), 4 (1) and 5 (1).
Its edges are 0–4 = 0–5 = d–4 = d–5 = 1/2 and 4–5 = 1. No rule applies:
- S1 on {4,5} has x = y_4 = y_5 = 1, but the only other vertices, 0 and d, have value 1/2 < 1, so there is no witness.
- Every other edge joins vertices of different values, so S1 cannot apply to it.
- S2 fails on every edge: 1/2 ≤ 1, and 1 ≤ 1.

**Both runs are executions of Algorithm S1S2.**
- Run A selects u = 4 first and scans v = 5 first.
  It then selects 1 and scans 2 first.
  Next it selects b; its neighbour 3 has y_3 = 1 = c, but x = 3/2 ≠ c, so the `else if` branch applies S2.
- Run B selects u = 1 first.
  The heap always contains every current vertex that has not been examined since the last shrink
  next to it. So the remaining pops find no applicable rule, and each run ends when H is empty.
- `../../scripts/verify_346320.py` re-implements Algorithm S1S2 literally, in exact rational
  arithmetic, with explicit selection orders. It reproduces both runs, and its output is in
  `../../outputs/verify-346320.json`.

**Conclusion.** The two final graphs have 3 and 4 vertices (and 2 and 5 edges). They are not
isomorphic under any notion of graph isomorphism, weighted or unweighted. So Conjecture 6.2 fails
for SRK = S1S2. Since S1S2 belongs to the quantified set, the literal MathDB statement fails too. ∎

## Search record

- **Exhaustive sweep.** `../../scripts/shrink_exhaustive.py` enumerates every point (y, x) of P_A on
  n ≤ 6 vertices with y_v ∈ {1/2, 1} and x_e ∈ {0, 1/2, 1}. It finds no failure for any strategy
  when n ≤ 5.
  - For n = 6 it checks 2759 labelled inputs (y sorted), and the only failing strategy is S1S2.
    The witness above is the first S1S2 witness found, and 6 is the minimum order within this
    half-integral class.
  - For n = 7 it completes every class with at least one value-1/2 vertex. That covers 26070
    labelled inputs: 16260, 5550, 2112, 933, 480, 270 and 465 inputs for 1 to 7 value-1/2
    vertices. S1S2 fails again (terminal vertex counts {3,4} and {4,5}). C1, C1C2, C1C2C3 and S1
    do not fail.
  - The all-value-1 class at n = 7 was run separately, in row-0 residue chunks, for C1, C1C2,
    C1C2C3 and S1. It covers 52065 labelled inputs with no failure; the logs are
    `shrinkx7k0-c*`. S1S2 was not run on this class, since it is already refuted.
  - Exhaustive coverage over half-integral points is therefore complete for n ≤ 7 for C1, C1C2,
    C1C2C3 and S1, with no failure. Among the classes searched for S1S2, failures occur at n = 6
    and n = 7.
- **Random samples.** `../../scripts/shrink_sample.py` uses sums of q random cycles with q = 2, 3
  or 4, on 7–10 vertices. The cycles are either Hamiltonian (giving points of the TSP polytope) or
  of mixed length.
  - Mixed-length samples found S1S2 failures at (n, q) = (8, 3), (7, 4) and (9, 3).
  - No sample made any other strategy fail.
  - No sample from the TSP polytope made any strategy fail, including S1S2.
- These searches are diagnostics, not proofs. Whether C1, C1C2, C1C2C3 and S1 are confluent is
  left open.
- **Mechanism.** S2 lowers vertex values (Lemma 4.6), and that can destroy the global witness
  condition "∃ w : y_w ≥ c" of S1. In run B the only remaining value-1 vertices are 4 and 5, so
  {4,5} is stuck. In run A, {4,5} is shrunk while vertex 1 still has value 1.

## Prior-art and subsumption checks (bounded)

- **All versions of the source.** v1–v4 all print the conjecture; v4 is the peer-reviewed final.
  - None of them gives an example, theorem or remark settling it.
  - Theorem 3.9 and Corollary 4.9 are about safety, not confluence.
  - Lemma 4.6 is the source's own fact that S2 lowers values. It is an ingredient here, but the
    source never draws the consequence, and no one-paragraph bridge from the source's own lemmas
    is apparent. The obstruction needs a specific global witness failure.
- **Web searches (2026-11-03).** Searches for Kobeaga/Merino/Lozano together with shrinking,
  isomorphic, counterexample, S1S2, and Conjecture 6.2 found no later discussion or resolution.
  - The later paper by Kobeaga and Merino, "A revisited branch-and-cut algorithm for large-scale
    orienteering problems" (arXiv:2011.02743v2), was fetched to `../../sources2/2011.02743.pdf`
    (receipt alongside) and read at lines 462–485 of the text.
    - It excludes rule S2 "which leads to excessively aggressive shrinking strategies and hence to
      vanish violated CCs in some cases", and keeps only C1C2 and S1 for the orienteering problem.
    - It contains no occurrence of "conjecture" or "isomorph" and does not discuss Conjecture 6.2.
    - The defect it names (losing cover constraints) differs from non-confluence. However, the
      practical relevance of S1S2 is lower than that of C1C2 and S1, and root should weigh this.
  - Kobeaga's 2021 PhD thesis (EHU, handle 10810/51029) was not read; this is an access gap.
- **Not a classical example sitting on a convention boundary.** The difference is in vertex
  count, not in an order or density convention.

## Significance caveats (for root)

- The conjecture is human-posed but heuristic: an operations-research observation drawn from
  computational tables.
- The counterexample is small, and its mechanism (non-confluence caused by a global side
  condition) may be judged routine.
- The strategies C1–S1, the Padberg–Rinaldi-type rules, are not refuted here.

## Lean plan (statement correspondence)

`lean/MathDB346320.lean` (UNCOMPILED) models the process as follows:
- A state is a labelling L : Fin n → Fin n. Its blocks are the current vertices.
- X and Y implement eqs. (16a)–(16d) literally: unmerged blocks use the original y.
- `Move` is exactly the set of pairs on which Algorithm S1S2 shrinks.
- `Step` merges two blocks. `Terminal` says no move is possible, and `Obtained` means reachable
  from the identity labelling and terminal.
- The shrunk support graph is a `SimpleGraph` on the representatives.

The endpoint is `∃ n y x, InPA y x ∧ ¬ ∀ L₁ L₂, Obtained y x L₁ → Obtained y x L₂ → Nonempty
(shrunk x L₁ ≃g shrunk x L₂)`. It is proved by the explicit runs, terminality by `decide`, and
the cardinalities 3 ≠ 4.

Points for the formal reviewer:
- The heap realisability is argued above, not formalised. The formal `Obtained` is the
  rule-level semantics that the conjecture's wording ("ordering of rules and shrinkable sets")
  refers to.
- `decide` over ℚ sums may be slow in the kernel. A fallback is to scale by 2 and work over ℕ,
  with a homogeneity lemma.
