# CANDIDATE 337062: refutation of the seven-class uniform edge betweenness conjecture

Lane: expanded-corpus-r199 (Claude). **No credit is claimed.** Status: ordinary proof (an exact finite computation, checked three ways) plus an UNCOMPILED Lean draft. Root, an independent reviewer and a Sol worker must decide on and compile any endpoint.

## 1. Record and source

- MathDB 337062, "Uniform edge betweenness centrality in seven circulant graph classes". The exact raw line, chunk, one-based line and hashes are in `raw/337062.jsonl`, `extracted.json` and `results.json`.
- Source: H. A. Newman, H. Miranda, R. Flórez, D. A. Narayan, "Uniform edge betweenness centrality", arXiv:1709.04773 (v1 is the only arXiv version; TeX read in `sources/tex/1709.04773/main.tex`).
- Version of record: Electronic Journal of Graph Theory and Applications 8(2) (2020) 265–300, DOI 10.5614/ejgta.2020.8.2.7. The PDF is in `sources/ejgta-567-vor.pdf` (sha256 63a58d5a…). Conjecture 2.1 on p. 279 is identical to arXiv v1.
- Definition 1.1 (version of record): B′_G(e) = Σ_{x,y} σ_xy(e)/σ_xy over ordered pairs of distinct vertices, where σ_xy is the number of shortest x–y paths and σ_xy(e) the number of those containing e. A graph is edge-betweenness-uniform if B′_G(e) is the same for all edges e.
- **Conjecture 2.1.** Each of the following seven classes of circulant graphs has uniform edge betweenness centrality but is not edge-transitive:
  - Class 3: C_{20+8(n−1)}(1, 2n+2, 2n+4)
  - Class 4: C_{32+8(n−1)}(1, 2n+5, 2n+7)
  - Class 5: C_{20+16(n−1)}(1, 4n, 8n+1)
  - Class 6: C_{28+16(n−1)}(1, 4n+4, 8n+5)
  - Class 7: C_{32+8(n−1)}(1, 2n+5, 4n+11)
  - Class 8: C_{32+8(n−1)}(1, 2n+7, 4n+11)
  - Class 9: C_{49+14(n−1)}(1, 2n+6, 4n+9)

  In each class n = 1, 2, 3, …. The MathDB statement matches this literally.

## 2. Result

**Theorem.** G = C_32(1,7,9), the n = 1 member of Class 4, is not edge-betweenness-uniform. Hence Conjecture 2.1 is false.

Exact values (ordered-pair definition):

| edge | step | B′(e) |
|---|---|---|
| {0,1} | 1 | 15169/615 ≈ 24.665041 |
| {0,7} | 7 | 15169/615 |
| {0,9} | 9 | 15172/615 ≈ 24.669919 |

So B′({0,9}) − B′({0,1}) = 1/205.

The failure is not isolated:

- Classes 4, 7 and 8 are pairwise isomorphic for every n by multiplier maps. For example, x ↦ (2n+5)x maps Class 4 onto Class 7 (`outputs/circulant/multiplier-iso.jsonl`, n ≤ 12).
- Exact computation shows Classes 4, 7 and 8 are **non-uniform for every n = 1, …, 60** (m = 32, …, 504).
- Classes 3, 5, 6 and 9 are uniform for every n = 1, …, 60 (`outputs/circulant/ebc-n1-12.jsonl`, `ebc-n13-60.jsonl`).

So exactly one of the four isomorphism-distinct proposed families, C_{8n+24}(1, 2n+5, 2n+7), fails, and it fails at every size tested.

## 3. Ordinary proof

G is the Cayley graph of Z_32 with connection set {±1, ±7, ±9}. It is 6-regular, bipartite (all steps odd), connected, with 96 edges and diameter 4.

From vertex 0 (`outputs/circulant/certificate-C32-1-7-9.json`):

| distance | vertices | σ_{0,y} |
|---|---|---|
| 0 | 0 | 1 |
| 1 | 1, 7, 9, 23, 25, 31 | 1 each |
| 2 | 2, 6, 8, 10, 14, 16, 18, 22, 24, 26, 30 | 3, 2, 4, 2, 2, 4, 2, 2, 4, 2, 3 |
| 3 | 3, 5, 11, 13, 15, 17, 19, 21, 27, 29 | 7, 7, 7, 6, 18, 18, 6, 7, 7, 7 |
| 4 | 4, 12, 20, 28 | 41, 40, 40, 41 |

Translation is an automorphism, so d(x,y) = d(0, y−x) and σ_xy = σ_{0,y−x}.

A shortest x–y path uses an edge e = uv at most once and in one direction. So σ_xy(uv) = σ_xu·σ_vy·[d(x,u)+1+d(v,y) = d(x,y)] + σ_xv·σ_uy·[d(x,v)+1+d(u,y) = d(x,y)]. This is the standard splitting: a shortest path through uv in the direction u→v is a shortest x–u path followed by uv and a shortest v–y path.

Summing σ_xy(e)/σ_xy over the 992 ordered pairs of distinct vertices with these tables gives the values in §2. That evaluation is a finite exact rational computation.

Consistency check: Σ_e B′(e) = Σ_{x≠y} d(x,y), since each shortest path of length d contributes 1/σ_xy to each of its d edges. Here Σ_{x≠y} d(x,y) = 32 · 74 = 2368. By rotation, each step class consists of 32 edges with equal B′, and 32·(2·15169 + 15172)/615 = 2368 ✓.

A uniform G would need B′ ≡ 2368/96 = 74/3 = 15170/615 on every edge, and no edge has that value.

## 4. Verification performed (diagnostics, exact rationals)

1. `scripts/circ_ebc.py`: one Brandes pass from source 0 per graph. By vertex-transitivity, B′ of a step-s edge is the sum of the source-0 dependencies over step-s edges. Covers all seven classes for n = 1..60.
2. `scripts/circ_allpairs.py`: an independent all-pairs method using the splitting formula over unordered pairs, with no symmetry shortcut. For C_32(1,7,9) it gives 15169/1230 and 15172/1230, exactly half the ordered-pair values.
3. `scripts/circ_certificate.py`: the literal ordered-pair sum for the edges {0,1}, {0,7} and {0,9}, plus the Wiener identity check.

Sanity controls: the source's proved family member C_21(1,6) comes out uniform with value 11 (unordered). Class 3, n = 1 (C_20(1,4,6)) comes out uniform at 17/3.

Every run was a capped `python3 -I` process, each well under 1 s (the n = 13..60 scan took 11 s).

## 5. Prior-art and credit screen

- **Version history:** arXiv has only v1. The EJGTA 2020 version of record keeps Conjecture 2.1 verbatim, so there is no retraction or correction.
- **Source-ingredient checks:**
  - The source's own proved theorems (C_{18n±3}(1,6n)) do not touch Classes 3–9.
  - The appendix data in the version of record covers vertex-transitive graphs on 14–21 vertices (pp. 282–300). The smallest Class 4/7/8 graph has 32 vertices, so it is not among the printed data. This is not an evaluation of the source's formula.
  - It is not a modification of a printed example and not a classical extremal graph.
  - The failure is invisible at 3–4 significant digits (24.665 vs 24.670), which is consistent with an authors' floating-point heuristic.
- **Citing work:**
  - Coroničová Hurajová–Madaras–Narayan, "Characterizing edge betweenness-uniform graphs", Theory and Applications of Graphs 9(1) (2022), Art. 5. Only the abstract was read: the PDF returned 403 at digitalcommons.georgiasouthern.edu and again at the core.ac.uk mirror, and neither was retried.
  - **This is an open prior-art gap:** that paper is by an overlapping author set and could mention the classes. Root should obtain it before acceptance (the 363762 lesson).
  - Web searches found no statement that Classes 4/7/8 fail.
  - Lehigh 2019 abstract by co-author H. Miranda (`sources/lehigh-miranda-2019.pdf`, read in full): it names only C_{18n±3}(1,6n) as uniform non-edge-transitive classes and says nothing on Classes 3–9.
- **Registries:**
  - Lean Pool HEAD 01db1d70 (unchanged): no betweenness or circulant-betweenness entries.
  - Omega HEAD 7089bc5f: D5 refetched, Problems unchanged at 24a0aaeb. Circulant hits are unrelated (energy, positivity, covering).
  - OpenAI/math HEAD 4eaee875 (unchanged).
  - 8 GitHub repository queries: no relevant hits. See `outputs/registry-screen.json`.
- **Family checks:**
  - 361332 and 350694 (vertex betweenness-uniform) were never credited (r179: source-refuted; r161: parked) and are a different invariant.
  - The credited circulant result 350979 (monophonic position number) is a different problem. This is not a parameter variant of it.
- **Credit risk: MODERATE.**
  - For: it refutes a refereed journal conjecture; the counterexample is exact and small, with an elementary finite certificate; and it shows a whole proposed family (Classes 4 ≅ 7 ≅ 8) fails throughout the tested range.
  - Against: (a) a single computation, which may be judged a modest-significance correction of numerical work; (b) the unread 2022 follow-up body; (c) "circulants" is on the credited-family watch list (though the problem here is different).

## 6. Statement-correspondence plan (Lean)

- Vertex type `ZMod 32`. Adjacency x ~ y ⇔ x ≠ y ∧ (y − x) ∈ {±1, ±7, ±9}. Mathlib's `SimpleGraph.circulantGraph` can be used if its convention matches; otherwise use an explicit definition with a proved equivalence.
- σ_xy is the cardinality of `G.finsetWalkLength (G.dist x y) x y`. Walks of length dist(x,y) are exactly the shortest paths, and the bridge lemma "walk of length dist ⇒ IsPath" is in Mathlib or short.
- σ_xy(e) is the cardinality of the subset of those walks whose edge list contains e.
- B′(e) is the ℚ-sum over ordered pairs x ≠ y.
- Uniform means ∀ e e' ∈ edgeSet, B′ e = B′ e'.
- The conjecture's negation for this record is ∃ class, n with ¬(Uniform ∧ ¬EdgeTransitive). It suffices to prove ¬Uniform(C_32(1,7,9)) and note that this graph is Class 4 at n = 1 (definitional arithmetic: 32 + 8·0 = 32, 2·1+5 = 7, 2·1+7 = 9).

Proof route:

1. `adjMatrix_pow_apply_eq_card_walk` turns walk counts into matrix-power entries.
2. Prove dist values by exhibiting walks and showing that shorter matrix powers vanish.
3. Prove the splitting lemma for σ_xy(e) (the only general combinatorial lemma).
4. Evaluate the two sums by `decide` or `norm_num` over explicit Nat tables (32×32, powers up to 4).

The splitting lemma can be avoided by computing σ_xy(e) directly with `decide` over `finsetWalkLength` (at most 41 walks per pair). That is heavier on the kernel but needs no new combinatorics.

Draft: `lean/EdgeBetweenness337062.lean` (**UNCOMPILED**, never run in this lane).

Estimated Lean cost: moderate. One bridging lemma plus a medium kernel computation (992 pairs, diameter 4). No analysis is needed.
