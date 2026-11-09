# Independent adversarial review: MathDB 337062 (seven-class uniform edge betweenness conjecture)

Lane: `ebc-review-r1` (Claude Opus 5.5). This is a review, not an acceptance. Credit is zero and only root decides.

**Overall recommendation: HOLD.** The mathematics is correct. I reproduced it exactly with my own code. The one decisive missing item is the body of the 2022 Theory and Applications of Graphs follow-up by an overlapping author set. Every legitimate open route to that body was blocked. Search-engine snippets of that PDF suggest it discusses circulants and "a conjecture". So it may already address Conjecture 2.1. The exact missing evidence is set out in §7.

| Gate | Verdict |
|---|---|
| A. Statement fidelity | **PASS** |
| B. Independent exact mathematics | **PASS** |
| C. Prior art | **QUALIFIED_PASS**: no prior refutation found by any reachable route, but the 2022 TAG body is unread |
| D. Significance and exclusion screen | **QUALIFIED_PASS**: conditional on C |
| E. Lean route | **QUALIFIED_PASS**: a cheap literal endpoint exists, but the draft is not usable as written |

All paths below are relative to `new-twenty-2026-10-31/`. `EC` = `expanded-corpus-r199`, `R` = `ebc-review-r1`.

---

## 0. Inputs and hash binding

- Read-only inputs: 30 files from the discovery lane, hashed before (`R/receipts/input-hashes-before.txt`, 2026-11-05T07:57:59Z) and after (`R/receipts/input-hashes-after.txt`). The two lists are **identical**. Key hashes:
  - `EC/CANDIDATE-337062.md` 32cad475b6585eb472d4f1bb70c33b4586047ac41d95d0f7a1236ceec7732783 (matches the brief)
  - `EC/sources/ejgta-567-vor.pdf` 63a58d5a0626c75a0469835065eabd742a0aba9624baed4da4ec04ce028869a1
  - `EC/sources/tex/1709.04773/main.tex` 6e8c237f9bd11bce1b82d837da74c5367e15eed4ae5c85934592cc2c22536175
  - `EC/raw/337062.jsonl` 9f948bf108389a82f5a64a2621e25b1ebc647fa7c88fa60dc07a317931d43c56
  - `EC/results.json` 80781d8bf9580f0dadf11eb12c4b9eca7c2dfcadc402caa2e17dde8527454994
  - `EC/lean/EdgeBetweenness337062.lean` 7b179ebc14fb72454a31555163bb9c2c8e0fbed1b1de697ae321e306f691ce9a
- I did not import or execute any discovery-lane script. My scripts are in `R/scripts/`.
- My own artifacts are hashed in `R/receipts/own-artifact-hashes.txt`. Network receipts are in `R/receipts/network-receipts.json`.
- I extracted the version-of-record text with `pdftotext -layout` into `R/extract/ejgta-vor.txt` (sha256 14b2b272…). Line numbers "VoR L*n*" below refer to that file.

## A. Statement fidelity: PASS

**Source.** Heather A. Newman, Hector Miranda, Rigoberto Flórez, Darren A. Narayan, "Uniform Edge Betweenness Centrality", arXiv:1709.04773. The TeX author block (main.tex L46–50) gives "Heather A. Newman, Hector Miranda, Rigoberto Fl\'{o}rez, Darren A. Narayan". The version of record is Electron. J. Graph Theory Appl. 8(2) (2020) 265–300, DOI 10.5614/ejgta.2020.8.2.7 (VoR L1, L30). It was received 28 February 2018, revised 9 February 2020 and accepted 17 February 2020 (VoR L40). The VoR prints the name "Flrez" (a font glyph loss) and "Heather Newman".

**Definition 1.1** (VoR L52–60; main.tex L83–92, unnumbered there), quoted exactly:
> The edge betweenness centrality of an edge e in a graph G, denoted B′_G(e) (or simply B′(e) when G is clear), measures the frequency at which e appears on a shortest path between two distinct vertices x and y. Let σ_xy be the number of shortest paths between distinct vertices x and y, and let σ_xy(e) be the number of shortest paths between x and y that contain e. Then B′_G(e) = Σ_{x,y} σ_xy(e)/σ_xy (for all distinct vertices x and y).

**Definition 1.2** (VoR L63–64; main.tex L94–97):
> A graph G has uniform edge betweenness centrality, or is edge-betweenness-uniform, if B′_G(e) has the same value for all edges e in G.

**Pair convention.** The sum is over ordered pairs. VoR L66–68 (main.tex L99–102) says: "We note that, for undirected graphs, shortest paths from x to y are regarded as the same as shortest paths from y to x, though the associated contribution to the sum B′_G(e) is double-counted."

- There is no normalization.
- Endpoints count: pairs with x or y an endpoint of e are included. Lemma 1.1 (VoR L73; main.tex L104–108) gives the lower bound 2 ≤ B′_G(e), which is attained only because the pairs (u,v) and (v,u) of the edge itself each contribute 1.
- The appendix values confirm the ordered convention. For example, VoR L795–797, entry 2 on 12 vertices with 18 edges, has values 13.3333 and 17.3333 whose sum 264 is twice the Wiener index.

**Scaling invariance (confirmed).** Unordered sums are exactly half of ordered sums, because σ_xy(e)/σ_xy is symmetric in x and y. So uniformity is the same under either convention.

- My all-pairs code works over ordered pairs. The discovery lane's unordered values (15169/1230 and 15172/1230) are exactly half of mine.
- I also tested a stricter variant that excludes pairs having x or y in e. C_32(1,7,9) is still non-uniform under it, with values 7379/1230 and 3691/615 = 7382/1230. So no reading of "between two distinct vertices" rescues the conjecture.

**Circulant definition** (main.tex L247–252; VoR p. 268):
> A circulant graph C_n(L) is a graph on vertices v_1, …, v_n where each v_i is adjacent to v_{(i+j) mod n} and v_{(i−j) mod n} for each j in a list L.

My code builds exactly this graph on Z_m.

**Conjecture 2.1** (VoR L676–695, on p. 279: the page footer "279" is at VoR L714). The arXiv TeX has it unnumbered at main.tex L969–982. Quoted exactly:
> We have identified seven other infinite classes which we believe have the same unusual combination of properties. We pose these as open problems.
> Conjecture 2.1. The following classes of circulant graphs have uniform edge betweenness centrality but are not edge-transitive:
> - Class 3: C_{20+8(n−1)}(1, 2n+2, 2n+4), n = 1, 2, 3, …
> - Class 4: C_{32+8(n−1)}(1, 2n+5, 2n+7), n = 1, 2, 3, …
> - Class 5: C_{20+16(n−1)}(1, 4n, 8n+1), n = 1, 2, 3, …
> - Class 6: C_{28+16(n−1)}(1, 4n+4, 8n+5), n = 1, 2, 3, …
> - Class 7: C_{32+8(n−1)}(1, 2n+5, 4n+11), n = 1, 2, 3, …
> - Class 8: C_{32+8(n−1)}(1, 2n+7, 4n+11), n = 1, 2, 3, …
> - Class 9: C_{49+14(n−1)}(1, 2n+6, 4n+9), n = 1, 2, 3, …

The arXiv v1 and VoR texts of the conjecture are identical. The only VoR change in that region is that the acknowledgements add thanks to a referee (VoR L697–700).

**MathDB literal** (`EC/raw/337062.jsonl`, statement sha256 6386883c…). It lists the same seven (order, steps) formulas with n = 1, 2, 3, …, and the same conjunction "uniform edge betweenness centrality but is not edge-transitive". The record matches the source literally. Two points carry no weight:

- MathDB omits the class labels 3 to 9.
- MathDB says "the proved class C_{18n+3}(1,6n)". The source proves both C_{18n−3}(1,6n) and C_{18n+3}(1,6n), at main.tex L767–768 and L965–966.

**Did the source verify Class 4, 7 or 8?** No printed verification exists.

- The authors used "Wolfram Mathematica 11 code for betweenness testing" (VoR L162 and L185; main.tex L216 and L261).
- The appendix (VoR L784 onward, pp. 282–300) lists only vertex-transitive graphs on **12, 13, 14 and 15 vertices**. Its section headers are at VoR L790, L1025, L1086 and L1344.
- The appendix prints floating-point values to 6 significant digits, for example "13.3333" and "2.72727".
- No graph on 32 or more vertices appears, and the classes are asserted with no data at all.

**Correction to the dossier.** `EC/CANDIDATE-337062.md` §5 says the appendix covers "vertex-transitive graphs on 14–21 vertices". That is wrong: it covers 12–15.

The dossier also suggests the failure is "invisible at 3–4 significant digits", consistent with a floating-point heuristic. That is speculative. At the 6-digit precision the authors actually print, 24.6650 and 24.6699 differ, as do the unordered values 12.3325 and 12.3350. How the authors reached the conjecture for Classes 4, 7 and 8 is unknown. It is not explained by printed precision.

## B. Independent exact mathematics: PASS

I wrote my own code. All of it uses exact `fractions.Fraction`, runs one process per call under `ulimit -v 2000000; timeout 100 python3 -I`, and each run took well under 12 s.

- **`R/scripts/ebc_exact.py`** applies two methods to every edge and every ordered pair, with no symmetry shortcut:
  - **M1**: BFS distance and path-count tables from every vertex, combined with the splitting formula σ_xy(uv) = σ_xu σ_vy [d_xu + 1 + d_vy = d_xy] + σ_xv σ_uy [d_xv + 1 + d_uy = d_xy].
  - **M2**: literal depth-first enumeration of every shortest path of every ordered pair, counting edge occurrences directly. It uses no splitting formula.

  It also checks the Wiener identity Σ_e B′(e) = Σ_{x≠y} d(x,y).
- **`R/scripts/sweep.py`** is a single-source, translation-reduced exact method for all seven classes. For an edge {0,s}, B′({0,s}) = Σ_{t∈Z_m} δ_0({t, t+s}), counted with multiplicity. It also searches for multiplier isomorphisms.
- **`R/scripts/typo_screen.py`** checks every 6-regular connected C_m(1,a,b) for uniformity.

### Results

**C_32(1,7,9)** (Class 4, n = 1) is 6-regular, with 96 edges and diameter 4.

- M1 and M2 agree on every edge, and M2's path counts agree with the BFS σ on every ordered pair.
- The ordered-pair Wiener sum is 2368, and the identity check holds.
- There are 9216 shortest paths over the ordered pairs (`R/logs/run1-exact-n1-controls.log`, `R/outputs/exact-n1-controls.json`).

| step class (32 edges each) | B′ (ordered) |
|---|---|
| 1 | 15169/615 ≈ 24.665041 |
| 7 | 15169/615 |
| 9 | 15172/615 ≈ 24.669919 |

The two distinct values differ by **1/205**, so the graph is **not** edge-betweenness-uniform. The uniform value would have to be 2368/96 = 74/3 = 15170/615, which no edge attains. My σ_{0,y} table from vertex 0 (`R/logs/run8-extract-tables.log`) matches the dossier's §3 table entry for entry, including 41, 40, 40, 41 at distance 4.

**C_40(1,9,11)** (Class 4, n = 2) has diameter 5. Its values are 270635/7381 for steps 1 and 9 and **270640/7381** for step 11, a difference of 5/7381. M1 and M2 agree on every edge (`R/logs/run3-exact-C40-enumerated.log`). It is **non-uniform**.

**Class 7 and Class 8 at n = 1.** Class 7 is C_32(1,7,15) and Class 8 is C_32(1,9,15). Each has the same two values, 15169/615 and 15172/615. The odd step class is 1 for Class 7 and 15 for Class 8. M1 and M2 agree. At n = 2, C_40(1,9,19) and C_40(1,11,19) have the same two values as C_40(1,9,11) (`R/logs/run2-exact-classes-n1-n2.log`).

**Multiplier isomorphisms** (`R/outputs/sweep-n1-12.json` and `sweep-n13-30.json`). For every n = 1..30 the three connection sets are pairwise distinct, and units k exist with k·(±L_4) = ±L_7, k·(±L_4) = ±L_8 and k·(±L_7) = ±L_8. The smallest multipliers are k = 2n+5 (4→7), k = 2n+7 (4→8) and k = 4n+11 (7→8, n ≥ 1).

I also verified the 4→7 multiplier by hand for every n. Let m = 8(n+3) and k = 2n+5. Then (2n+5)² = 4(n+2)(n+3) + 1, which is 1 mod m if n is even and 4n+13 ≡ −(4n+11) if n is odd. Also (2n+5)(2n+7) = 4(n+3)² − 1, which is 4n+11 if n is even and −1 if n is odd. So k·{±1, ±(2n+5), ±(2n+7)} = {±1, ±(2n+5), ±(4n+11)}. The 4→8 case is analogous with k = 2n+7. Multiplication by a unit is a graph isomorphism of circulants, so Classes 4, 7 and 8 are the same graph family up to isomorphism.

**Sweep, n = 1..30.** All 210 graphs are connected and 6-regular, and every Wiener check holds.

- Classes 3, 5, 6 and 9 are uniform for every n ≤ 30.
- Classes 4, 7 and 8 are non-uniform for every n ≤ 30.

This agrees with the discovery lane's claim for n ≤ 60 on the sub-range I checked. I did not re-run n = 31..60.

**Uniform controls.**

- The source's proven C_21(1,6) is uniform with value 22 ordered, which is 11 unordered and matches the dossier.
- C_15(1,6) is uniform with value 13.
- Class 3 at n = 1, C_20(1,4,6), is uniform with value 34/3, which is 17/3 unordered and matches the dossier.
- C_28(1,6,8), C_20(1,4,9), C_36(1,8,17), C_28(1,8,13), C_44(1,12,21), C_49(1,8,13) and C_63(1,10,17) are all uniform.

**Typo-sensitivity screen** (`R/logs/run6-typo-screen.log`). I tested all 91 connected 6-regular C_32(1,a,b) and all 153 connected 6-regular C_40(1,a,b). **None** is edge-betweenness-uniform.

- Every connected circulant on 32 vertices has an odd step, which is a unit, so it is multiplier-equivalent to one containing step 1. Hence **no 6-regular connected circulant on 32 vertices is edge-betweenness-uniform**.
- No misprint in the steps of Class 4, 7 or 8 at n = 1 can rescue the conjecture.
- The screen works: the controls at m = 20 and 28 return exactly the known uniform graphs, including Classes 3, 5 and 6 (`R/logs/run7-typo-screen-control.log`).
- Classes 7 and 8 are separately printed lines that fail identically, so a single-typo explanation is implausible.

**Process disclosure.** In run 2, the output was piped into a small second `python3 -I` formatter, which ran concurrently and outside the `ulimit` wrapper. Several trivial JSON-printing `python3 -I -c` one-liners also ran after downloads, outside the wrapper. All were tiny. No Lean, lake, leanchecker or SAT/ILP binary was run.

## C. Prior art: QUALIFIED_PASS

**Follow-up identified exactly.** Jana Coroničová Hurajová, Tomáš Madaras and Darren A. Narayan, "Characterizing Edge Betweenness-Uniform graphs", *Theory and Applications of Graphs* 9(1) (2022), Article 5, DOI 10.20429/tag.2022.090105, posted March 24, 2022 (OpenAlex W4220696407). Narayan is a co-author of the source.

The abstract (DOAJ API record, OpenAlex, and `EC/sources/tag-vol9-iss1-5.txt`) says only: "It was recently shown by Madaras, Hurajová, Newman, Miranda, Flórez, and Narayan that … only four graphs are edge betweenness-uniform but not edge-transitive. In this paper we present new results involving properties of betweenness-uniform graphs."

**Every open route I tried for its body:**

| Route | Result |
|---|---|
| Journal PDF `digitalcommons.georgiasouthern.edu/cgi/viewcontent.cgi?article=1219&context=tag` (the only full-text location OpenAlex knows; `any_repository_has_fulltext: false`) | **403 Cloudflare challenge**. Not retried; host abandoned |
| DOAJ API record | metadata only; its full-text link points back to the denied host |
| Wayback Machine availability API | **429**. Not retried |
| arXiv | no arXiv version: the arXiv-domain web search finds none, OpenAlex lists none, and a guessed author listing returned 404 |
| NSF PAR | holds only the 2020 EJGTA paper (PAR ID 10252270), not the TAG paper |
| Slovak library catalogue record (dk.fchpt.stuba.sk) | connection failed; not retried |
| core.ac.uk | not attempted: it 403'd the discovery lane |
| ResearchGate | barred by the brief |

**Material warning signal.** Web-search engines have indexed the TAG PDF text. Two independent extended searches returned summaries saying the PDF excerpt "mentions a conjecture about circulants and a theorem confirming one case". They also mention circulants "on vertices in circular distance 6n−1" that are "edge betweenness-uniform and neither edge-transitive nor distance regular".

These are machine summaries of truncated snippets, not primary text, and I could not verify them. The "6n−1" item may simply restate the source's C_{18n±3}(1,6n) theorems. But they raise a real possibility that the 2022 paper discusses Conjecture 2.1: it might prove one class, or report that some classes fail. This is the precise gap that must be closed.

**Citing works.** OpenAlex lists four works citing W2756009780, which merges the arXiv and EJGTA records:

1. Weng et al., ICDE 2023: ego-betweenness on bipartite graphs, an applied and different measure. I read the abstract.
2. Hartman–Pokorná 2021, arXiv:2105.06777: vertex betweenness-uniform graphs from trees.
3. The TAG 2022 paper above.
4. Niveditha–Bhat–Hanif 2026, Arab J. Basic Appl. Sci.: total EBCM equals the Wiener index. I read the abstract; it is unrelated to the classes.

The TAG paper's own resolved reference list (13 of 14 entries) contains no other circulant or edge-betweenness paper beyond Gago–Hurajová–Madaras 2013 and the source itself.

**Web search** (8 queries, listed in the receipts). I found no statement anywhere that Class 4, 7 or 8 fails or that Conjecture 2.1 is false.

**Registries.**
- Lean Pool HEAD is `01db1d7049cf9668bda1e9e106875ee1278b43e6` (2026-10-07), unchanged.
  - The recursive tree has 25038 entries and is not truncated. No path matches betweenness, circulant, centrality or shortest path.
  - `LeanPool/projects.yml` has 3 unrelated keyword hits. The candidates files (`discovered.yml`, `decisions.jsonl`, `shortlist.md`, queues, `manual.txt`) have only unrelated hits: Narayana numbers, Hilbert betweenness axioms and Newman polynomials.
- GitHub: 4 spaced, unauthenticated repository queries. Three returned 0 results. "betweenness-uniform" returned 238 noise results, none relevant.
- OEIS and other tables: no relevant table of edge-betweenness-uniform circulants is known to me, and none surfaced in the searches.

**Verdict.** No public refutation was found, and the source has not been revised. But the single most relevant document, by an overlapping author and two years after the conjecture, is unread. Its indexed text appears to touch circulant conjectures. Prior art is therefore not cleared.

## D. Significance and exclusion screen: QUALIFIED_PASS (conditional on C)

**Arguments for credit:**
- It is a genuine refutation of a refereed journal conjecture that the authors stated as believed after computer exploration ("We have identified seven other infinite classes which we believe…").
- The counterexample is the smallest member of a printed class: C_32(1,7,9), with 32 vertices and 96 edges.
- The certificate is exact and finite: 992 ordered pairs, diameter 4, with an explicit rational gap of 1/205.
- It matches the qualifying precedent type: a small exact, computer-found counterexample to a published conjecture.

**Exclusion checks:**
- **Known result or public refutation:** none found, but this depends on the unread TAG 2022 body (see C).
- **Evaluating the source's own formula:** no. The source gives no formula for these classes and no data beyond 15 vertices.
- **Contradicted by the source's own results:** no. The proved families C_{18n±3}(1,6n) are 4-regular 2-circulants and do not overlap Classes 3–9.
- **Withdrawn or replaced:** no. The 2020 VoR repeats the 2017 statement verbatim after peer review. Whether 2022 replaced it is unknown (see C).
- **Wording, domain or endpoint correction:** no.
  - The failure is robust to ordered versus unordered pairs and to excluding endpoint pairs.
  - No 6-regular circulant on 32 vertices is uniform, so a step typo cannot rescue it.
  - Two other independently printed classes, 7 and 8, are isomorphic to Class 4 and fail identically.
- **Generic failure of a heuristic, routine corollary, or short augmentation:** no.

**Weaknesses root should weigh:**
- Only one of the four isomorphism-distinct families fails; Classes 3, 5, 6 and 9 hold for n ≤ 30. So the refutation removes one family (4 ≅ 7 ≅ 8) from a seven-line conjunction. Mathematically, the conjecture is false because of the 4/7/8 family.
- The "is not edge-transitive" half is untouched. A non-uniform graph is automatically not edge-transitive.
- The computation is elementary. Significance is moderate: it corrects an unverified computational claim in a modest journal. But it is still a clean disproof of a stated conjecture, which the campaign's precedents have treated as qualifying.

## E. Lean route: QUALIFIED_PASS

**Cheapest literal endpoint.** State `Conjecture : Prop` over all seven classes and all n ≥ 1, and prove `¬ Conjecture` from `¬ EdgeBetweennessUniform (C_32(1,7,9))`. Here `classData 4 1` reduces to (32, 1, 7, 9) by `rfl`, since 32 + 8·0 = 32, 2+5 = 7 and 2+7 = 9. The required pieces:

1. Vertices `ZMod m`, using Mathlib's `SimpleGraph.circulantGraph s := fromRel (· - · ∈ s)`. I checked Mathlib master `Mathlib/Combinatorics/SimpleGraph/Circulant.lean`, sha256 3b656b56…. `fromRel` symmetrizes and drops loops, which matches the source's ±j adjacency. Mathlib also provides `circulantGraph_adj_translate`.
2. σ_xy as the number of shortest paths. Fidelity is best served by defining it **literally** as paths, `w.IsPath` with `w.length = G.dist x y`, and proving that this equals `finsetWalkLength (G.dist x y)`, since every walk of length `dist` is a path.
3. σ_xy(e) by filtering on `e ∈ w.edges`.
4. B′ as the ℚ-sum over ordered pairs x ≠ y.
5. Uniformity as a ∀ e, e′ ∈ edgeSet equality.
6. Edge-transitivity via `G ≃g G` acting through `Sym2.map`.
7. The finite bridge: (a) a distance and σ table from vertex 0 (diameter 4), transported by translation; (b) the splitting lemma; (c) two 992-term exact sums over a common Nat denominator. The lcm of the σ values {1, 2, 3, 4, 6, 7, 18, 40, 41} is 103320.

**Estimated cost: moderate.** No analysis is involved. The dominant risk is kernel performance. Direct `decide` on `finsetWalkLength` over all 992 pairs would build around 10⁵–10⁶ walk objects in the kernel, which is probably infeasible without `native_decide` (forbidden). So the splitting-lemma plus translation route, or a small verified reflective checker, is needed. My rough estimate is 500–1500 lines of Lean and one Sol worker cycle or two.

**Assessment of the uncompiled draft** (`EC/lean/EdgeBetweenness337062.lean`, 103 lines, never compiled):

- Definitions are faithful in shape:
  - L21–23 `sigma`, L26–28 `sigmaEdge` and L31–34 `edgeBetweenness` correctly sum over ordered pairs, with y ∈ univ.filter (· ≠ x).
  - L37–38 uniformity and L41–42 edge-transitivity are correct.
  - L50–58 `classData` matches all seven classes, checked line by line against VoR L683–695.
- **Blocking defect 1 (L66).** `haveI : NeZero d.1 := sorry` sits inside the `Conjecture` definition itself, so the statement contains a `sorry`. It must be replaced by a proof that `(classData c n).1 ≥ 20` for c ∈ {3, …, 9}, which is a case split plus `omega`, or the orders must be written as explicit successors.
- **Blocking defect 2 (L82–86).** The two value theorems, which carry the entire mathematical content, are `sorry`.
- **Smaller sorries.** L90–91 (adjacency facts) and L101 (the `classData 4 1` instance transport) are easy. `NeZero` is a Prop, so the instance terms are proof-irrelevant.
- **Risks:**
  - L46–47 builds `circulantGraph` on a `Set` literal. Its `DecidableRel` instance needs `DecidablePred (· ∈ {a,b,c})` for a Set, which may elaborate to classical decidability and block `decide`. A coerced `Finset` is safer.
  - `G.dist` is noncomputable, so every evaluation must go through proved distance lemmas.
  - The Mathlib pin may differ from master.
  - The proof plan in L73–81 is sound but its `decide`-only alternative is unrealistic.

## 7. Recommendation: HOLD

**Exact missing evidence.** The full text of J. Coroničová Hurajová, T. Madaras, D. A. Narayan, "Characterizing Edge Betweenness-Uniform graphs", Theory Appl. Graphs 9(1) (2022), Art. 5, DOI 10.20429/tag.2022.090105. The only known copy is `https://digitalcommons.georgiasouthern.edu/cgi/viewcontent.cgi?article=1219&context=tag`, which is behind a Cloudflare challenge. The supplemental reference file `ref_tag2022090105.pdf` (166 kB) is on the same host. Root must establish:

1. whether the paper mentions Conjecture 2.1 of Newman–Miranda–Flórez–Narayan, Classes 3–9, or the circulants C_{32+8(n−1)}(1, 2n+5, 2n+7), (1, 2n+5, 4n+11) or (1, 2n+7, 4n+11);
2. whether it states, proves, corrects or refutes any of those classes, in particular whether it reports that C_32(1,7,9) or Classes 4, 7 and 8 are not uniform;
3. what its "conjecture about circulants" and "theorem confirming one case" are (search-snippet claims, unverified).

Root can obtain the text by a legitimate route this lane cannot use: for example, the user opening the PDF in a browser, or an authorized, non-automated copy.

**How to resolve:**
- If the paper is silent on Classes 4, 7 and 8, or only proves or discusses other classes, → **PROCEED** to Lean along the route in §E, fixing the L66 statement `sorry` first.
- If it already reports the failure of Class 4, 7 or 8, or replaces Conjecture 2.1, → **EXCLUDE** as publicly refuted, withdrawn or replaced.

**Dossier corrections for root**, which do not change the mathematics:
- The VoR appendix covers 12–15 vertices, not 14–21.
- The floating-point explanation for the authors' error is unsupported at their printed 6-digit precision.

I do not self-accept. Root decides.
