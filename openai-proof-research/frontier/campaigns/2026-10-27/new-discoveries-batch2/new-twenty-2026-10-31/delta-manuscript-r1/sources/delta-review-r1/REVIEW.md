# Independent adversarial review of MathDB 352253

Recommendation: **PROCEED to Lean formalisation**, with the chain proof replaced as specified below. This is not acceptance, a completed formal refutation, or a significance ruling by root. Credit remains zero. Review date: 2026-11-04 UTC. No child agents were used.

| Gate | Verdict | Finding |
|---|---|---|
| A: statement fidelity | QUALIFIED_PASS | The ordinary counterexample survives the illustrated source definition, including vertex coincidences. The discovery lane's proposed incidence bridge does not. |
| B: source-internal overlap | PASS | None of the seven printed Figure 14 gadgets occurs in G′ under the checked interpretation. The source does not supply the doubled-input/pure-minimum bridge. |
| C: independent mathematics | PASS | Complete independent DAG, all move legalities, and a stronger chain search checked; all 25 labelled minima are chain-free and nonminimal. |
| D: prior art | QUALIFIED_PASS | No resolution located in the bounded current searches; important coverage limits below. |
| E: significance and Lean | QUALIFIED_PASS | More than a printed-gadget instance; feasible finite formal endpoint, but the present partial Lean chain theorem is inadequate. Root decides significance. |

## A. Literal target and fidelity

The source is **Shannon Jeffries and Karen Yeats, A degree preserving delta wye transformation with applications to 6-regular graphs and Feynman periods**, arXiv:2110.07764v2; journal Ann. Inst. H. Poincaré D 11 (2024), 641–682, DOI 10.4171/AIHPD/172. References below use the existing read-only `expanded-corpus-r153/sources/delta-journal.txt`, with one-based lines. The Figure 14 page was rendered independently to `tmp/journal-678.png` and visually inspected.

Lines 121–125 exclude loops but allow parallel edges. Definition 2.1, lines 194–204, removes a 6-valent centre having three distinct double connections, adds one edge between each pair of its neighbours, and permits the inverse on any triangle, removing one edge per pair. A connection comprises **all** edges between two vertices (227–238); doubly adjacent means multiplicity exactly 2. There is no bound of 2 on multiplicities elsewhere. The matrices and my independent operations match these definitions.

“Minimal” means minimum **vertex count in the equivalence class**, whereas “minimum” additionally minimizes connections among minimal graphs (1140–1144). Equivalence allows both operations (Section 4 introduction, 767–773), not just reductions. Conjecture 5.1 (1559–1573, journal p. 678) first minimizes over all *pure* YY–Δ sequences and then asserts the chain criterion for the selected G′. The nine-move witness therefore establishes nonminimality in precisely the required sense. No proof that order 10 is the global minimum is needed.

The 18-vertex input is a doubled simple cubic graph. The full pure DAG minimum is 11, attained by reductions `[0,0,3,4,6,7,11]`; this is a legitimate smallest G′, not merely an irreducible terminal graph. All 25 labelled pure-minimum results fail the criterion, so choosing a different pure minimum does not rescue the statement.

The verbal chain must be read with the first-column diagrams 14(a), (b), (d), as the source itself instructs (1566–1573). For one triangle these diagrams require two end base vertices, each with two single triangle edges and two double attachments. For longer chains each internal base consumes four triangle edges and one double attachment. The degree-6 condition and edge distinctness force the base vertices to be distinct: identifying two would require 12 incident edge ends at one 6-valent vertex. Apex and attachment vertices may coincide freely when capacities permit. The end-vertex condition (four neighbours, no connection greater than 2) prevents collisions of an end's attachment vertices with each other or its triangle vertices. Consequently its actual row has type `[1,1,2,2]`.

**The important objection:** internal base vertices need not have actual row type `[1,1,1,1,2]`. An internal double attachment can coincide with an apex and create a triple connection. Thus `Delta153.lean:63–69` and discovery `scripts/chains.py:4–20` are restricted tests; their use as the claimed general bridge is unjustified. My schematic positive control (`recomputation.json:alias_control`, script 180–187) has two triangles, an internal triple connection, and a valid edge-distinct chain; the lane's internal test rejects its middle vertex.

This defect does **not** defeat the candidate. I implemented an edge-capacity search (`scripts/recompute.py:143–179`) that reserves every schematic edge, permits all apex/attachment coincidences, and makes no internal row-type restriction. It finds no chain in G′ or any of the 25 minima. This covers the faithful illustrated definition; a reading which discards the diagrams and permits arbitrary triangle networks is not the source's stated criterion.

There is also a short local ordinary proof for G′, suitable for formalisation. The only possible end bases are 3 and 6. Their single triangle neighbours are 1 and 8, whose connection has size 3. Any first triangle must therefore be `(3,1,8)` or `(6,1,8)` (up to orientation). The next base is 1 or 8, neither an end. After consuming that triangle, its only available double attachment uses the other two edges of the 1–8 connection. Starting at 6 leaves possible forward neighbours 3 and 4, which have no edge between them. Starting at 3 leaves 4 and 6, whose connection has size 2. Neither can serve as the next internal base: after this second triangle, vertex 4 has no available double connection; vertex 6 also has none because its double connection to the starting base 3 was already used as an attachment. Neither can terminate the chain: vertex 4 is not an end, and vertex 6 would reuse its already consumed double attachment to 3. The cases with 1 and 8 interchanged are identical. This replaces the incorrect “cannot even leave an endpoint” explanation.

The brief's Conjecture 4.8 is indeed the preprint's non-bipartite lower bound (`352253.txt:1103–1109`). In the journal it is **Conjecture 4.9** (1236–1241); journal 4.8 is a proposition about bipartite inputs. The present order-10 graph meets the non-bipartite bound n/2 + 1 for n = 18. It does not refute that neighbouring conjecture.

## B. Source-internal check and Figure 14

Sections 4.3–4.4 were read, not inferred from the abstract. Section 4.3 defines minimality and proves only an upper bound in the bipartite case (1211–1234). Section 4.4 proves simple 6-regular graphs minimal and studies their equivalence classes (1296–1468). It does not imply that all pure minima of doubled cubic inputs are simple. G′ has triple connections, so the simple-class results, including Lemma 4.16, cannot be applied to it.

The source openly says that non-chain Figure 14 gadgets reduce arbitrary graphs (1525–1530, 1550–1573). That alone is not a source-internal contradiction: it neither produces one as a pure minimum of a doubled cubic input nor proves its occurrence there without a chain. Its last paragraph explicitly identifies this as the extra content of Conjecture 5.1. The printed finite-simple examples are likewise not counterexamples. I found no already printed doubled-input/pure-minimum counterexample in the inspected sections.

I transcribed 14(c), (e), (f), (g) from the rendered figure into weighted-edge templates (`recompute.py:79–114`). The matcher permits noninjective vertex maps but requires distinct edges, checks multiplicity capacities, and enforces the degree budget under vertex identifications. None embeds in G′. The stronger chain check excludes (a), (b), (d), and every longer first-column chain. This is specifically a check of the seven printed examples, not a classification of the source's unlisted infinite family of gadgets.

The nine-move trace is not one printed gadget executed inside the initial G′. Its first expansion `(0,5,7)` and fourth operation (removal of the vertex that expansion introduced) form a commuting inverse detour around the expansion/reduction involving vertex 6. Deleting that detour gives this independently checked seven-move witness, using current indices:

```
expand (1,6,8); reduce 6;
expand (4,7,10); expand (3,7,10);
reduce 10; reduce 7; reduce 9.
```

Orders are 11 → 12 → 11 → 12 → 13 → 12 → 11 → 10. The original nine-move trace does create printed gadgets temporarily: after its second operation, template (c) embeds with schematic `(L,R,top,bottom) = (1,8,4,3)`, double attachments `L→12, R→12, bottom→2, bottom→6`; template (g) also embeds. The attachment coincidence at 12 is legal. Template (g) remains after the next reduction, then none of the four non-chain printed templates appears after the fourth operation. These facts locate the source ingredients without misdescribing G′ itself as a printed example. The full mappings are saved in `figure_matches_along_trace`.

## C. Independent recomputation

Only my own script was executed. Discovery scripts were read after the initial independent recomputation and were never imported or run. The initial matrix was rebuilt from the explicit 27-edge list, not taken as the computational starting point from the lane's certificate. It was compared with the supplied original matrix as an input consistency check.

`recompute.py:5–58` defines both operations from Definition 2.1, asserts symmetry, looplessness, nonnegative multiplicities and row sum 6 at every generated step, visits every legal pure successor, and exhausts the worklist. Counts by order are:

| Order | States |
|---|---:|
| 18 | 1 |
| 17 | 18 |
| 16 | 126 |
| 15 | 435 |
| 14 | 777 |
| 13 | 688 |
| 12 | 258 |
| 11 | 25 |

Total 2,328 states; 9,846 directed move arcs, counting legal moves even when successors coincide. No symmetry quotient is used. Exhaustion plus closure proves the lower bound for every pure sequence by induction on its length. The displayed seven pure reductions attain it. The independent-set diagnostic gives independence number 7 and 25 maximum independent sets; it is **not** substituted for the DAG proof.

Every supplied nine-move step is legal and reaches order 10; the shorter witness is also checked. All 25 minima are chain-free under the stronger capacity search. Every one is nonminimal: reverse its pure path to the original, follow the displayed pure path to G′, then use the shrinking witness. This conclusion needs no separate random search from the other minima.

The machine-readable result, including matrices, traces, controls and mappings, is `recomputation.json`. Full computational output is `logs/recompute.log`. The initial restricted diagnostics remain labelled as such in the script and JSON; the authoritative chain fields are `faithful_chain_Gprime`, `faithful_chains_all_minima`, and `faithful_chain_free_minima`.

## D. Bounded prior-art investigation

Current network receipts, raw bodies, SHA-256 hashes, dates and final URLs are in `downloads/request-*/receipt.json`; command output is in `logs/fetch-review*.log`. Each request used a fresh empty lane-local directory and normal TLS verification. No forbidden service was queried; there was no 403/429/challenge retry. One guessed author-publications URL returned 404; the author's linked research page was then used.

* arXiv abs/2110.07764 still reports v2, 27 July 2022. The current math.CO listing, Yeats's author listing, and a Jeffries author search were fetched. The latter returned the source paper; the former lists later work under Rowan Yeats, including October 2026 papers on posets and spanning forests. The author's home page explicitly identifies the former publication name, so searching only the old name would have been inadequate. The linked research list contains the source and no announced resolution of these conjectures.
* OpenAlex identifies the source as W3206968406. Its citing-work query returned exactly two works: Schnetz, **ϕ3 theory at six loops** (2025; arXiv:2505.15485), and Gitler–Sandoval–Angeles, **On Delta-Wye Reducibility of Toroidal Graphs** (2026). The former's downloaded primary text concerns renormalization computations and cites Jeffries–Yeats as reference [20], not a chain-criterion resolution. The latter's publisher abstract, obtained in the initial web search, concerns ordinary delta-wye forbidden minors on the torus, not the degree-preserving YY operation; its full body was not inspected.
* The OpenAlex author query returned 22 works from 2022 onward. I additionally downloaded the relevant Panzer–Yeats **Feynman symmetries of the Martin and c₂ invariants of regular graphs**, arXiv:2304.05299. Its Section 7.2 (`downloads/request-016/text.txt:3662–3790`) concerns Martin sequences of doubled cubic graphs and period identities; its conjectures are not the YY chain criterion. No Conjecture 5.1/4.8 resolution was found in that body. Other author papers were title/list screened, not exhaustively read.
* Live OpenAI/math HEAD was `4eaee87548250b2682affda7d05d947c05554bae`, dated 2026-10-30, matching the discovery lane's saved head and complete preprints tree. Current Omega HEAD was `8e15c484cf5786fe69fef0627fd84a63cfeb5942`, dated 2026-11-04 08:25:41 UTC, newer than the discovery lane's snapshot. Its fresh complete D5 tree has 13,912 paths and Problems tree 1,717 paths, both untruncated. Path screening found no Jeffries/Yeats/352253/wye counterpart; unrelated delta-named paths are listed in `logs/inspect.log`. This is path-level screening, not a statement-level audit of every registry theorem.
* Exact-title, author/conjecture, counterexample, and MathDB-ID searches located the source, not a resolution. The second search's full tool result is saved as `logs/web-search.json`; the initial search returned the toroidal article's publisher abstract and the source. A negative search is not worldwide novelty proof.

These limits justify QUALIFIED_PASS, not unconditional novelty clearance. In particular, sparse OpenAlex citations and lack of a path-name match cannot prove absence of an obscure theorem or unpublished counterexample. No later public resolution or directly subsuming theorem was located.

## E. Significance and literal Lean route

The source's brute-force method and the discovery search are related in the unavoidable sense that both use the source's moves. The discovery code (`scripts/delta.py:43–69`, read only) generates random simple cubic graphs at several even orders, computes pure minima, and applies randomized expansion/greedy-reduction searches. This is a small finite computational discovery, not a new general structural theory. The authors already knew expansion-first reductions and non-chain gadgets. Those facts limit the claim's significance.

Nevertheless, the supplied counterexample is neither a printed gadget with padding nor the next named catalogue entry fed into an already conclusive published procedure. It supplies the missing doubled-input restriction, an exhaustive pure-minimum obstruction, and absence even of the seven printed reducible gadgets. All 25 choices fail. Unlike the excluded 347138/337352 source-ingredient bridges, the essential counterexample is not a formal consequence of an example supplied by the source. Unlike 372205's literal source-internal error, I found no printed contradiction which makes this just a correction of an existing example. The 355701 precedent remains a real caution: root may judge a random finite search insufficiently substantive. My recommendation is to allow formalisation, with exactly one candidate and no separate credit for the seven-move simplification or incidence repair.

The existing Lean artifacts are honest partial results. I copied the two proved source files to `lean/` and recompiled them with Lean 4.34.1, pinned read-only mathlib package builds, warning-as-error and the required caps. `logs/lean-delta.log` reports only `propext` for explicit reachability, order drop and endpoint blocking; `logs/lean-soundness.log` reports `propext, Quot.sound` for `lower_sound`.

* `Delta153.lean:3–24` gives reasonable finite matrix operations and reachability. The nine-move theorem (48–58) and order drop (59) are correct. General wellformedness preservation, doubled-cubic hypotheses and the seven initial pure-move legalities still require explicit statements and proofs. The abstract `Move.down` lacks a separate vertex-bound premise, but its wye test cannot succeed out of range; prove that fact instead of relying on it silently.
* `Delta153.lean:60–69` certifies a restricted Boolean property. It cannot be promoted to source-chain absence by the lane's stated incidence argument. Replace it with the local edge-capacity obstruction proved in A, or a sound complete chain checker with explicit edge-injective semantics.
* `Soundness.lean:3–27` correctly proves the recursive pure-lower checker's soundness, conditional on a true check. This supplies no concrete lower bound without its missing computation.
* `PureCheck.lean:6` is the unproved direct `decide` attempt. I read it but did not compile it or treat it as a theorem. Its recursive expansion repeats the same subproblems and was already near the RSS cap; do not retry it as the formal route.

The cheapest credible endpoint uses a finite closure certificate: list the 2,328 matrices, root index, and every legal successor index; check each listed graph has order at least 11, root equality, and closure for every legal wye. A generic lemma then inducts on `PureReach` to keep the current graph in this closed set, yielding the lower bound. No graph-isomorphism theorem or canonicalisation is necessary. Split the 9,846 transition checks into perhaps 32–64 independently compiled chunks if kernel `decide` on one large declaration is too expensive. Each row can assert an already-defined successor matrix equality and membership; do not trust external hashes in place of graph equality. The final module combines initial pure reachability, lower bound, chain absence, explicit shrinking reachability and the doubled-cubic witness into the literal existential negation of Conjecture 5.1. Preserve labels only for computation; explain invariance under relabelling in the mathematical bridge.

Estimated remaining effort: moderate, roughly 1–3 focused working days including semantic definitions, closure lemma, chunk generation and clean replay. This is an estimate, not a demonstrated resource bound. First formalise the short chain obstruction and generic closure lemma, then pilot one chunk under the caps before generating all chunks. A generic formal graph library is unnecessary. The final dependency audit, explicit-module leanchecker runs, extracted clean rebuild and independent fidelity review remain mandatory. This review does not certify an accepted endpoint.

## Receipts and scope

Every Python and Lean execution used `scripts/cap.sh`: taskset CPUs 0 and 1, CPU 120 seconds, wall 140 seconds, an RSS watchdog killing at 6 GiB, `MALLOC_ARENA_MAX=2`, lane-local TMPDIR/cache and Python `-I`. Every Lean call also used `-M3500`; only one heavy process ran at once. The wrapper reaps its watchdog and target. No leanchecker was invoked. No task-owned background job remains.

`inputs-before.sha256` and `inputs-after.sha256` hash-bind **every file** in the discovery lane before and after review. They are byte-identical; each manifest has SHA-256 `160ed89d3d0c54ec928e011abdde48c60b05274ba0c2b3e5245368a3c20a37fa`. The empty diff is saved in `logs/input-hash-diff.log`. This includes the source PDFs/text, scripts, outputs and compiled/uncompiled Lean inputs. Downloads have separate per-request hashes. All generated scripts, logs, downloaded bodies, compiled modules and this review are inside the assigned review lane. No git, shared ledger edit, upload, publication, browser tab, external message or author contact occurred.

Root alone decides whether to accept the proposed significance judgment and authorize the next lane. PROCEED here means proceed to the missing literal Lean proof with the repaired semantics; it grants no acceptance credit.
