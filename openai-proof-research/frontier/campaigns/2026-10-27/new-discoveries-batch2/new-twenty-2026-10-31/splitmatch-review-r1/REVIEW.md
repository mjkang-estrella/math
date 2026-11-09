# Independent adversarial review of MathDB 381751

Recommendation: **EXCLUDE** from campaign discovery credit. This is a correct finite refutation of the published conjecture, but the witness is a short augmentation of the source's own K₄ obstruction, in the binding brief's 341250/373598 exclusion profile. Root alone adjudicates acceptance. Credit remains zero. Completing the general Lean bridge would not remove this substantive objection.

Gate verdicts: **A PASS; B PASS; C QUALIFIED_PASS; D FAIL; E FAIL.** Gate D fails clearance because the relevant author thesis body remains unread; the bounded searches below do not cure that gap. No located public refutation is being asserted.

## A. Statement fidelity — PASS

The exact authors are **Michael Anastos, David Fabian, Alp Müyesser, Tibor Szabó**. The title is *Splitting Matchings and the Ryser-Brualdi-Stein Conjecture for Multisets*. Published EJC 30(3) (2023), P3.10, 28 July 2023, DOI 10.37236/11714. The independent published download is byte-identical to the discovery source: SHA256 `97836f0695a522eb88675dbe7c3ba433da7a52c86b423b464e11ffba07c9e9c6`.

The complete conjecture, transcribed from the supplied source (line breaks and mathematical typesetting normalized), is:

> Conjecture 3. Let G be a graph on 2n vertices whose edge set is decomposed into perfect matchings M₁, M₂ and M₃ and let a₁, a₂, a₃ be non-negative integers such that a₁ + a₂ + a₃ = n − 1. If G has a component that is not isomorphic to a K₄, then there exists a matching M in G such that |M ∩ Mᵢ| = aᵢ for each i ∈ {1, 2, 3}.

Exact references: `downloads/published/text.txt:88–93`, pp. 2–3; arXiv v2 `downloads/arxiv-v2/text.txt:82–84`, p. 2. The existential component hypothesis is also explained at published lines 84–86. It is neither connectedness nor “no component is K₄.” The witness satisfies the latter stronger condition anyway.

The edge classes form a **partition**, not merely overlapping subsets: published lines 22–24 and 61–64 say edge-disjoint/disjoint union. Theorem 2 explicitly allows multigraphs; Conjecture 3 says graph, and the surrounding discussion of the bipartite extension restricts to simple graphs (`downloads/published/text.txt:115–116`; v2 lines 110–113). There is no need to settle an implicit broader multigraph convention: a simple graph is admissible in either reading. Parallel edges and repeated membership are not used by this witness. Zero multiplicities are explicitly allowed. The intended sum is exactly **n − 1**, not n; n is the perfect-matching size and half the vertex count. Theorem 2's n − 2 existence result is consistent with the example, whose maximum under the prescribed caps is 6 = n − 2.

I read both complete arXiv versions and the published paper. The live abs submission history (`downloads/arxiv-abs/raw:157–160`) lists only v1 (6 December 2022) and v2 (1 June 2023), with no withdrawal/retraction notice. **The non-K₄ conjecture is absent from v1**: v1 lines 60–75 give the K₄ obstruction and two bipartite conjectures. The universal exception claim appears in v2 as Conjecture 1.3 and persists in EJC as Conjecture 3. This witness does not refute v1's bipartite conjecture.

`mathdb-entry.json` preserves the literal record. Its existential component wording matches the published target. Its final remarks concern consequences the source attributes to a positive answer, and are not extra hypotheses. Provenance was checked against the original normalized chunk, line **785**: raw SHA256 `4c8663f7a856dca56d8f0dd56d64f27f0b2990fcc5038627aa6f5118b6ace35f`, chunk SHA256 `5d12317791e9a1578acc1223028a8dc821a69c3f08bea3bc6ae08c816db5a6e8`, statement SHA256 `d3c339ac3e32280196bc36b4ba9a9947e8659f0c98beeb0565645490462df702`. See `scripts/validate_inputs.py`, `logs/input-validation.log`.

## B. Independent mathematics — PASS

My own `scripts/mathcheck.py` rebuilds A = {01,23,45,67}, B = {12,03,56,47}, C = {02,14,36,57}. Each is perfect; all 12 unordered edges are distinct and loopless. The union is connected: 0–3–6–5–7–4–1–2–0 is the B/C Hamilton cycle. Thus two copies have exactly two components, each of order 8 and therefore not K₄. The target is n = 8 and (1,3,3), summing to 7.

Two independent finite calculations agree. Vertex-recursive enumeration with memoization computes all local colour-count vectors, then their exact Minkowski sum for the two components: 24 local and 127 global vectors; (1,3,3) is absent. A separate direct combination loop checks **all 8 × C(8,3)² = 25,088** prescribed-colour selections of seven edges and finds **zero** with 14 distinct endpoints. This loop does not rely on the spectrum computation. Full output: `mathcheck.json`, `logs/mathcheck.log`.

Ordinary proof: bipartition B ∪ C as X = {0,1,6,7}, Y = {2,3,4,5}. Every A-edge is internal to X or Y. In a perfect matching let p and q be the numbers of internal edges in X and Y, and t the number of crossing edges. Then 2p+t = 4 = 2q+t, so p=q and the total number of A-edges is even. Under A ≤ 1 there are none. A perfect matching in the alternating B/C 8-cycle must then be all B or all C, giving four edges of that colour. Caps B ≤ 3, C ≤ 3 exclude both. Each component consequently contributes at most three edges, so the union contributes at most six rather than seven. No computational assumption is needed.

Smaller-order checks: all eligible triples with A fixed to the standard pairing were checked at orders 4, 6, 8. The eligible counts are 0, 32, 1,872, respectively; none violates any n − 1 target. Fixing A loses no labelled graph up to relabelling. In particular one copy satisfies every target summing to 3. At 10, 12, 14 vertices I checked 30 reproducibly random eligible triples each (seed 381751), with no violations. These are **spot-checks**, not an independent confirmation of the lane's exhaustive coverage through 14 or a proof of minimality. The direct seven-edge loop and the spectrum algorithm were written independently; no discovery script was imported or executed.

## C. Lean assessment — QUALIFIED_PASS

Packet SHA256: `26696a02df86785f733fc4242447abdd1b2206aeff0f8300183c14d84d132ca5`. My extractor rejects path escapes, symlinks and oversized entries. It extracted into a new lane-local directory. No packet executable or wrapper was run; only the inspected Lean source and audit source were copied into `build/`.

Strict compile of `SplitMatching.lean`, strict compile of `Audit.lean`, and **explicit-module `leanchecker SplitMatching` all exited 0**. Logs: `logs/lean.log`, `logs/audit.log`, `logs/checker.log` (the checker is silent on success). Audit output reports **69** module-origin declarations, no unsafe, partial or new axiom declarations, and transitive axioms contained in {propext, Classical.choice, Quot.sound}. The ordinary `decide` checks are kernel computations, not native_decide. Lean 4.34.1 and the read-only mathlib cache specified in TASK.txt were used; this is not a rebuild of upstream caches.

Source references in `build/SplitMatching.lean`: endpoints/colour/incidence at lines 12–25; local arithmetic at 5–10; simplicity/perfection at 27–32 and 107–110; obstruction at 34–59; actual graph at 60–78; component lower bound at 80–103; edge identification at 113–127; literal count bridges at 137–158; fixed theorem at 160–178. These statements match the finite construction. Five distinct reachable vertices suffice to rule out a K₄ component in ordinary mathematics.

However, `SplitMatching381751.literal_counterexample` is **not** the negation of a quantified conjecture. The remaining formal bridges are real: turn every graph matching into an edge-ID selection, prove matching and colour-cardinality preservation, derive non-isomorphism of the actual component from its cardinality bound, and transport the vertex set Fin 2 × Fin 8 to the canonical 16-vertex type. `graph_edge_iff` proves existence of edge IDs but does not itself package the required arbitrary-matching correspondence.

I supplied and strictly compiled **`build/EndpointSpec.lean`**, with no axioms or unfinished proof. It gives exact, general definitions:

* `Vertices n = Fin (2*n)`, edges as `Sym2 (Vertices n)`, and arbitrary `SimpleGraph` G.
* `IsMatching n G S`: all edges in G and at most one selected incident edge at each vertex.
* `Decomposes n G M`: each graph edge belongs to exactly one of the three finite edge classes and each class has exactly one incident edge at every vertex. Hence these are edge-disjoint perfect matchings covering the graph.
* `HasNonK4Component`: there exists a vertex v whose induced reachable component is not isomorphic to `SimpleGraph.completeGraph (Fin 4)`.
* `Conjecture3 : Prop`: for **all n, G, decompositions M and a : Fin 3 → ℕ**, under the exact sum and component hypothesis, a graph matching S exists with `(S ∩ M i).card = a i` for every colour i.

The required literal endpoint is:

```lean
theorem SplitMatchingLiteral.not_Conjecture3 :
    ¬ SplitMatchingLiteral.Conjecture3
```

This theorem is **specified, not proved** here. The spec contains no `sorry`, axiom or theorem asserting it. Finite graphs on other vertex types transport to Fin (2*n), so canonical labels do not narrow the mathematical scope. Natural subtraction is harmless at n=0, where the component premise is impossible.

Useful pinned APIs: `SimpleGraph.Subgraph.IsMatching` (`Matching.lean:67`), `IsPerfectMatching` (`:236`); `ConnectedComponent` (`Connectivity/Connected.lean:390`), `.supp` (`:548`) and `.toSimpleGraph` (`:643`); `Reachable`, graph isomorphisms and `induce`; `Sym2` for unordered edges; finite-cardinality bounds and `Nat.card_le_card_of_injective`. The spec uses transparent equivalent incidence definitions to avoid reliance on a bounded selector universe.

## D. Prior art and retention — FAIL (clearance incomplete)

The literature screen is bounded and performed live on 4 November 2026. No prior exact refutation was located. This is not a global novelty certificate.

OpenAlex: DOI record **W4385357696** lists one citing work. The full citing query (count 1, per_page 200) returns Müyesser–Pokrovskiy, *A random Hall-Paige conjecture* (2025). I downloaded arXiv:2204.09666v3 and read the citation context at `downloads/hall-paige/text.txt:4004–4010`, with reference [6] at 4047–4048. It concerns prescribed multisets in group multiplication tables and the Latin-square conjecture, and supplies no three-colour non-bipartite exception counterexample there. Full-title OpenAlex search returned six works, retained in `downloads/openalex-title/raw`; the older unrelated works do not establish a later resolution. Searching the arXiv identifier as full text returned the citing Hall–Paige paper, **not a separate arXiv record**. An exact landing-page filter returned zero records; therefore I do not claim a separate complete arXiv citation graph. See `logs/network-inspect.log`, all receipts under `downloads/`.

The source's complete proof and references contain no diamond/prism/cube construction or non-K₄ exception family. In the cited Arman–Rödl–Sales *Colourful matchings* (arXiv:2102.09633), I checked the actual Question 1.1 and Theorems 1.3–1.5 (`downloads/colourful/text.txt:25–89`) and the concluding remarks (1462 onward). These provide asymptotic/constant-loss existence statements, not this exact obstruction. The cited Black–Cetin–Frick–Pacun–Setiabrata paper (arXiv:1809.03268) was downloaded and its introduction/main statements inspected; its independent-set fair-splitting results do not print this component in that inspected material. This is not a line-by-line audit of every cited article. The public Fabian arXiv author search includes same-name physics false positives; the combinatorial later leads concern bootstrap percolation. Broad searches for later work by Arman, Rödl and Sales, splitting/rainbow/prescribed-colour matchings, exact conjecture numbering, and MathOverflow yielded no relevant resolution. Search terms/access outcomes are in `web-search-notes.md`.

Thesis gap: David Fabian's *Graph bootstrap percolation and additive combinatorial constructions* is highly relevant. Its indexed institutional abstract says it studies split matchings and the n − 2 theorem. Indexed chapter material identifies Chapter 5 and Conjecture 5.3.1, discusses the K₄ parity obstruction, and still presents the extension conjecturally. Those snippets do **not** establish the absence of additional obstructions elsewhere in the thesis. The discovery lane's exact challenged PDF URL was not requested again. My institutional record request through web fetch returned **429**, and I should have blocked redirects to that record thereafter: an attempted alternative DNB URN route subsequently redirected to the **same institutional record**, returning a bot challenge. This was an inadvertent revisit to a rate-limited endpoint, recorded candidly; no challenge execution, bypass, subsequent retry, or PDF retrieval occurred. The resolver response is retained in `downloads/thesis-dnb/`; its title is “Making sure you're not a bot!” (HTML-escaped apostrophe). No full thesis text has been read. This operational deviation does not establish clearance.

GitHub: three unauthenticated repository API queries, spaced by at least eight seconds, for `"2212.03100"`, `"splitting matchings"`, `"Ryser-Brualdi-Stein"`; each returned total_count 0, incomplete_results false, HTTP 200. Three is below the limit of eight. Repository metadata search is not code search and cannot rule out unindexed Lean files. No 403 occurred.

Lean Pool: current HEAD **01db1d7049cf9668bda1e9e106875ee1278b43e6**, commit date 7 October 2026. I fetched `LeanPool/projects.yml` and the complete untruncated tree at that SHA, then **all ten blobs in candidates/** at the same SHA. Queries for the ID, arXiv ID, splitting-matchings wording and authors found no relevant counterpart. The only broad Ryser hit is an unrelated permanent-formula description (`logs/pool-screen.log`). This clears only this registry snapshot, not all public formalizations. The original lane's broader registry screen was read as a claim, not substituted for an independent live check.

Exact evidence missing for D: **a legitimate full-text inspection of Fabian's split-matchings thesis chapter and its relevant surrounding remarks**, plus any necessary follow-up if it identifies further constructions. The current excerpts cannot clear the author's own thesis. Additional live author/citation coverage would strengthen, but cannot replace, that inspection. As E independently warrants exclusion, I do not recommend more Lean investment to cure D.

## E. Significance and exclusion — FAIL

The witness is genuinely outside the printed “all components K₄” family, so this is a real mathematical refutation, not a domain or wording correction. Nevertheless the campaign expressly excludes short augmentations of source constructions, even when they falsify a new conjecture.

There is an exact two-switch derivation. On one pair of source K₄ blocks, {0,1,2,3} and {4,5,6,7}, keep A and B as in the candidate and take

`C₀ = {02,13,46,57}`.

Their union is precisely two disjoint K₄s with the source decomposition. Apply the single colour-preserving 2-switch

`{13,46} → {14,36}`.

This gives **exactly H**. Repeat in the other pair of K₄ blocks. Starting from the source's four K₄s on the same 16 vertices, two switches produce the complete candidate, with the **same all-odd tuple (1,3,3)**. This equality of removed/added unordered coloured edges is independently asserted by `scripts/mathcheck.py` and recorded in `mathcheck.json`. No additional vertices, sophisticated operation, or new parameter regime is needed.

The perfect-matching parity proof above is a short check that this alteration preserves the obstruction needed under the caps. It is not a proof that arbitrary switches preserve every K₄ obstruction. But the full new ingredient is still this very short parity check on a pair of diamonds, followed by the source's disjoint-component deficit argument. The source does not print the switch; **“not printed” does not make a short augmentation eligible** under the binding 341250/373598 precedent. I judge this case squarely within that exclusion, rather than retaining it merely because small exact counterexamples can otherwise qualify.

The authors explicitly conjecture at published lines 84–93 that K₄ is the only exception; no additional obstruction is acknowledged in the inspected source. I make no claim about their private knowledge or the unread thesis. An easy restriction to bipartite G avoids this example and is already the source's separately emphasized conjecture (indeed the v1 formulation). Imposing connectedness also excludes this witness; neither repair is proved here. The witness therefore contributes an elementary extra obstruction to the source's exception classification, while leaving its main n − 2 theorem and bipartite problem intact. That is mathematically useful but insufficient for this campaign's substantive-credit standard.

## Reproducibility and handback

All writes, extracted files, temporary directories, caches and downloads are confined to this review lane. No git, shared ledger edits, child agents, browser tabs, uploads, author contact, external messages, software installation or TLS disabling were used. No discovery Python code or packet executable was imported/run. Each download has a fresh directory and URL/time/status/hash receipt. Search-engine observations and failures are separately recorded.

Each Python/Lean/checker invocation used `scripts/cap.sh`: two-CPU affinity, per-process CPU 120 s, wall timeout 140 s, sampled process-group RSS kill at 6 GiB, MALLOC_ARENA_MAX=2, lane-local TMPDIR and cache. Every Lean subprocess, including the one started by leanchecker, receives -M3500 and -j1. Only one heavy job ran at a time. The watchdog is sampled, not a cgroup hard guarantee. No background jobs remain at handback. The initial checks' tool completion statuses are also summarized in `review.json`; logs preserve the complete prover/audit outputs. The executable **`scripts/replay.sh`** replays the offline mathematical/provenance/strict Lean checks using the safely extracted sources and the same caps; it does not perform fresh network requests.

Before/after candidate input hashes are `inputs-before.sha256` and `inputs-after.sha256`; they are byte-identical. The manifests cover the discovery lane's Lean, Markdown, JSON, retained source `raw`/text and packet inputs. The exact MathDB JSONL is separately bound by `raw-before.sha256`, original chunk/statement checks and `logs/raw-unchanged.log`. Candidate-manifest verification appears in `logs/inputs-final-unchanged.log`. These manifests do not claim that the parent's concurrently maintained administrative ledgers are immutable.

Required files: `REVIEW.md`, `review.json`. Supporting scripts, downloads/receipts, extracted source, strict logs, mathematical output, endpoint specification and offline replay driver are retained alongside them. Overall **EXCLUDE** is a recommendation to root, not self-acceptance or a ledger mutation.

The complete offline `scripts/replay.sh` was also executed successfully: `logs/replay-driver.exit` is **0**, and all its sequential provenance, enumeration, strict compile, audit, explicit checker and endpoint-spec steps passed under `set -euo pipefail`. Its individual full outputs are `logs/replay-*.log`. The candidate manifests contain 111 entries. Toolchain and pinned dependency-manifest hashes are additionally retained in `dependencies.sha256`.
