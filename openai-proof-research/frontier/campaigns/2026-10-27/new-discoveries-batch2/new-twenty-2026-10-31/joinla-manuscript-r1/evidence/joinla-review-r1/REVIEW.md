# Independent adversarial and formal-fidelity review of MathDB 365453

Review date: 2026-11-04 UTC. Recommendation: **PROCEED TO ACCEPTANCE PACKAGING**, subject to the bounded prior-art qualifications below. This is a review recommendation, not acceptance or credit. Root decides.

| Gate | Verdict |
| --- | --- |
| A: statement fidelity | PASS |
| B: independent mathematics | PASS |
| C: Lean fidelity and own replay | PASS |
| D: prior art and family independence | QUALIFIED_PASS |
| E: significance and exclusions | QUALIFIED_PASS |

## A. Statement fidelity

The authors are Gee-Choon Lau and Wai Chee Shiu. The title is *On local antimagic chromatic number of the join of two special families of graphs – II*, Utilitas Mathematica 124 (2025), 189–206, DOI 10.61091/um124-12. I independently downloaded the publisher PDF: its SHA256 is 7f1e8188a9cf596cf68773da4063cb1bf8f908d48b7a01132c686bb4c9158e5d, identical to the discovery copy. My fresh pdftotext output also matches the discovery text byte for byte.

References below to published text mean outputs/published.txt, whose line numbers therefore agree with expanded-corpus-r159/sources/antimagic-published.txt. Lines 30–42 define a bijection onto 1 through q, incidence sums, distinct weights at adjacent vertices, minimization of their count, disjoint union, and the multiplier mG. Lines 57–59 explicitly distinguish aP₂ ∨ O_m from a(P₂ ∨ O_m) by listing their vertices and edges. Although the introductory definition starts with a connected graph, the paper explicitly extends it to disconnected graphs and makes the target disconnected claim. Connectedness is not a hidden exclusion.

Published p. 205, lines 914–917, excludes precisely even component count and odd matching size from its constructions, then conjectures, for r,s ≥ 1 and m ≥ 2,
χ_la(2r((2s+1)P₂ ∨ O_m)) = 3.
The MathDB raw/365453.jsonl line 1 and results.json lines 635–658 reproduce this quantifier range and disjoint-union interpretation. Thus r=s=1, m=2 is literally two copies of a join having six matching endpoints and two null vertices, not one join of six matching edges with two null vertices.

Each component has 8 vertices and 3+12=15 edges. The union has 16 vertices, 30 edges, degree multiset 3 repeated 12 times and 6 repeated 4 times. Triangles force at least three proper vertex colors. The source's Theorems 2.1 and 2.3 (lines 172, 258) and 3.1 and 3.3 (660, 727) cover even matching size. The split/merged constructions have other graph structures; none changes that parity restriction into this target. Lemma 1.1 (69–79) is a two-color bipartite obstruction, not a three-color impossibility theorem here. No source theorem already settles the target; the abstract's connected join assertion is consistent with this counterexample.

The live arXiv listing, downloads/arxiv/body lines 140 and 160–162, still lists only v1. The published conjecture remains present in the independently retrieved version of record.

## B. Independent mathematics

I checked the entire palette reduction, including exchanged color roles across components. The following is a complete proof.

Suppose a local antimagic bijection to 1,…,30 uses at most three weights. A triangle implies exactly three distinct weights. Every null vertex in a component is adjacent to both endpoints of every matching edge. Those two endpoints have different weights. Consequently all null vertices in the component have the third weight, and each matched pair uses the other two, in either orientation. This handles arbitrary color assignments, not only labelings respecting a prechosen global tripartition.

Write M_i for the sum of the three matching labels of component i. If its null weight is X and its other weights are Y,Z, summing the six endpoint weights and summing the null weights gives
3(Y+Z) = 2M_i + 2X.
The join-edge labels sum to 2X: each join edge is incident with exactly one null vertex. The total edge-label sum is T=465.

If both components have the same null weight X, their matching sums are equal. The total-label identity becomes T=4X+2M_0, impossible because T is odd. No assumption about endpoint orientation enters.

If their null weights X,Y differ, denote the remaining weight by Z, and let S=X+Y and M=M_0+M_1. Adding the component identities gives 2M=S+6Z; the total-label identity gives 465=2S+M. Hence 5M=465+12Z. The six matching labels are at most 30, so M≤180 and 12Z≤435.

There is exactly one endpoint of weight Z in each of the six matching pairs. These six vertices are independent, since matching edges join different colors and different matching pairs have no edges between them. Their incident edges consist of the six matching edges once each and twelve distinct join edges. If Q is the latter sum, then 6Z=M+Q, and injective positive labels imply Q≥78. Elimination gives 5Q=18Z−465, so 18Z≥855. Multiplying this by 2 and the previous upper bound by 3 would give 36Z≥1710 and 36Z≤1305, contradiction.

This proves no labeling with ≤3 weights exists. This lower-bound argument alone proves the refutation. A separately verified four-weight certificate below establishes the exact value 4 in ordinary mathematics. Existence of some local antimagic labeling follows from the published general existence theorem for graphs without isolated edges, but is unnecessary for contradicting an asserted minimum attained at 3.

### Independent code and neighbours

scripts/independent.py is my own code; it imports no discovery scripts or packages. It exhausts all possible integer weight triples using necessary conditions derived afresh for G=2(nP₂ ∨ O_m). Set q=2n(1+2m), T=q(q+1)/2. A degree-d vertex weight is between d(d+1)/2 and d(2q−d+1)/2.

For equal null roles, it enumerates every possible null weight X and endpoint weight Y, solves T=mX+n(Y+Z) for Z, and checks M=T−2mX is even and lies in the range for 2n distinct labels. Equality of component matching sums proves the evenness condition. For different null roles, enumerate X<Y; both also occur at endpoints, so use the intersection of their degree bounds. Solve 2T=(2n+m)(X+Y)+2nZ and check the matching sum M=T−m(X+Y) and the join sum Q=2nZ−M against the bounds for 2n and 2nm distinct labels respectively. Interchanging the component names makes X<Y exhaustive. The third color Z need not be numerically between them.

No relaxed weight tuple survives for (n,m)=(3,2), (3,3), or (5,2). Since every labeling would yield a surviving tuple, these are rigorous finite necessary-condition refutations, not merely an unsuccessful label search. The first independently decides the target. The latter two also rule out three weights for the requested neighbours r=s=1,m=3 and r=1,s=2,m=2, without asserting Lean proofs for those extensions. See outputs/independent.json and logs/independent.log.

My bounded independent heuristic found a four-weight certificate; scripts/check_four.py then checked it separately by reconstructing the source graph with named component vertices. All labels 1,…,30 occur once, every adjacent pair has different weights, and the exact palette is {45,49,84,99}. In the edge order (uv, ux₀, ux₁, vx₀, vx₁), the three pairs in the first component have labels (19,15,11,27,3), (22,2,21,10,17), (16,4,25,26,7), and the second component has (14,18,13,30,5), (20,24,1,6,23), (8,9,28,12,29). Every u has weight 45, every v weight 49, and the two null weights are 84 in the first component and 99 in the second. Thus the exact ordinary value is χ_la=4. The upper bound is not part of the replayed Lean theorem. See scripts/four.py, scripts/check_four.py, outputs/four.json, outputs/four-verified.json and their logs. This certificate is informative and is not needed for the formal refutation. A preliminary C++ version could not run because no C++ compiler was available; scripts/four.cpp and logs/four.log preserve the failed attempt.

## C. Lean fidelity and replay

I verified the specified packet SHA256 a68ba4bde2e1f3dabacc336c30848ba0ed4a1f701e3df98e68d12eaf6bdd31aa and safely extracted regular files only into a previously empty replay directory using my scripts/extract.py under the resource driver. It rejects absolute paths, parent traversal, links and special entries. No packet shell script was executed.

All following line references are to replay/lean/Antimagic.lean:
- Lines 10–20 define 30 indexed edges and 16 vertices. The matching index t is assigned to component floor(t/3); the five edges are its matching edge and its four joins to the two null vertices.
- Lines 22–46 define actual incidence sums, injectivity into integer labels 1,…,30, and unequal weights on each edge.
- Lines 125–126 define Three using three arbitrary integers, without requiring distinctness. Thus fewer than three weights are included, not accidentally excluded.
- Lines 141–157 establish equal null weights within each component. Lines 177–202 select the twelve distinct join edges at common-weight endpoints; injectivity and cardinality are proved.
- Lines 238–271 prove no_three by the exhaustive same-null/different-null split, with no hypothesis fixing color roles across components.
- Lines 278–303 define the source adjacency and prove its looplessness, symmetry, complete edge enumeration and uniqueness, including reversal.
- Lines 305–316 prove that bounded injectivity enumerates the entire interval 1,…,30.
- Lines 318–323 are the exact endpoint: no f:E→ℤ can satisfy Labeling, Proper, and a palette of at most three weights.

This endpoint is an equivalent instantiated obstruction, not syntactically a theorem mentioning χ_la or quantifying over r,s,m. Its mathematical interpretation is sufficient: a finite minimum equal to 3 implies an actual labeling with three weights, and every such labeling transports to the edge enumeration by completeness/uniqueness. Integer-valued labels in the proved interval are exactly the natural source labels. Conversely, Three is precisely “at most three distinct weights” on this nonempty finite vertex set. Triangle properness rules out fewer than three.

There is no substantive missing mathematical bridge. The packet does not formalize a general parameterized graph constructor, a general χ_la minimization operator, or a Lean theorem explicitly transporting such an operator to this instance. Root should preserve that syntactic limitation in packaging rather than advertise a nonexistent general Lean definition. The brief explicitly allows an equivalent instantiated negation; this packet meets that reading. If a separate policy demands a literal theorem containing the χ_la symbol or the full universal family, that would require an additional formal wrapper, not a repair to the obstruction.

My scripts/replay, using my scripts/run, strictly rebuilt Antimagic and Audit separately, then explicitly checked both modules with leanchecker Antimagic and leanchecker Audit. All four calls exited 0. Logs are logs/Antimagic.log, logs/Audit.log, logs/checker.log, logs/checker-Audit.log. Lean calls used -M3500 -DwarningAsError=true; the supplied Lean 4.34.1 binary and package paths were used. The read-only package manifest pins mathlib at d13f23b723b8a846827a245b89c10fc7d3f11612.

The packet Audit.lean source was read, not blindly trusted. It seeds every Antimagic declaration, closes types and values and inductive companions, verifies closure, and emits metadata. My independent.py separately validates the emitted rows: 97 local declarations, 6,845 transitive declarations, only propext, Classical.choice, Quot.sound as axioms, and no local unsafe, partial, implemented-by or extern flags. The endpoint #print axioms output independently lists exactly those three axioms. The source scan has one harmless hit: Audit's string "_unsafe_rec", used to inspect companions. No sorry, admit, new axiom, native_decide, unsafe declaration or external implementation appears in the proof. Precompiled dependencies are trusted; I did not rebuild upstream mathlib.

## D. Prior art and family independence

This is bounded prior-art evidence, not an assertion of exhaustive literature coverage.

I read the cached primary bodies, bound by inputs-before.sha256:
- The source's own Section 2/3 constructions and its explicit parity exception.
- Chan–Lau–Shiu, *Complete solutions on local antimagic chromatic number of three families of disconnected graphs*, CCO 10(4) (2025), 973–988, DOI 10.22049/cco.2024.29032.1818. In sources/antimagic-cco.txt, Theorem 8 and proof at lines 693–701 prohibit label 1 on the triangle using a degree-two cycle argument; Theorem 9 at 763–765 obtains χ_la(C₃+C₃)=4. This is relevant counting/parity precedent. It supplies no theorem for joins with degree-six vertices. The mixed-role case above is not obtained by a triangle-subgraph monotonicity theorem; none is valid merely from these definitions.
- The companion *On local antimagic chromatic numbers of the join of two special families of graphs*, Congressus Numerantium 236 (2025), 15–39. sources/antimagic-companion.txt lines 282–293 and 407–434 give odd numbers of odd-size blocks and odd-component corollaries, excluding two components here.
- The related tripartite constructions in sources/antimagic-cited.txt, Theorems 2.1, 2.4, 3.1, 3.2 at lines 245, 409, 505, 515, use different component/degree structures and odd product restrictions. They do not assert this lower bound.

The originating Arumugam et al. definitions and bounds are credited by the source; its cited bipartite two-color lower bound does not settle a triangle-containing three-color problem. No direct bound implying the target lower bound was identified in these bodies.

Live checks on 2026-11-04:
- The source arXiv listing is still v1; the publisher PDF still states the conjecture.
- OpenAlex published record W7083575723 reports zero citing works; its citing query returns zero. The arXiv record W4404305306 reports zero in its scalar count, but its citing query returns one result: the Congressus Numerantium companion above. I used the actual query, not just the inconsistent scalar. No later resolution surfaced.
- Public web searches included the arXiv ID with counterexample/conjecture, the exact conjecture label and authors, disjoint-union lower bounds, the graph fragment, and 2026 join-conjecture terms. Source and construction papers surfaced; no exact refutation was found. Search snippets are discovery aids, not primary-body clearance.
- The MDPI primary page for *Local Antimagic Chromatic Number for Copies of Graphs* returned 403 on the first HTTP attempt; it was not retried. Its full body was not cleared in this review. General existence and upper bounds advertised there do not themselves imply the target, but unread lower-bound material remains a literature limitation. Crossref, Semantic Scholar, arXiv search API and ScienceDirect were not queried.
- OpenAI/math current head is 4eaee87548250b2682affda7d05d947c05554bae, agreeing with the discovery refresh; its existing catalogue topic screen adds no target-specific hit.
- Omega current head is b52262a023c4db9bb30a128ebfd80ea4ef4c1a53, newer than the discovery screen. The whole recursive root response was truncated, so I did not treat it as complete. Fresh separate D5 and Problems recursive trees are nontruncated, with 13,929 and 1,720 entries; target/arXiv/local-antimagic filename screens have no hits. This is a current path screen, not a proof-body or full-repository semantic audit. An initial request to teorth/erdosproblems was a registry-identification mistake, not an Omega clearance; its receipt is retained and was excluded from the conclusion.

For family independence I read antimagic-manuscript-r2/PROOF.md lines 5–21 and the construction discussion. Credited 354228 proves the even branching case χ_la(T(t,n))=t^n+1 for connected complete full t-ary trees. It uses leaf counts, tuple-sum permutations, and constructions attaining a bound. The present target refutes a different named conjecture on disconnected triangle-containing joins, via nonexistence under all labelings. These are neither the same source conjecture nor graph-family parameter variants. Sharing χ_la is not enough to make them one credited family. The tree result supplies no ingredient for the new obstruction. I recommend treating them as distinct, while leaving credit to root.

## E. Significance and exclusion recommendation

The finite instance refutes the full universal MathDB conjecture; a universal construction for the entire family is not required. It survives publication of the source in 2025. The proof does not apply the source's published labeling procedure to a next catalogue entry, repair a definition, augment a source construction, or restate a known bound from a credited family.

The principal adversarial concern is that the equal-null parity case is elementary and has an older disconnected-triangle analogue. That case alone is insufficient: exchanging the null color between components defeats the naive parity argument. The complete palette case split and distinct-join-label obstruction close that genuine missing case. This is a short argument, but I do not find a cited theorem from which the result follows by routine substitution. Against the campaign's stated precedent allowing small exact counterexamples to published conjectures, it merits acceptance packaging. Its scope and literature limitations should remain explicit. I assign E QUALIFIED_PASS because significance and novelty remain root judgments and the bounded screen leaves an inaccessible body.

## Integrity, reproduction and evidence

All writes, downloads, extraction, outputs, temporary paths and caches stayed in this review lane. No child agents, git, shared-ledger edits, discovery-script execution, browser tabs, uploads, external messages or author contacts were used. Downloads were treated as data, with normal TLS validation and no challenge/403 retries.

Every Python, Lean, leanchecker and labeling-search process used scripts/run: taskset CPUs 0,1; CPU 120 seconds; wall 140 seconds; a process-group RSS watchdog sampled every 0.1 seconds and killed above 6 GiB; MALLOC_ARENA_MAX=2. Only one heavy process ran at a time. No resource timeout or RSS kill occurred in completed proof checks. The watchdog sums the controlled process group's RSS; no measured peak memory claim is made. No worker is intentionally left running at handback.

inputs-before.sha256 and inputs-after.sha256 enumerate every discovery-lane file and are byte-identical. Each manifest hashes to dc10677eec230db71928f5510387dc57cfeec7929416aa9d476d098499f14dd5. The replayed Antimagic.lean hashes to 444d5df26217f4085e462dbdea61586ef9f52d8d33b51641e243c5a0f361a2c0. family-inputs-before.sha256 binds the two tree-family documents before reading; logs/family-hashes.log verifies them afterward. Download URL/status/time/hash receipts and HTTP headers are beside each downloads/*/body. Scripts, full build/audit logs, outputs/audit.tsv and independent arithmetic outputs are retained for root.

To reproduce, use scripts/replay build Antimagic, scripts/replay check Antimagic, scripts/replay build Audit, scripts/replay check Audit, and scripts/run python3 -I scripts/independent.py, from this lane. Extraction has already populated replay; scripts/extract.py deliberately requires an empty destination and should not be rerun over this evidence.

No acceptance is claimed. Root should carry forward the exact instantiated endpoint description, the fact that the exact χ_la=4 upper bound is separately checked but not Lean-formalized, and the bounded prior-art limitations when deciding acceptance packaging.
