# Independent adversarial review of MathDB 349177

Recommendation: **HOLD**: four compiler-generated partial declarations violate the brief’s literal local-metadata rule, despite a successful kernel replay and safe endpoint dependency closure. This is a review recommendation, not acceptance or a claim of worldwide priority. No campaign credit is assigned here.

Review date: 2026-11-04. All generated material is confined to this review directory. No discovery script was imported or executed; only the extracted Lean proof modules were compiled. The numerical checker, inverse-totient search, extraction code, resource wrapper and replay driver are this review's own implementations.

## Gate A — QUALIFIED_PASS: statement fidelity

The Lean endpoint refutes the conjecture for the **tree obtained by contracting each hexagon of the Deutsch–Klavžar D_k recursion to one vertex, retaining the intervening edges and junctions**. This is, in my assessment, the plainly intended tree reading of the source; it is not a claim about the cyclic molecular graph itself.

Precise source references (line numbers refer to the hash-bound discovery text extractions; numbered copies are in logs/):

* Preprint `sources/349177.txt`, Definition 2.1 and Example 2.2, lines 75–93; final nanostar discussion, Figure 10, Theorem 3.4 and Conjecture 3.5, lines 438–495.
* Published `sources/nanostar-published.pdf.txt`, lines 104–116 (definition and explicit undirected convention), 118–132 (orbits include 1 and tree theorem), 424–470 (tree structure, Theorem 11, Figure 10, failed attempts and final conjecture). The conjecture is on printed page 271, not page 272. The reference list continues on page 272.
* Deutsch–Klavžar `sources/nanostar-cited-deutsch.pdf.txt`, §4.3, lines 544–553; printed page 639, Figures 9–12 (rendered and visually inspected in `tmp/deutsch-639.png`).
* Alikhani–Iranmanesh `sources/nanostar-cited.pdf.txt`, lines 318–340: the different D3[n] molecular family, including its two edges between hexagons and different counts.
* MathDB `raw/349177.jsonl`, line 1: the literal conjecture says at least four stages and refers back to this paper; it supplies no competing recursion.

The paper defines A as an arbitrary set of natural numbers, not necessarily finite. It includes iteration zero and the eventual vertex 1. Its displayed edge builder neglects explicitly excluding the loop from phi(1)=1, but its loopless graph convention, tree theorem, and every figure make loop omission the intended convention. The published version expressly discards edge direction. Positivity is consistent with the domain and the assertion that every orbit reaches 1. A finite realization loses no generality by using a Finset: A is contained in A_phi by iteration zero, so any A realizing a finite graph is itself finite. The source writes equality H=G_phi(A); its numerical assignments to pre-existing chemical trees plainly mean equality after vertex labeling, equivalently graph isomorphism.

I visually compared published Figure 10 (`tmp/published-271.png`) with cited Figure 12. The circled positions in the former correspond exactly to hexagons in the latter, with solid branching junctions retained. This is positive evidence for contraction, rather than merely an inference from the word “tree.” Contracted F is a rooted path of length 3; contracted G1 is one edge. The bouquet recursion then gives precisely the Lean arm recurrence: after removing the common root, arm(0) is a leaf and arm(k+1) has two unary vertices followed by a binary vertex with two copies of arm(k). Three such arms meet at the centre. This establishes the bridge uniformly in k, with order 6·2^k−8 for k≥1, rather than choosing a family to fit the witness.

Neither source version says that stage 3 is impossible, proved possible, or checked; the only stage mentions are the stage-2 construction and the at-least-four conjecture. The independent stage-3 control below is compatible with this silence. The final paragraph reports unsuccessful attempts to **prove nonexistence**, not a published search algorithm or a negative exhaustive search.

Qualification: the source never explicitly defines a contraction operation or a general tree recurrence. Its chemical references include more than one molecular family. A fully literal cyclic molecular reading would make even its Theorem 11 false, so I reject that reading as the intended conjecture. The matching figures and the named D_k recursion supply a persuasive mathematical interpretation, but packaging must state this interpretation openly and must not represent hexagon contraction as an explicit sentence in the source.

## Gate B — PASS: independent mathematics

`mathcheck.py` uses fresh trial division for phi, recomputes complete orbits until repetition, inserts every non-loop totient edge, and compares canonical rooted-tree strings against a separately constructed recursive graph. It checks connectivity and the exact edge count; this is stronger than matching degree or distance histograms. `labelscheck.py` additionally compares every adjacency at every index against the labels in the extracted Lean certificate.

The supplied 23 generators give exactly 88 vertices and 87 edges, unique centre 1024, and distance counts
`1, 3, 3, 3, 6, 6, 6, 12, 12, 12, 24`.
All parents and the canonical tree string are retained in `logs/math-witness.json`. Every vertex is an actual orbit vertex and every parent lies in the same vertex set, so there are no silently omitted vertices or edges.

The paper's A={3,256,376,384,564} gives exactly D2: 16 vertices, 15 edges, centre 16, layers 1,3,3,3,6. For D3, I independently check the discovery lane's numerical witness
`{3,167,334,13107,16384,16449,19577,21932,31657,39154,63314}`
using my own phi and graph code. It has 40 vertices and is the stage-3 model. This is independent verification of data, not an independently discovered witness. The unoptimized independent inverse search first timed out at 25 seconds for stage 3; that negative search result was superseded by direct verification of the witness, not concealed.

A separate bounded stage-5 inverse search is retained in `logs/math-stage5.json`. Its failure to find a realization within the budget is only a search limitation and does not establish impossibility, hardness, minimality, or uniqueness. The witness comparison remains an exact finite calculation independent of search heuristics. The full controls and exact Lean adjacency comparison are in `logs/math-controls-and-labels.log`.

## Gate C — FAIL against the literal metadata rule; kernel replay PASS

The input archive is `proof-source.zip`, SHA-256
`5aa1150cb685221b2f9dbfbab4cd9eff9f503d917add10b62a491a1e19d81fac`.
`setup.py` checks absolute paths, traversal, symlinks and entry sizes before writing into a fresh `build/` directory. Extracted discovery scripts are retained as source evidence but never executed.

`build/lean/Definitions.lean` was read line by line. Lines 7–12 give the inductive tree; 14–29 give sizes and disjoint preorder edge offsets; 30–33 give the arm and nanostar; 34–38 give the simple tree graph; 39–45 give the iterated orbit and undirected loopless totient graph; 46–48 give positive witnesses, graph isomorphism, and all k≥4 quantification. Lines 50–88 prove the finite labeling bridge: closure shows that the entire orbit equals the label image, injectivity and surjectivity produce the graph isomorphism, and positivity is preserved. There is no residual unproved arithmetic or orbit bridge.

`Certificate.lean:6–11` supplies 88 labels, all totient parent indices, size and arithmetic checks. `EdgeRows0` through `EdgeRows7` exhaust all 88 adjacency rows, including all nonedges. `Endpoint.lean:110–122` constructs Realizable(nanostar 4) and applies the universal conjecture at 4 to derive its negation. The Lean witness set is all 88 labels, rather than only the 23 terminal generators; this is legitimate and gives the same orbit graph.

My `replay.sh` rebuilds all twelve modules in dependency order and invokes leanchecker with each explicit module name. It uses the prescribed Lean 4.34.1 and read-only package oleans under the prescribed formal/.lake/packages location. Warning-as-error is enabled. Full output is in `logs/lean-*.log`, `logs/check-*.log` and `logs/replay.log`. Endpoint axioms are printed in its build log. `Inventory.lean` and `Audit.lean` enumerate and print axioms of all 335 local declarations; `finalize.py` compares the actual inventory against the audit coverage. My additional `ReviewMetadata.lean` enumerates safety metadata and exposes four compiler-generated partial definitions. Source scanning finds no prohibited proof feature. Only propext, Classical.choice and Quot.sound occur as transitive axioms.

Trust qualifications: the external prebuilt mathlib/package oleans are trusted, not independently rebuilt or source-attested. Leanchecker uses Lean's kernel, not a separate foundation. The RSS watchdog is sampled and does not guarantee detection of every transient peak. These are replay trust limits, not unproved theorem assumptions.

## Gate D — QUALIFIED_PASS: bounded prior art and retention

A fresh publisher fetch returned 200 and is byte-identical to the hash-bound published PDF, SHA-256 `435183d2ccd61d32ec80530d13a7260ff326402dc895cdc19e8b7ebf413da6aa`. The Gazette version retains the conjecture verbatim in substance. The arXiv abstract page lists only v1, submitted 2020-12-23. The requested listing route returned 429; it was not retried or bypassed.

OpenAlex resolves both DOI 10.1017/mag.2023.57 and arXiv DOI 10.48550/arXiv.2012.12492 to W4382939950. Its citing-work query returns two works: an unrelated OECD/climate Twitter analysis and “A graph related to the Tau function,” DOI 10.1063/5.0315935. The latter's retained abstract concerns iteration of the positive-divisor-count function, not phi; its full text remains unread. The attempted AIP URL returned 403 (and was not an authenticated or validated article route); no further request to that site was made. I do not claim the abstract excludes an incidental discussion of the nanostar conjecture. This is the specific unread-successor limitation. OpenAlex author/topic screens and the newer Alikhani totient/divisor-sum abstract supplied no graph realization or refutation.

Fresh Lean Pool HEAD is `01db1d7049cf9668bda1e9e106875ee1278b43e6`. The complete recursive tree is not truncated. The correct `LeanPool/projects.yml` and every file under root `candidates/` were fetched at that immutable SHA and screened. No nanostar, 349177, arXiv identifier or relevant author hit appears. Totient hits concern Selberg sieves, Wikifunctions and Markoff-order estimates; none describes this graph problem. GitHub unauthenticated repository searches for nanostar+totient, the arXiv identifier, nanostar+Lean, “totient graph,” and totient+Lean found no matching realization or formal refutation. The last query returned six repositories, whose retained descriptions concern fibers, consecutive totients, Lehmer, divisor-sum jumps and Erdős problems. Repository metadata and registry text screening do not clear all code bodies, private repositories or deleted history.

Public title/topic and MO/MSE searches surfaced no refutation. Queries and limits are in `logs/web-searches.md`; per-request URLs, headers, hashes and failures are in `downloads/` and `network-receipts.json`. No Crossref, Semantic Scholar, arXiv search API or ScienceDirect request was made, and no challenge or 403/429 was retried. This supports bounded retention, not absolute novelty certification.

## Gate E — QUALIFIED_PASS: significance and exclusions

This is a modest exact counterexample to a stated published conjecture. The search is routine inverse-totient backtracking and the lane reports a roughly four-second successful run. There is no evidence here of a new general inverse-totient method, a structural classification, or deep number-theoretic progress. Packaging should make none of those claims.

Nevertheless, Theorem 11 is just the explicit five-element D2 witness: it does not publish a recursive labeling procedure that mechanically outputs D4. Extending its diagram requires new compatible preimages at many distinct vertices while avoiding label collisions. The caterpillar and alkane formulas in the source have different branching geometry; they do not already contain this nanostar construction. I therefore do not identify the 355701 exclusion (run the source's own algorithm on its next case), a cited obstruction-family variant, or a short augmentation of a published general construction.

A theorem that every finite tree is a G_phi-graph is false: K1,5 cannot occur, since 1 must be a leaf adjacent to 2 and phi(x)=2 has only the three solutions 3,4,6. Large totient fibers at unspecified integers do not force an iterated tree rooted at 1, with a prescribed height and simultaneous extendible children. Likewise, phi(2^a)=2^(a−1) supplies a path, not the two suitable continuing preimages needed repeatedly on each arm. The primary statements of the cached OpenAI totient-asymptotic and dilation/fiber papers were read; they address counts/least-preimage intervals and large fibers, respectively, not this prescribed orbit tree. No short subsumption argument was found. This is an assessment of the statements, not an audit of upstream truth.

On the campaign's precedents allowing small exact counterexamples, I would recommend packaging rather than exclusion on significance alone, once Gate C is resolved. The root must still decide whether this modest result clears the requested substantive standard; formal proof length and the MathDB open label add no significance by themselves.

## Integrity, resources and deliverables

`inputs-before.json` and `inputs-after.json` bind all 463 selected discovery files (including all proof sources, relevant PDFs/texts, raw records, outputs and logs; replay/cache/tmp directories were excluded). `validation-summary.json` records the comparison, archive hash, declaration count and axiom set. No input mutation is authorized. Local scripts are `cap.sh`, `setup.py`, `mathcheck.py`, `labelscheck.py`, `replay.sh`, `metadata.sh`, `dependencies.sh`, `fetch.sh` and `finalize.py`.

Every Python, Lean and leanchecker call uses `cap.sh`: two CPUs, CPU 120 seconds, wall 140 seconds, MALLOC_ARENA_MAX=2, lane-local TMPDIR/cache and a 6 GiB process-group RSS watchdog. Lean calls additionally carry -M3500 and -j1, including Lean invoked by leanchecker via my own wrapper. The lock serializes heavy calls. The replay began before the lock was added; no numerical process was launched until a lock-holding replay call was observed, so no heavy calls overlapped. Watchdogs are reaped at each call. All long-running tool sessions are collected before handback.

No git, shared-ledger edit, child agent, browser tab, upload, author contact or external message occurred. This recommendation leaves acceptance and any campaign count to the root.

Additional source-access qualification: the third chemical reference, Rashid et al., J. Chem. 2020 Article 1280632, was not independently read; the discovery lane preserves a 403 receipt for its Hindawi PDF. I did not retry that denied route. The uniform tree bridge rests on the accessible Deutsch–Klavžar recursion and its exact Figure 12 match, rather than treating the inaccessible chemistry paper as affirmative evidence.

Final verification: the twelve strict builds and twelve explicit-module leanchecker calls completed successfully. The actual inventory and axiom-audit coverage agree at 335 local declarations; only the three allowed axioms occur. All 463 input hashes are unchanged. My additional metadata command initially had an unannotated numeric counter which Lean inferred as MessageData; I added the explicit Nat type and reran it. The initial diagnostic and source are preserved in `logs/review-metadata-initial-failure.log` and `logs/ReviewMetadata-initial.lean`; this auxiliary checker mistake required no change to any certificate source.

### Gate C blocking finding and exact missing evidence

The strict extra metadata check exposed **four local definitions with `Lean.DefinitionSafety.partial`**:

* `R162.edges._unsafe_rec`
* `R162.size._unsafe_rec`
* `R162.arm._unsafe_rec`
* `R162.instDecidableEqTree.decEq._unsafe_rec`

These are Lean-generated structural-recursion compilation artifacts, not source-written partial definitions. No declaration has unsafe metadata, and these four have no axioms. Lean's own `Lean/Elab/PreDefinition/Structural/Main.lean:187–200` explicitly creates `_unsafe_rec` declarations and calls `addAndCompilePartialRec`; `PreDefinition/Basic.lean:280` implements that compilation path. Their existence alone does **not** invalidate the kernel-checked endpoint. `logs/review-metadata.log` lists all 335 declarations and the four partial flags. `logs/review-metadata-nonsafe.log` preserves the strict rejection.

Nevertheless, the binding brief explicitly asks for local metadata with “no ... unsafe, partial ...” and states no exception for compiler artifacts. I cannot silently treat the actual metadata as clean. Thus Gate C is FAIL under that literal requirement and the overall recommendation is HOLD, superseding the provisional packaging recommendation discussed earlier in this report.

**Exact missing evidence:** a replacement source-only packet whose independently rebuilt local metadata has no partial declarations, with fresh strict module replay, axiom coverage and an unchanged literal endpoint. An alternative disposition would require an explicit root ruling that compiler-generated runtime artifacts are outside this campaign prohibition, supported by the endpoint dependency check; this review does not grant that policy exception. There is no request to modify shared files or change the numerical witness. No mathematical counterexample defect was found.

The independent dependency walk (`ReviewDependencies.lean`, run through `dependencies.sh`) traversed the types and proof/definition values of all local constants reachable from `R162.not_conjecture349177`. It found **271 local dependencies, all safe and non-partial**, with none of the four runtime helpers reachable. The retained log is `logs/review-dependencies.log`. This narrows the hold to compliance with the literal all-local-metadata rule; it is not a claim that partial runtime compilation contaminated the proof.
