# Independent final formal review: MathDB 382297

Reviewer: Claude Opus 5.5, high effort, done personally, no subagents. Credit 0; campaign 57 of 80 unchanged. Root alone adjudicates.

## Recommendation

**TECHNICAL_PASS_ROOT_ADJUDICATION_PENDING.**

I tried to break the claim and could not. `Bun.bunkbed_E7_transitive` is a kernel-checked statement of Hollom's BBC(E7, T_n), with only the three permitted axioms. I found no defect that affects validity or fidelity. Everything I found is cosmetic or a limit on the evidence, listed below. This is a technical recommendation, not acceptance: the paper and root's significance decision remain unpaid.

## Gate results

| Gate | Result | Basis |
|---|---|---|
| A. Fresh replay | PASS | Zip checked for absolute paths, parent references and symlinks; 33 of 33 hashes match; 33 compiles and 33 kernel checks, all exit 0, from an empty build directory. `results/FRESH-REPLAY.json`. |
| B. Source audit | PASS | All 33 modules read personally, plus a mechanical scan. No disallowed or metaprogramming construct. Hypothesis chain discharged. |
| C. Axioms and closure | PASS | Exactly `propext`, `Classical.choice`, `Quot.sound`. Full closure of 6913 constants walked, none missing, 0 unsafe, 0 partial. |
| D. Statement fidelity | PASS | Every listed item checked against arXiv v1 (formulas recovered from the HTML), the journal text and the literal. |
| E. Semantic controls | PASS | `src/ControlE.lean` compiled and kernel-checked; Python brute force and mutation table agree. |
| F. Live prior art | BOUNDED, NO MATCH | Two searches, two strings, full responses saved. No proof or disproof of the tournament case surfaced. This is not novelty clearance. |
| G. Science | PROOF PASS; significance for root | Short proof rechecked independently. Modest but not, in my view, a routine application of an identified earlier result. |

## Gate A: fresh replay

Extraction used the empty `src/` and `build/` directories, with labels `fresh_compile_MODULE` and `fresh_check_MODULE`. No run was killed. Peak sampled memory across all lane runs was 2.25 GiB and the longest run took 1.9 s. `PinCheck` reports Lean `4.34.1`, githash `5045d0056413266e57c625dcd7c365b10e377c52`.

## Gate B: source audit

Mechanical scan over code with comments stripped: zero occurrences of `sorry`, `admit`, `axiom`, `unsafe`, `partial`, `opaque`, `implemented_by`, `extern`, `native_decide`, `ofReduceBool`, `macro`, `syntax`, `elab`, `notation`, `infix`, `prefix`, `postfix`, `run_cmd`, `run_tac`, `run_meta`, `private`, or any instance `priority`.

Things that could look suspicious, and why they are harmless:

- `noncomputable local instance DecidableEq (Fin (j+1)) := Classical.decEq _` appears in six modules. It is local and does not appear in the endpoint statement.
- `attribute [local irreducible] Bun.stf` (and `BunDom.stateCount`) only restricts unfolding during elaboration.
- `set_option maxHeartbeats` appears three times, at 400000 or 800000.
- `open Classical` affects only decidability instances. `Fintype.card` does not depend on which `Fintype` instance is used, because `Fintype` is a subsingleton.
- `#print axioms` in `BunStepOld` is informational.
- The Lean definitions in `BunkbedBase` are at root namespace (`Token`, `Out`, `Arc`, `Reach`, ...). Nothing redefines a mathlib name, since a clash would be a compile error under these imports.

Hypothesis chain: the endpoint takes only `n u v`. `state_endpoint` needs `u ≤ j` and `j < n`, both supplied. `endpoint_step` needs `j+1 < n` and `u ≤ j`. Every hypothesis of `reflection_step` and `payoff_nonneg` (nonnegativity, flip equivariance, no-crossing, dominance, antisymmetry, positivity) is proved by `kernel_flip`, `kernel_cross`, the induction hypothesis, `payoff_flip` or `payoff_pos`. No theorem carries a conclusion-bearing hypothesis.

Bridge audit: `stf_reach_strong` proves both directions by induction, with an inner `ReflTransGen` induction for the last vertical arc, so it is not circular. `reach_char` in the base is not used to close the bridge.

| Module | Role | In endpoint closure |
|---|---|---|
| BunkbedBase | Model definitions, index monotonicity | yes |
| BunkbedCount | Fintype instances for tokens and outcomes | yes |
| BunDomAbstract | Abstract flip, reflection step, payoff pairing | yes |
| BunState | Prefix windows and recursive state `stf` | yes |
| BunBeforeSource | Pre-source state is empty | **no, orphan** |
| BunDomFiber | Assignment split and fiber equivalences | yes |
| BunReach | Indicator algebra, `stf` congruence | yes |
| BunStartSupport | Start-state support | yes |
| BunStepLower | Lower closure of `stepU` | yes |
| BunStepOld | Old-index stability of `stepU` | yes |
| BunUpperSupport | Upper support of state | yes |
| BunBridge | Window restriction `wres` | yes |
| BunDomPins | Pinned-function and hit counts | yes |
| BunHorWitness | Witness form of `hor` | yes |
| BunLowerSupport | Lower support of state | yes |
| BunOldStable | Old-index stability of `stf` | yes |
| BunDomEndpoint | Source-level inequality | yes |
| BunDomZero | Zero-fresh count | **no, unused** |
| BunNewIndicators | New-index membership identities | yes |
| BunDomRecursion | `stf` under join, state count, transport | yes |
| BunReachSupport | Same-index reachability, token transport | yes |
| BunDomRows | Row counts and product equivalence | yes |
| BunReachBridge | Literal `Reach` iff state membership | yes |
| BunDomFiberSums | Row sums, increment weights | yes |
| BunDomActualCounts | Fiber counts for actual assignments | yes |
| BunDomCountLaw | Kernel, uncompressed count law | yes |
| BunDomCompressed | Count law over the size box | yes |
| BunDomDominance | Kernel flip, no-crossing, dominance | yes |
| BunDomPayoff | Payoff formula and positivity | yes |
| BunDomFinal | Endpoint step, `state_endpoint` | yes |
| BunFinalWindow | Window factor for outcomes | yes |
| BunFinalEndpoint | The endpoint theorem | yes |
| BunFinalModel | `card_token`, `card_out`, probability form | no, statement support only |

## Gate C: axioms and closure

`src/AuditClosure.lean`, compiled and kernel-checked, walks types, values, constructors, recursor rules and inductive links from `Bun.bunkbed_E7_transitive`.

- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for the endpoint, `card_token`, `card_out` and `prob_layer_true_le_false`.
- Closure: 6913 constants, 0 missing. Kinds: 4032 theorems, 2171 defs, 349 constructors, 293 inductives, 59 recursors, 4 quot, 3 axioms, 2 opaque.
- Axioms: exactly the three permitted. Unsafe: 0. Partial: 0.
- Opaque: `Lean.opaqueId`, `String.Internal.append`. `implemented_by` (5): `List.attachWith`, `Nat.repr`, three `Lean.Name` constructors. 51 `extern` entries are core primitives such as `Nat.add`. These are compiler-level attributes on core constants; they do not change kernel terms.
- 268 constants come from 30 of the 33 Bun modules.

## Gate D: statement fidelity

Source definitions. Definition 1.1: bunkbed structure with two copies and a vertical edge at each vertex, "bidirectional" for digraphs. Definition 1.2: uniform selection from the family; path of retained edges. Definition 1.4: P(u0 → v0) ≥ P(u0 → v1) for all u, v. Model 4.5: F ⊆ E(D̃) uniform over all subsets. Conjecture 6.4: BBC(E7, T_n) (v1), BBC(D7(T_n)) (journal).

| Item | Finding |
|---|---|
| Arcs i→j exactly for i<j | `Arc` horizontal clause requires `x.1 < y.1`; `HToken` exists only with `fst < snd`. `no_reverse_arc`, `reverse_count_zero` confirm. |
| Two layers | `Vert n = Fin n × Bool`. |
| One independent horizontal token per arc per layer | `HToken` is the triple (i, j, layer); `layers_distinct` confirms. |
| One shared bidirectional vertical token | `Token = HToken ⊕ Fin n`; `vertical_shared` proves the two directions are equivalent for every outcome. The journal's Section 6 says the two directions are "either both retained or both removed", and places independent directions in the separate D8 model. |
| Uniform law | `Out n = Token n → Bool`, every assignment counted once. `card_token : n*n`, `card_out : 2^(n*n)`, matching n(n−1)+n tokens. |
| Reach | `Relation.ReflTransGen (Arc n ω)`. |
| Source and targets | `(u,false)` to `(v,false)` and `(v,true)`. |
| All n, u, v | n=0 vacuous, n=1 by control; v<u gives two empty events; v=u is the reflexive case. All handled in the proof. |
| Direction | card(v,true) ≤ card(v,false), i.e. P(u0→v1) ≤ P(u0→v0). The swapped form is proved false. |
| `Fintype.card` | Elaborated term, shown with `pp.explicit`, is `Subtype.fintype` with `Classical.propDecidable` over `Bun.instFintypeOut_src`. Any `Fintype` instance has the same cardinality, so this counts exactly the intended set. |

E7 versus D7: the same model. v1 names it E_7; the journal renames it D_7 with the same text and number. The MathDB literal uses E_7. Model E8/D8 is different and is not this statement.

Zero-length paths: the source does not define the convention, and it matters only at v=u. With reflexive reach the counts at n=1 are 1 and 2. A non-reflexive walk reading gives 1 and 1, so the inequality still holds. A reading that excludes both a length-zero path and a repeated vertex would make P(u0→u0)=0 and render Definition 1.4 false for every graph, so it cannot be intended. For v≠u the convention has no effect.

Canonical form: the theorem is about the order tournament on `Fin n`. Any transitive tournament is isomorphic to it, and the source treats T_n as one object. I regard this as faithful; no isomorphism transfer is formalized.

The MathDB literal has no extra content beyond BBC(E7, T_n), and its status text is the corpus record as of retrieval.

## Gate E: semantic controls

`src/ControlE.lean` derives its reachability facts directly from `Arc` and `ReflTransGen`, using a closure predicate and an explicit equivalence `Out 2 ≃ Bool⁴`. It does not use the authors' reachability bridge for these counts.

| Control | Result |
|---|---|
| n=1, u=v=0 | `(0,true)`: 1 outcome; `(0,false)`: 2 outcomes |
| n=2, u=0, v=1, derived by hand | `(1,true)`: 7 of 16; `(1,false)`: 9 of 16 |
| Reachability formulas at n=2 | true layer iff (v0∧hT)∨(hF∧v1); false layer iff hF∨(v0∧hT∧v1) |
| Swapped inequality | Proved false at n=1 and at n=2 |
| Endpoint at n=2 | Instantiates to exactly 7 ≤ 9 |
| Shared vertical token | Both directions equivalent, for all n, ω, i |
| Token universe | 1 token at n=1, 4 at n=2, 16 outcomes at n=2 |
| v<u | 0 outcomes |
| n=0 | Vacuous |

Python brute force over all outcomes for n ≤ 4 (`results/python-controls.json`) found no violations and matches the size-state Markov chain exactly. The chain shows no violations for n ≤ 30.

Mutation table at n=1,2: coupled horizontal layers, one-way vertical, undirected horizontal and non-reflexive reach each change an exact count. Two independent vertical tokens leave the n=2 probabilities unchanged (28/64 = 7/16), so counts alone would miss that mutant. It is caught by `vertical_shared` and `card_token_two`.

The first version of the control module failed to compile (`control_e_v1`, exit 1, my own two proof errors). It is retained and was repaired only by changing the source.

## Gate F: live prior art

`inherited-denials.json` was read in full, in chunks of at most 15000 characters, before any network use. Two calls, each charged first and saved in the next tool call:

1. "bunkbed conjecture transitive tournament directed graphs proof Hollom conjecture D7 2025 2026"
2. "bunkbed inequality directed acyclic graphs tournaments unconditioned digraph percolation theorem counterexample arXiv"

Findings: no proof or disproof of the tournament case surfaced. The results were Hollom's paper, Gladkov, Pak and Zimin (undirected counterexample), Przybyłowski's acyclic counterexample (arXiv 2506.22284), Donderwinkel, Jorritsma and Perarnau on forests (2511.13589), and aggregator pages that still list the problem as open. Those aggregators are not evidence of openness.

Przybyłowski's result does not touch this statement: T_n is not produced by that construction, and the positive proof here relies on completeness of the predecessor sets.

Only two of the four allowed strings were used, because each native call takes one query and the call limit is two. I fetched no bodies. DOI 10.1016/j.ejc.2025.104289 stayed closed. Registry roots were not refreshed.

## Gate G: science

Independent recheck, by hand from the model. Reveal indices in order from u. With (a,b) the reached counts, the next vertex has X,Y independent with failure probabilities 2^-a, 2^-b, because every earlier reached vertex has exactly one arc to the new index and the layers use distinct tokens. Then U = X ∨ ZY, V = Y ∨ ZX. Increment probabilities are qr, (1−q)r/2, q(1−r)/2, 1−(q+r)/2 with q=2^-a, r=2^-b, summing to 1. The kernel is flip-equivariant and cannot cross the diagonal in one step, since a−b changes by at most 1. Initial mass is half at (1,0), half at (1,1). Paired sums preserve reflected dominance. U−V = (1−Z)(X−Y) gives payoff (2^-b − 2^-a)/2, nonnegative for a>b. The Lean proof follows this argument exactly, with counts in place of probabilities.

Is it routine? My own view: elementary and short, but not a routine application of an identified earlier theorem. Sketch of a direct form, mine and not formalized: at the first index where |R|=|S|, swap the layers afterward using a bijection between the two reached sets; that gives an outcome-level involution, and before that index a>b holds throughout. This confirms the result is accessible once the count statistic is seen, and it uses the same mechanism.

Strongest case for routine: about 300 words; a textbook skip-free reflection idea; it extends at once to fixed post sets and column-dependent probabilities (a reviewer-derived extension, with no credit); the journal itself says induction looks promising; a specialist could find it quickly.

Strongest case against routine: this is a deliberately stated conjecture for a full infinite family and fixed endpoints, and the author reports it was "more difficult than expected"; it is repeated in the thesis after the acyclic counterexample; the complete-graph proofs do not transfer, since they use source randomization and undirected components; no complete prior-to-target bridge was found by me or the earlier reviewers. Under the campaign's exclusion standard, which requires such a bridge, I do not see grounds for exclusion. Significance is modest, and that judgment is root's.

Family spot check: keyword scan over the 57 accepted and 39 prior scopes. Only superficial hits: 333709 (deterministic bootstrap infection in projective planes), 368807 (ASEP polytope), 324571 (shoe pairs). None gives this model or endpoint. This was not a per-row comparison.

## Defects

| ID | Severity | Description |
|---|---|---|
| D1 | Cosmetic | Stale comments: `BunkbedCount` header lists contents that are not there; `BunBridge` refers to `CHECKPOINT.md`; `BunReachSupport` shares the `BunReachBridge` header; working jargon such as "paid" and "task target". |
| D2 | Cosmetic | Dead code: `BunBeforeSource` is imported by nothing; `BunDomZero` and lemmas such as `reflection_time` and `count_transport` are outside the endpoint closure. |
| D3 | Low | Base definitions sit in the root namespace. No effect here; a future import of more of mathlib could collide. |
| D4 | Low (convention) | Zero-length path convention is not stated in the source. It is immaterial for v≠u and at v=u (see Gate D). |

No defect affects the theorem or its fidelity.

## What I did not check

- The mathlib revision. I did not open anything under the shared packages root, because the lane rules protect paths outside the lane. `formal_command.py` asserts the Lean and leanchecker binary hashes on every run, and `PinCheck` reports the version; the mathlib revision and upstream oleans are trusted per `PINS.json`.
- `leanchecker` replays each named module against its imports. Upstream Mathlib, Batteries and core oleans were not replayed.
- Prior art beyond two search strings; no fetched bodies; the closed acyclic final; registry roots; non-English literature; any worldwide novelty claim.
- A paper, which remains unpaid; none was in the packet.
- An isomorphism transfer from an abstract transitive tournament to `Fin n`.
- Visual inspection of the rendered PDFs. I read the journal text extraction and the v1 HTML with formulas recovered, not page images.
- Thesis text and the other cached sources beyond the search-level mentions; I relied on the earlier reviews for those.

## Process disclosures

- All lane reads and writes went through `run.py` and `write_lane.py`; Lean ran only through the wrappers, one at a time. Exits are recorded in receipts: 118 at tally time, one nonzero (`control_e_v1`).
- Outside `run.py`, I used small `python3 -I -c` filters to trim receipt JSON from displayed output, and one script to edit my draft control file in the scratchpad before writing it through `write_lane.py`. Neither touched a lane file directly.
- Two large outputs were persisted by the harness outside the lane. I did not open those files; I re-read the content through `run.py` in smaller chunks.
- The mathlib pin note in `PINS.json` asks workers to verify metadata before compilation. I did not do that, for the reason above, and the Lean version check ran after the replay.
- The family check used keyword scans and is weaker than the per-row comparison in earlier reviews.

Credit 0. Campaign 57 of 80 unchanged.
