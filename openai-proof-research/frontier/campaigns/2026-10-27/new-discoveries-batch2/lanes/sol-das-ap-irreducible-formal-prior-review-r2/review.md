# Independent formal and prior-source review

2026-10-30 UTC. Solo review, no children. **Recommendation: retain the n=5 refutation as mathematically and formally verified; HOLD acceptance for the source/publication and novelty gates below.** Counts remain **9 additional / 39 total / next 40**. Root alone accepts and counts. This review changes no shared, git, public, browser, MathDB, manuscript, or inherited mathematical Lean file.

| Gate | Decision | Exact scope |
|---|---|---|
| SOURCE | PASS for arXiv v3; journal identity HOLD | Actual p10 definition and p22 Conjecture 5.1 match the endpoint. Final/accepted journal body was not obtained. |
| MATH | PASS | Explicit zero-diagonal n5 pattern, all four AP conditions, all ten nonzero deletions, ten > eight. |
| FORMAL | PASS for inherited finite refutation | Fresh strict serial compilation and exhaustive actual-origin audit: 71 declarations, no unsafe/partial, Std3 axioms only. |
| SUBSTANTIVE | Provisionally eligible, root adjudication remains | Full negation of the universal source conjecture; no specific complete classical subsumption bridge identified. |
| NOVELTY | HOLD | Bounded positive comparison evidence; unread journal/thesis and incomplete public-registry/current literature coverage remain. |

## Frozen object and exact source

Reviewed archive: `sol-das-ap-irreducible-source-formal-r1/source-only.tar.gz`, SHA-256 **a8e63b8b21d9963e64ce8a9e6dc6cda4789228b418e351417aa5b3a20259f0d3**. It was hashed, copied, checked against the original again, and extracted only into this lane before reading its scientific content. `freeze.json` records these checks and every extracted file hash. Administrative inputs are snapshots only. `immutable-references.json` checks the archive's shallow scientific original/copy chains and selected existing primary/prior references, without recopying historical trees. Final verification rechecks originals and frozen copies. The underlying original-reference chain was checked during the evidence phase; the initial pre-reading freeze was of the supplied archive itself.

Actual source: Sunil Das, *Sign patterns that allow algebraic positivity*, arXiv:2112.00442v3; v3 history 22 March 2022, PDF title date March 23. Primary PDF SHA-256 **c7ebbffde1cd95c6cf363b9627d3dbd2311d066d0156fffd5a68e6df21198379**. Read the frozen actual definition p10, Lemmas 3.9–3.10 and their proofs pp11–12, and conclusion/Conjectures 5.1–5.2 p22. The text extraction is frozen with SHA-256 `a29482c3443e4d18f5f3ce112e579c0f19368d0f4cda897344b61d93671f53ab`.

AP-irreducibility requires A irreducible, a plus in every row, a plus in every column, and B_A irreducible. Minimality means every replacement of a nonzero cell by zero destroys that conjunction. Conjecture 5.1 bounds the nonzero count by 2n−2 for every such zero-diagonal pattern. It does not add an assumption that the pattern allows algebraic positivity. The subsequent comment about known algebraically positive matrices does not insert that hypothesis. Conjecture 5.2 is separate.

Lawful Crossref metadata freshly identifies DOI **10.1016/j.laa.2022.08.007**, LAA **653 (2022), 151–182**. Crossref gives November 2022 issue publication; OpenAlex gives August 10, 2022 publication metadata. These are distinct metadata date fields, not independently verified body dates. OpenAlex's target locations offer the publisher and submitted arXiv version, no accepted institutional PDF. The previously verified ISI record is metadata/abstract only. These facts do not establish that the exact numbered conjecture survived into the journal body. The restricted IITG 2021 thesis remains unread and uncleared.

## Entire mathematical Lean inspection and source bridge

I read all of `Definitions.lean` (SHA-256 **99ad710f6b7c0da4bbf1805641d3d5d10ac890eb550ac333f52a358d88595e08**) and `Witness.lean` (**ca70edcb04188fb1fe82d7a707410a5bb2e6800eb0a0cbbc09b80695311e70f5**), not just their summaries or previous receipt. Replay copies, extracted bytes and original worker files are byte-identical.

`Pattern n` is literally `Fin n → Fin n → Sign`, with exactly zero/plus/minus. `positive` is 1 on plus and 0 elsewhere; `negative` is −1 on minus and 0 elsewhere. `B A i j = positive A i j - negative A j i`. `B_support` proves the OR, not XOR: A_ij is plus or A_ji is minus. `B_overlap` proves the value is 2 when both apply. Thus the integer realization preserves the source sign support, including overlap. No cancellation or positive-magnitude interpretation of A− is used.

`CutIrreducible` quantifies over every nonempty proper finite vertex subset and demands an outgoing support edge. `cut_iff_no_block` proves equivalence with absence of a nonempty set/complement zero rectangular outgoing block. `cut_iff_strong` proves equivalence with reflexive-transitive reachability for every ordered pair: the forward proof uses the set reachable from the initial vertex; the reverse proof propagates membership along paths in a hypothetical closed cut. Both proofs were inspected in full. This is adequate for ordinary matrix irreducibility: enumerate S and its complement to place the zero outgoing block upper-right; conversely a simultaneous permutation block decomposition supplies such an S. Reversing the order swaps upper-right/lower-left conventions. The ordinary permutation/digraph equivalence is explicitly stated in the actual Abagat–Pelejo body p2. The packet does not formalize permutation matrices, but it proves the equivalent finite cut and path characterizations; no unresolved witness-specific irreducibility assumption is hidden here. The n=0/1 conventions do not affect the n5 counterexample.

`APIrreducible` contains all four source conditions, including A irreducibility. `erase` changes exactly the selected cell. Every AP test of an erased pattern recomputes B from that erased pattern. `MinimalAP` requires AP and failure after **every nonzero cell deletion**. It does not ask only for deletion of selected signs, and it is not minimality for A connectivity alone.

The literal matrix is

```
0 + 0 0 +
+ 0 0 0 -
0 0 0 + 0
0 0 + 0 -
0 - + - 0
```

Six plus entries and four minus entries give ten. Initial A and B have the same support and the spanning bidirected path 1–2–5–4–3; positive entries cover all rows and columns. Here is a complete independent reading of the deletion certificates (1-based cells):

| Deleted cell | Sufficient failure |
|---|---|
| (1,2)+ | no plus in column 2 |
| (2,1)+ | no plus in row 2 |
| (3,4)+ | no plus in row 3 |
| (4,3)+ | no plus in row 4 |
| (1,5)+ | no plus in column 5 |
| (5,3)+ | no plus in row 5 |
| (4,5)− | A has no outgoing edge from {3,4} |
| (5,4)− | recomputed B has no outgoing edge from {3,4} |
| (5,2)− | A has no outgoing edge from {3,4,5} |
| (2,5)− | recomputed B has no outgoing edge from {3,4,5} |

`audit.py` independently enumerates all 30 nonempty proper cuts for A and recomputed B, plus row/column coverage, and all ten deletions, without importing worker code. `math-check.json` preserves all four condition flags for each deletion. The Lean proofs use kernel `decide`, not `native_decide`, for the finite propositions.

Actual endpoint types are preserved without filtering in `replay/IndependentAudit.log` and `declaration-inventory.json`. `literal_counterexample` has no hypothesis: it existentially supplies a Pattern 5 satisfying zero diagonal, minimal AP and count > 2*5−2. `literal_conjecture51_false : ¬ SourceConjecture` unfolds to the exact universal assertion over positive n and all patterns. `literal_universal_bound_false` explicitly states its negation without a named wrapper. There are no extra algebraic positivity, eigenvalue, connectivity, minimality or computational-certificate hypotheses. n5 alone refutes the universal claim; a general family, optimum, Conjecture 5.2 and eigenvalue assertions are neither required nor certified here.

## Fresh replay and exhaustive declaration audit

Fresh `replay/` began without candidate oleans. Definitions was compiled first to its local olean, then Witness, then the audit import. All were separate serial `-j1 -M2700 -DwarningAsError=true -DautoImplicit=false` invocations. Mathematical sources were not edited. Audit instrumentation is a separate review file; it introduces no new mathematical claim. Its environment traversal includes **every constant whose actual origin module is Definitions or Witness**, with no namespace/name/public-only filter, including generated match, simplifier, recursion, instance and proof declarations. It is an independently rerun instrumentation copy, with an independently written full-output parser, not adoption of the inherited receipt.

Result: **58 Definitions + 13 Witness = 71** unique declarations. Each has actual fully printed type, module origin, unsafe flag, definition safety (or nondefinition), and transitive `#print axioms` result. Every unsafe flag is false; every definition safety is `safe`; zero partial definitions. All transitive axioms are contained in `{propext, Classical.choice, Quot.sound}`. Every printed declaration has an axiom result, including generated entries. Forbidden source constructs were also screened, as a supplement rather than a substitute for the environment audit.

Compiler binary SHA-256 **e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550**; mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612**. All nine manifest package heads and the pinned manifest hash were checked by direct metadata reads, without git commands, before replay and again in final verification. Imported upstream cached libraries are the inherited trusted pinned environment, not newly rebuilt upstream proofs; candidate caches came only from this fresh compilation. No cache override or alternative compiler is used. `pins-verification.json` records the check and available package build paths.

Lean guard records: Definitions 1.046s / peak sampled group RSS 1,710,329,856 bytes; Witness 1.821s / 1,802,870,784; audit 4.953s / 2,209,792,000. All exit 0, no warnings/errors, under groupRSS2800MiB, CPU210, wall230, no additional Lean AS cap. The helper retains AS/groupRSS512MiB for itself and Python; the Lean child receives the expressly authorized separate budget through its dedicated session guard. Sampling is 40ms and does not exclude unsampled transients. No budget was increased beyond the stated Lean exception.

## Complementary primary comparison and novelty limits

The earlier review is frozen as `prior/review.md`; its actual-source comparisons are retained, not rebranded as new searches. I spot-rechecked the immutable actual Abagat–Pelejo v2 p2 irreducibility definition and Theorem 4 pp3–4: this is a necessary B_A condition for allowing AP, not an oversized minimal-pattern construction or sufficiency theorem. Das 2412.06379v4 Theorems 3.14–3.15 and their proof mechanisms/summary concern patterns **requiring** AP on an underlying cycle; the n5 witness has seven underlying edges, not C5. No matching bridge follows from those scopes. Their original/copy hashes are in `immutable-references.json`; no repeated full review is claimed.

The target's actual Lemma 3.10 proves the 2n−2 bound only when distinct A+ irreducible components have no positive connecting entries. Our positives 1→5 and 5→3 cross {1,2}, {5}, {3,4}, violating that hypothesis. Lemma 3.9 is minimality for a single connectivity predicate. Our ten-entry pattern is minimal for a conjunction, and a negative deletion may preserve A connectivity while destroying B connectivity. Neither proof supplies the refutation by direct application. A substantive exclusion requires a **specific complete previously proved signed construction/adaptation** with the exact reversed-negative B and all-deletion minimality, not just an SCC algorithm or small random witness. None has been identified in the bounded bodies read. This supports provisional eligibility, not worldwide novelty.

Fresh OpenAlex cited-work query (2026-10-30 13:12 UTC) returned five indexed citers. Four metadata titles concern order3/4 or Toeplitz patterns, and the fifth is a 2025 order4 paper; metadata is not body clearance. The database omits even the already known relevant Das cycle paper from this target's five citers, illustrating its incompleteness. I selected the apparently potentially all-order Toeplitz title for one bounded new actual-body comparison.

Zhao–Tian, *Some Studies on Toeplitz Sign Pattern Matrices*, AAM12(1)(2023),332–338, DOI **10.12677/aam.2023.121036**: lawful publisher PDF SHA-256 **979129d37555087968d514897714f8b5a0fe032ea80b4f7fd050fbfa90b27da0**. Actual pp332–338, all main theorem statements 3.1–3.4 and proof bodies were read in the preserved extraction. Theorems 3.1–3.3 classify zero-diagonal **order-three Toeplitz** patterns allowing AP; proof cases use irreducibility/plus coverage, explicit polynomial positivity or eigenvector realizations. Theorem 3.4 changes the diagonal via scalar shift, still order3. The conclusion also fixes order3. This contains no n5 minimal AP refutation or proved lift preserving all-deletion minimality. Its references cite both the target and the restricted 2021 thesis. No correctness audit of that paper's ancillary assertions is asserted or needed for this scope comparison.

The target accepted/final journal text was not found in the bounded lawful metadata/previous institutional route evidence. No ScienceDirect/Elsevier workaround, restricted thesis fetch, challenged publisher, SemanticScholar429, Google, GitHub API/raw/codeload/diff/patch, proxy, TLS-disable, browser, message or external-copy request was attempted. Old inaccessible registry intervals remain parked. The earlier malformed ELA publisher response remains headers-only, not a published proof body. Retrieval records and originals/frozen response hashes are in `retrieval/http.jsonl`; the Hans HTML was gzip encoded and locally decoded from its frozen bytes, not refetched. All other new responses were readable; no new terminal denial was retried.

## Concrete remaining gates and integrity

Before acceptance, root must (1) obtain a lawful actual accepted/final target body and reconcile the definition/conjecture wording, or explicitly delimit acceptance to the verified v3 with an authorized source-gate decision; (2) retain the restricted thesis hold until a lawfully readable body can be checked, without access circumvention; (3) complete a bounded current public-registry and closest remaining citing-body screen through permitted available routes, recording unresolved coverage rather than retrying denied intervals; (4) adjudicate substantive credit in light of the exact classical-bridge test above; and (5) complete any required manuscript/final packet review separately. No general-family/optimum/AP-eigenvalue theorem is an outstanding requirement for this finite refutation.

`archive-check.json` independently reconstructs sorted USTAR/gzip bytes exactly, checks all 42 members (41 entries against the source manifest plus that manifest itself), normalized uid/gid/mtime/mode, and absence of compiled artifacts. Some historical helper/Lean source references and duplicate primary PDFs are inherited archive members; none is imported as candidate mathematical proof. This reviewer did not recursively add historical copies. Source-only describes absence of compiled outputs, not absence of all historical source references.

Inherited failures remain in the supplied archive's FAILURES.md and original immutable worker lane: broad Mathlib import RSS kill, unnecessary Fintype derivation/transparency and lemma/lint failures, and initial missing ZeroDiagonal Decidable elaboration. Original failed build logs remain referenced outside the archive; the source archive does not contain every old run log. No failed build was used as a premise. New review commands passed; `prepare.py` emitted administrative key names while initially inspecting the freeze object, and the later `evidence.py` performs the substantive original/copy assertions explicitly. No failure was erased or silently converted into clearance.

All new Python, hashing, extraction, retrieval and helpers ran through the mandated helper guard with OPENBLAS_NUM_THREADS=1, OMP_NUM_THREADS=1 and PYTHONDONTWRITEBYTECODE=1 except the single outer-shell spelling error disclosed in `FAILURES.md`. Native bounded reads/apply_patch were used as allowed. The first final verifier failed on resolving an inherited relative copy path; that failure is preserved in `FAILURES.md`, and only its path resolution was corrected. The earlier statement that review commands passed refers to the scientific replay/audit/retrieval phase, not this subsequently discovered verifier failure. `manifest.json` excludes itself and `receipt.json`; the separate guarded `verify.py` runs after final writes, checking exact manifest coverage, fixed scientific originals/copies, immutable references, response pairs, pin identities, and independent audit/math results. Acceptance and count changes are not authorized to this reviewer.
