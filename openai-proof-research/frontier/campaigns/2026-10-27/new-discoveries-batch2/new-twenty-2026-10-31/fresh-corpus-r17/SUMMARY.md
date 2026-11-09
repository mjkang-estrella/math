# fresh-corpus-r17 research handoff

No acceptance-ready full-scope Lean solution is claimed. The main finding is a kernel-checked **formula-level refutation of MathDB337160's minimum-location clause**, held for graph/association-scheme semantic identification, literature and significance. No campaign count or shared file was changed.

All40 literal reserved records were read and preserved in `inputs/{id}.jsonl` and `inputs/literal-records.json`. `results.json` is ID-keyed and contains all40 original statements, line numbers, raw-line hashes including original newlines, full chunk hashes, source receipts, individual technical dispositions, and precise review depth. Nine records received primary-passage inspection; four have specifically identified selected proof/construction inspection. Downloading the other manuscripts does not mean their proofs were reviewed. This is not exhaustive technical or worldwide novelty clearance of all40.

## Main finding:337160

In Brouwer–Cioabă–Ihringer–McGinnis arXiv1709.09011v2, Section6 pp20–21, take q=4,e=3/2,d=4,j=2. The literal Gaussian-binomial eigenvalue formula gives

    (91392, 5208, 60, −84, 1428).

Its absolute values have a unique minimum at index2, whereas Conjecture6.2 predicts floor((d+e+1)/2)=3. The column is genuinely valley-unimodal and is outside every listed exceptional tuple. This refutes the minimum-location clause, not unimodality. The direct Gaussian-sum calculation independently agrees with a generating-polynomial diagnostic. See `ATTEMPTS.md`, `dual-polar-witness.json`, and `lean/DualPolar.lean`.

The literal formal theorem is `DualPolar.source_formula_refuted : ¬DualPolar.SourceFormulaConjecture`. Its definitions include the rational Gaussian product, full source summation support, valid prime powers and square-field half-integral parameters, absolute values, valley property, minimum predicate, and exception clauses. All14 definitions/theorems have transitive axiom audits; only propext, Classical.choice and Quot.sound occur. The strict extracted replay passes. **No Lean construction of finite polar spaces or identification of their eigenmatrix with that formula is present. Therefore this is not claimed as the full MathDB Lean endpoint with every semantic bridge.**

The source arXiv v2 still states the conjecture. The publisher accepted-manuscript access returned403 and was not retried or bypassed. The identified Vanhove2011 and Stanton1980 predecessor proof bodies remain unread. Cioabă–Gupta2102.10155v1's introductory scope/Grassmann conjecture passage was inspected, not its full proofs; this gives no polar-space novelty clearance. An omitted minimum-location exception could fail the user's substantive significance standard. Root/independent review must decide; no discovery credit or global-priority assertion is made.

The research-only `formula-only-packet.zip` includes the statement, ordinary proof/source map, primary PDF, raw MathDB line, pinned replay script and manifest. Packet SHA256: `1f0ccff9e906dc9ce164c58a2321e2ece89640aa00730848a777923d66413768`. Fresh extraction is under `fresh-extracted/`; its strict replay return code is0, about7.62 seconds, measured child peak RSS1843540KiB. Source SHA256: `9827473bed5f8e8cd4239645a71752e785b24b93d26a81d715b9a3ff1c5996de`. This is a formula-only research packet, not an acceptance packet or paper.

## Other sustained attempts

**336772:** original Section4 proofs and the closest Alon–Defant successor's Theorem1.2/37-graph exception list were inspected. Most products are already covered by that theorem; K3^4 is explicitly residual. The original lonely/social count and stronger triangle route were pursued: the latter gives only39 rather than27. A1458-variable private-closed-neighbor model for a minimal dominating set of size>=28 timed out after35 seconds with no incumbent. No solver infeasibility or exact upper bound is claimed. The missing step is a sharper structural argument for the finite exceptional graph, not a Lean arithmetic issue.

**336964:** the source defines DD_m as the size of either matched dominating set, not the union. A sampled graph search with exhaustive per-graph subset/matching checks found no counterexample. A deterministic second mechanism checked every single-edge repair of the source's9-vertex no-swap graph and2044 clique attachments (sizes1..4, every nonempty old-vertex attachment subset). None gives finite DD_m>alpha. A minimum-pair deletion/exchange proof is blocked by private dependents on both matched sides; no universal exchange lemma was obtained. `ATTEMPTS.md` records these obstacles.

Important exclusions:337025 is already refuted by its own Section7 double-star construction;337309 already has the source's polynomial tropical complexity upper bound.337000 has an exact known successor resolution.336802,336941,337106,337158,337159 already report solutions/refutations in their literal records, with proof-depth limits retained.337212 has corrupted degree wording; no low-degree wording correction is counted.336920's known indefinite Heawood rank bound is not PSD evidence. All remaining parked targets have individual explanations in `results.json`.

## Provenance and historical reconciliation

Ancestor AGENTS, both campaign ledgers, parent prior-campaign-context, upstream pin/catalogue and r16 handoff were read. Their path hashes are in `context-pins.json`. The bounded exact-ID search through historical summary/review/result/rejection/context/ledger files found only current reservation listings, recorded with hashes in `inputs/historical-hits.json`; it does not clear notes indexed only by titles or other names. Reservation coverage excludes only its listed sources, not complete campaign/global prior art. Protected330264/335230/326640 and active333569 were not investigated or duplicated. Historical routine/known-result exclusions and r16's Jones/Li–Wu exclusions remain in force; no parameter variant/helper is nominated.

Live OpenAI/math HEAD was fetched before major investment and equals `4eaee87548250b2682affda7d05d947c05554bae`, unchanged from the verified r16 receipt. Hashes of the referenced current/complete-preprints-tree receipts were verified and reused. `registry-screen.json` records the exact terms and path hits. This is a complete inherited **path** screen at an unchanged head, not a proof-body screen. The root recursive tree is truncated and was not treated as complete. Inherited MathDB403 and Palomar403 were neither retried nor bypassed. Public search results and abstract claims were leads only; search misses do not establish novelty.

`sources/receipts.json` records successful public HTTP URLs, UTC retrieval dates, HTTP statuses and byte hashes. `source-versions.json` records actual arXiv PDF headers. The publisher403, web-only author listings, search terms and unread identified predecessors are separately recorded in `source-access-limits.json`; there is no invented hash for a body not returned by the tool.

## Reproduction and trust limits

From this lane:

    OPENBLAS_NUM_THREADS=1 timeout 200s python diagnostics.py
    timeout 110s python structured-swap.py
    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 timeout 65s python upper-domination.py
    python lean/replay.py
    python fresh-extracted/lean/replay.py

Diagnostics are exact integer/rational or exhaustive per-graph computations, but are not Lean proofs. MILP is floating-point exploration only. Diagnostic scripts enforce at most2 CPU affinity, explicit2–3GiB address-space caps and100–180-second CPU limits; timing/RSS is in their JSON where available. The dual-polar and sampled-swap sweep took about1.17 seconds; deterministic attachments about0.94 seconds. HiGHS warned that its threads option was passed through; CPU affinity independently bounds usable CPUs.

Lean is4.34.1, with pinned read-only mathlib revisiond13f23b723b8a846827a245b89c10fc7d3f11612. Replay uses j1, max2 CPU affinity,120-second CPU/130-second wall limits and a2048MiB Lean managed-memory limit; managed memory is not a total RSS ceiling. Initial address-space-capped runs failed at thread creation; their logs are preserved, and no failed elaboration is treated as a proof. The successful fresh run kernel-checks all new declarations and audits all14. Imported prebuilt oleans are trusted, not rebuilt. No sorry/admit/new axiom/unsafe/native_decide/ofReduceBool occurs in the final source.

`reservation.json` remains unchanged, SHA256 `ffb8c71b02762e93e3b92edca452cd8bd9ee6d7851464df3cdfc52a9c5c40755`. All writes were inside this lane. No child agents, git, shared edits, messages to others, tabs, publication or uploads were used.
