# ACTUALBRIEF, expanded-corpus-r533 (Claude Opus 5.5, high effort)

Credit claimed: 0. Root alone adjudicates. No Lean, program, enumeration, numerical test, CAS, solver or child was used for mathematics.
Statements of author-complete proof below are author claims and have had no independent review.

## Outcome
Three author-complete ordinary proofs of printed conjectures, full text in FULLCANDIDATE.md, formal costs in DORMANT-SOL-FORMAL-PLAN.md:

| ID | Result | Author recommendation |
|---|---|---|
| 347063 | Split Smallest: moves = phi^2 n + O(log^2 n). Combine Smallest: moves = c n + O(sqrt n log n), c = 5/2 - phi + sum_{j>=2} 1/F_{2j} = 1.20648... | Route to independent adversarial qualification. Strongest of the three. Prior art entirely unchecked. |
| 352303 | Full conjecture: star minimum, path maximum, both equality clauses, via BH(T) = N(T)/n with an explicit edge-pair formula and a pendant-path shift | Route to independent adversarial qualification, with the routine objection below. |
| 381964 | Full spectrum and stability on K_{n+1}, all n>=2 | EXCLUDE AS ROUTINE, credit 0. Proof supplied anyway. |

Zero IDs are claimed qualified. Two IDs (372171, 363473) are settled in their own sources, credit 0.

## What the family's structure made sufficient
- 347063(b): in Combine Smallest, while a pool sits at even index p, the whole lower state is one integer L in [0,F_{p-1}), its Zeckendorf representation, and each macro is the rotation L -> L+F_{p-2} mod F_{p-1}. Over a full cycle a chip balance gives exactly F_p - 1 splits.
- 347063(a): a single exact potential w_j = j+2+psi(-psi)^j drops by exactly 1 per Phase 1 move, with w_1 = phi^2.
- 352303: M^{-1} of the edge Laplacian has entries +-(outer size)(outer size)/n, so sum 1/lambda^2 is a sign-free integer sum over edge pairs. Under a pendant-path shift only S = sum s_e^2 and (p,q,t) matter.

## Serious attempts at a routine or generic proof, as required
- 347063: linear functionals neutral on combining moves are value-proportional, so no potential can count Combine Smallest splits, and source Theorem 1.2 and Lemma 3.3 give only Theta(n) and the combine count. No reduction found. Objections retained: part (a) alone is a short potential argument; if the literal is read as Theta(n) only, it is source-own and earns 0; the corpus literal mis-states the start position.
- 352303: coefficient monotonicity does not imply it because sum 1/lambda^2 is a difference of two quantities that both increase toward the path; spectrum majorization points the wrong way. No complete prior-to-target bridge found. Strongest objection: one page combining a classical inverse edge-Laplacian formula with the standard pendant-path shift. The proposal is not a claim that these tools are new.
- 381964: the attempt succeeded, which is the objection: S_{n+1} acts multiplicity-freely on the tangent space, so the source's own printed Jacobian forces the block form.

## Limits that would change the disposition
- 347063: NO search was spent on this target. All three native searches were used before the route was found. Follow-up Zeckendorf-game work from the same group was not read, the Fibonacci Quarterly final was not read, and a later exact result is possible. This is a real HOLD, not a formality.
- 352303: one search, excerpts only, no proof found. No final version shown on the arXiv listing. Companion Wei-Li-Yang 2110.02656 unread.
- 381964: final Axioms 12 (2023) 577 returned HTTP 403 and is closed; see NEW-UNAVAILABLE.json. Unread.
- Every proof here is unreviewed. The Combine Smallest assembly and the endgame case list are the places a reviewer should press hardest.

## Lean feasibility, literal statement needed
Details in DORMANT-SOL-FORMAL-PLAN.md. 347063: finitely supported chip positions, the two deterministic priority step functions, game length from n copies of F_1, tsum constant; elementary but large. 352303: SimpleGraph trees, Hermitian Laplacian eigenvalues, incidence bridge, and a leaf-move induction on arbitrary trees. 381964: Frechet derivative on the Markov tangent space and exact characteristic data, cheap, but author recommends exclusion.

## Parked routes and exact gaps
349418: uniform mass on C_m is a local maximum and passes KKT by hand; unpaid are the reduction of an optimal mass to support on m vertices and the global inequality. 346227: l=1 is false by a trivial degree bound, a domain correction worth 0; intended l>=2 needs the 349418 gap and an O(n^l) error. 346406: needs width-flexible 6-colourings; the source table leaves m = 1,5,7,11 mod 12 at n>=7. The other twelve were parked after the literal only, with sources unread, and those parks say nothing about open status. Recollected public leads for 381534 and 318604 and 329858 are unauthenticated memory, not exclusions.

## History reconciliation
933 allowlisted files; 479 skipped BEFORE stat/open by protected-token filtering on every path component (including every path containing "integration" or "formal", which is conservative and may hide relevant parent records); 454 opened. No exact ID key match. Three source-URL matches, read as neighbours only and not transferred: r75 381965, r292 363474, r348 367900. history-access-inventory.json.

## Inventories
- Literals: literal-bindings.json, twenty chunk path/hash, one-based line, raw line and hash INCLUDING trailing newline, newline flag, raw statement token/hash, decoded statement/hash.
- HTTP: guard-ledger.jsonl, 12 charged GET hops, 10 successes (8 PDF, 2 listing HTML), 1 redirect, 1 HTTP 403. New closure recorded in NEW-UNAVAILABLE.json.
- Search: 3 calls, 3 strings of a 9-string allowance, each precharged and its complete response saved in the next tool call under searches/.
- Read: TASK.txt 0-152712 in 11 chunks; inherited-denials.json 0-299274 in 20 chunks; each at most 15000 characters, receipts read_task_chunk_* and read_denials_chunk_*.
- Source reading was targeted passages via pdftotext, no visual or figure inspection, no whole-body audit, and no final-version equivalence.
- Runner receipts: every completed run has a receipt. One true nonzero exit, get_381964_final exit 1 (HTTP 403), preserved and not rerun.

## Process disclosures
1. Bootstrap output exceeded the tool display; it was persisted by the harness outside the lane and I did not open that file. TASK and denials were read in full through the runner.
2. inspect_history_allowlist_shape printed the allowlist keys (paths only, no listed file opened) and its 237.8KB display was likewise persisted by the harness outside the lane, not read by me.
3. charge_search_1 was preceded by a shell cd into the lane; the runner itself uses the absolute path.
4. Native-search telemetry, transient memory peaks and the writer's own peaks are unknown. Sampled peak RSS across receipts about 61 MB; no universal resource claim.
5. An authoring slip left the string NS in the 346406 prior gate; repaired before seal by receipt fix_gate_and_summarize.

## Twenty ID-keyed gates (from results.json; literal text is there too)

### 367898: Simonovits's supersaturation conjecture for bipartite graphs
status PARK_LITERAL_ONLY; credit 0
- literal: Read
- source: arXiv source body NOT READ in this lane; literal only
- ordinary: Flagship supersaturation, no mechanism attempted
- prior: no search spent on this target
- novelty: NOT ESTABLISHED
- significance: Not assessed
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: Full Simonovits conjecture
- provenance: mathdb-normalized-chunk-0011.jsonl line 2085, raw line with newline sha256 c1a60ba5632b702b2977936ae4a9b5699626365cdc9262533f79cf34dca4821a

### 353539: Collapsibility-number conjecture for Vietoris–Rips complexes of hypercube graphs
status PARK_LITERAL_ONLY; credit 0
- literal: Read; collapsibility number defined only by reference
- source: arXiv source body NOT READ in this lane; literal only
- ordinary: Not attempted
- prior: no search spent on this target
- novelty: NOT ESTABLISHED
- significance: Not assessed
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: All r>=4 upper and lower bounds; definition unread
- provenance: mathdb-normalized-chunk-0008.jsonl line 2846, raw line with newline sha256 41666e1dea1e2cf88353725ef898684b72f28e536cf9a45cee88520aade42540

### 381964: Spectral stability conjecture for simple random walks on complete graphs
status AUTHOR_COMPLETE_PROOF_AUTHOR_RECOMMENDS_EXCLUDE_AS_ROUTINE; credit 0
- literal: PASS: literal matches source Conjecture 3.5
- source: Source arXiv 2212.12401v1 Sections 1.3, 3.1, Remark 3.1 and Conjecture 3.5 read. Final Axioms 12 (2023) 577 returned 403 and that entire work is closed; final unread
- ordinary: Author-complete: explicit operator on the tangent space and block triangular spectrum for all n>=2, agrees with printed n=2..7 data
- prior: One search returned no proof, excerpts only
- novelty: NOT ESTABLISHED
- significance: Author recommends EXCLUDE AS ROUTINE: specialization of the source printed B-prime Jacobian, block structure forced by multiplicity-free S_{n+1} action. Dissent recorded
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: Final source closed and unread
- provenance: mathdb-normalized-chunk-0014.jsonl line 996, raw line with newline sha256 778838352cced8f60da1d17697e0ffe1b1f96c211d6c25cfbcd28075e01fbf46

### 352303: The extremal biharmonic index conjecture for trees
status AUTHOR_COMPLETE_ORDINARY_PROPOSAL_ROUTE_TO_QUALIFICATION; credit 0
- literal: PASS: literal matches source Conjecture 5.3 with n>=5
- source: Source arXiv 2110.09931v1 definition, Theorem 5.1, 5.2 and Conjecture 5.3 read; listing shows v1 only, no journal reference
- ordinary: Author-complete both bounds and both equality clauses. Exact formula BH=N(T)/n reproduces source double-star formula. See FULLCANDIDATE.md Part B
- prior: One search of one string returned no proof, excerpts only, not clearance; Wei-Li-Yang 2110.02656 unread
- novelty: NOT ESTABLISHED
- significance: Serious routine objection recorded: classical inverse edge-Laplacian formula plus standard pendant-path shift. No complete prior-result-to-target bridge found; coefficient monotonicity does not imply it
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: Unpaid: independent proof review, deeper prior search
- provenance: mathdb-normalized-chunk-0008.jsonl line 1620, raw line with newline sha256 658bd95fc393218db53d994c53762d4a876d8a62029577968e53cc5de4a78d44

### 352404: Sharp discrepancy conjecture for arithmetic progressions in grids
status PARK_LITERAL_ONLY; credit 0
- literal: Read
- source: arXiv source body NOT READ in this lane; literal only
- ordinary: Not attempted
- prior: no search spent on this target
- novelty: NOT ESTABLISHED
- significance: Not assessed
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: Removal of the sub-logarithmic factor
- provenance: mathdb-normalized-chunk-0008.jsonl line 1720, raw line with newline sha256 8476d2f2b8aedb9fc6eae1905f932648f10b071c527d09d3b71db6b10534ecc4

### 343272: Approximate Hamilton packing conjecture for regular tripartite digraphs
status PARK_LITERAL_ONLY; credit 0
- literal: Read; c>1 range not checked against source
- source: arXiv source body NOT READ in this lane; literal only
- ordinary: Not attempted
- prior: no search spent on this target
- novelty: NOT ESTABLISHED
- significance: Not assessed
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: Approximate Hamilton decomposition
- provenance: mathdb-normalized-chunk-0006.jsonl line 2660, raw line with newline sha256 552a5accd08f9d1506f1c7417904aaa6649a812aef7bb12d30dc6b4d30ce6580

### 329857: Tournament-forest conjecture for transitive tournaments
status PARK_LITERAL_ONLY; credit 0
- literal: Read
- source: arXiv source body NOT READ in this lane; literal only
- ordinary: Not attempted; hard extremal
- prior: no search spent on this target
- novelty: NOT ESTABLISHED
- significance: Not assessed
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: Polylog upper bound for tournament forests
- provenance: mathdb-normalized-chunk-0003.jsonl line 4333, raw line with newline sha256 d8a64d26a8d363951387225aaca377a2532aa6e46cff6bd434b64d1d3481970e

### 329858: Pach–Tardos conjecture for forest matrices
status PARK_LITERAL_ONLY; credit 0
- literal: Read
- source: arXiv source body NOT READ in this lane; literal only
- ordinary: Not attempted; author recollection of later Pach-Tardos work is a lead only, body not read
- prior: no search spent on this target
- novelty: NOT ESTABLISHED
- significance: Not assessed
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: Polylog bound for forest patterns
- provenance: mathdb-normalized-chunk-0003.jsonl line 4334, raw line with newline sha256 96c57dd752fc6e6b6263f7340f9a308acecff6c1c2f01eda6283881d81c50898

### 324777: The short-orientation conjecture for regular graphs
status PARK_LITERAL_ONLY; credit 0
- literal: Read
- source: arXiv source body NOT READ in this lane; literal only
- ordinary: Not attempted
- prior: no search spent on this target
- novelty: NOT ESTABLISHED
- significance: Not assessed
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: Improve log log d to log d
- provenance: mathdb-normalized-chunk-0002.jsonl line 4303, raw line with newline sha256 d952b272576ce302b7bf2629c0f371c8e46c9a201bd3be4e590c73b5cabb4790

### 317448: Atomlessness of tree-valued Λ-resampling dynamics at almost every time
status PARK_LITERAL_ONLY; credit 0
- literal: Read
- source: arXiv source body NOT READ in this lane; literal only
- ordinary: Not attempted; analytic and infinite
- prior: no search spent on this target
- novelty: NOT ESTABLISHED
- significance: Not assessed
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: Almost-sure atomlessness; Lean very expensive
- provenance: mathdb-normalized-chunk-0001.jsonl line 2035, raw line with newline sha256 bee4b248afc9c72acd0b3e5edf57815571991107a06ee4202ca647958fbf7f87

### 379439: Plesník's chromatic decomposition conjecture for complete graphs
status PARK_LITERAL_ONLY; credit 0
- literal: Read
- source: arXiv source body NOT READ in this lane; literal only
- ordinary: Not attempted
- prior: no search spent on this target
- novelty: NOT ESTABLISHED
- significance: Not assessed
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: All k>=4
- provenance: mathdb-normalized-chunk-0013.jsonl line 3494, raw line with newline sha256 c1d84ee66a3bcbfc3bc932da4090b3c5afea9a68e143c2c17b28e9cc83edabc5

### 345503: Conjectured stable fluctuations of total length for regularly varying Lambda-coalescents
status PARK_LITERAL_ONLY; credit 0
- literal: Read
- source: arXiv source body NOT READ in this lane; literal only
- ordinary: Not attempted; analytic and infinite
- prior: no search spent on this target
- novelty: NOT ESTABLISHED
- significance: Not assessed
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: Stable limit theorem; Lean very expensive
- provenance: mathdb-normalized-chunk-0006.jsonl line 4872, raw line with newline sha256 79f9367027b50b6d87b230c54aed22ea53c6b36dc4e66d8e7ab35eaff4b561ca

### 346227: Asymptotic conjecture for the number of even-length paths in planar graphs
status PARK_LITERAL_DEFECT; credit 0
- literal: Literal says every positive integer l; at l=1 it is false since sum C(d,2)<=3n^2<4n^2. Source Conjecture 1 prints no range; Cox-Martin print m>=2
- source: Source 2004.09207 Section 3 read
- ordinary: l=1 failure trivial, zero credit as a domain correction; l>=2 unproved, equivalent in leading constant to rho(m)
- prior: Search as for 349418
- novelty: NOT ESTABLISHED
- significance: Domain correction earns nothing
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: Intended l>=2 needs the 349418 gap and an O(n^l) error
- provenance: mathdb-normalized-chunk-0007.jsonl line 593, raw line with newline sha256 e291f8687586f08794d9458dfcecb156f53d935de342e8d306922ce197d5e504

### 318604: Nikiforov's lower-bound conjecture for the energy of subcubic trees
status PARK_LITERAL_ONLY; credit 0
- literal: Read; constant c defined by reference
- source: arXiv source body NOT READ in this lane; literal only
- ordinary: Not attempted; author recollection of Heuberger-Wagner extremal tree work is a lead only, body not read
- prior: no search spent on this target
- novelty: NOT ESTABLISHED
- significance: Not assessed
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: Definition of c unread; possible public route via extremal subcubic trees unverified
- provenance: mathdb-normalized-chunk-0001.jsonl line 3184, raw line with newline sha256 ec362ae585eb8b564cc7bec548e4b784d8438745fa8f59cabf69d5d02d706225

### 363473: Kahn's matching-uncovered probability conjecture for regular linear hypergraphs
status EXCLUDE_SOURCE_OWN_PUBLIC; credit 0
- literal: Literal itself reports the refutation
- source: Source 2406.06421 Theorem 1.4 and Conjecture 1.1 read
- ordinary: Source Theorem 1.4 refutes for every k>2; proof not audited
- prior: Source itself
- novelty: Not new
- significance: Public, credit 0
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: Source refutation
- provenance: mathdb-normalized-chunk-0010.jsonl line 2698, raw line with newline sha256 7c178d9abf5f196a75ae243f4a60d77c1afbefa9d98e14411590d160e1beb98b

### 349418: Uniform-mass conjecture for the path optimization parameter
status PARK_PRECISE_GAP; credit 0
- literal: PASS against source Conjecture 5.1 and Definition 2.1
- source: Source 2101.05911v2 Definition 2.1, Section 5 read
- ordinary: Partial, uniform on C_m: cycle-supported second-order local max, KKT inequalities hold for pendant and chord additions by hand; no global proof
- prior: Search found Cohen Antonir-Shapira O(m^-m n^{m+1}), excerpt only, not constant 8; body unread
- novelty: NOT ESTABLISHED
- significance: Not assessed, no proof
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: Unpaid: reduction of an optimal mass to support on m vertices, and the global inequality
- provenance: mathdb-normalized-chunk-0007.jsonl line 3760, raw line with newline sha256 7c0338ab6ccac622ba13010fb88fed5a1bdf39d5734310ba7a1453b72be44ee0

### 346406: Asymptotic six-color conjecture for cycle–path Cartesian products
status PARK_PRECISE_GAP; credit 0
- literal: PASS against source Conjecture 1
- source: Source 2005.02864v2 intro, table and Section 5 read
- ordinary: Not proved; needs 6-colourings of C_m box P_n for infinitely many m coprime to 6
- prior: no search spent on this target
- novelty: NOT ESTABLISHED
- significance: Not assessed
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: Unpaid: a width-flexible periodic 6-colouring pattern; source table leaves m=1,5,7,11 mod 12 at n>=7
- provenance: mathdb-normalized-chunk-0007.jsonl line 771, raw line with newline sha256 23ade06c92bce2f4b23afac430f29e92c34b95ec773417332bf7d49557b4b513

### 381534: Asymptotic planar Turán conjecture for cycles of length at least seven
status PARK_LITERAL_ONLY; credit 0
- literal: Read
- source: arXiv source body NOT READ in this lane; literal only
- ordinary: Not attempted; author recollection of a Cranston-Lidicky-Liu-Shantanam counterexample for large l is a lead only, body not read, no exclusion claimed
- prior: no search spent on this target
- novelty: NOT ESTABLISHED
- significance: Not assessed
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: Read and bridge the recalled counterexample or prove the bound
- provenance: mathdb-normalized-chunk-0014.jsonl line 571, raw line with newline sha256 7df4a1743bc0e69591863ccd4280c304316d4e35528496a770b4c895291b18b3

### 347063: Linear-growth conjecture for Split Smallest and Combine Smallest games
status AUTHOR_COMPLETE_ORDINARY_PROPOSAL_ROUTE_TO_QUALIFICATION; credit 0
- literal: Corpus literal says the game starts from the Zeckendorf decomposition, which is a transcription defect and would give zero moves. Bound instead to source Conjecture 1.4 and Definition 1.1; root must adjudicate
- source: Source arXiv 2006.16457v1 Definitions, Theorems 1.2 and 1.3, Conjecture 1.4 and Section 4 read; listing shows v1 only; Fibonacci Quarterly final unread
- ordinary: Author-complete: SS(n)=phi^2 n+O(log^2 n) by exact potential; CS(n)=cn+O(sqrt n log n) with c=5/2-phi+sum_{j>=2}1/F_{2j}=1.20648 via Zeckendorf low-state rotation. See FULLCANDIDATE.md Part A
- prior: HOLD: NO SEARCH spent on this target, because all 3 calls were used before the route emerged; follow-up Zeckendorf game literature unread
- novelty: NOT ESTABLISHED
- significance: Limit constants are not in the source, but pure Theta(n) reading is source-own Theorem 1.2, credit 0 under that reading; part (a) alone is a short potential argument
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: Unpaid: independent proof review, prior search, final source, literal adjudication
- provenance: mathdb-normalized-chunk-0007.jsonl line 1424, raw line with newline sha256 58fd15e51c865e3701f99df6a683780294db9da3a951e7d19629f835362de698

### 372171: Biro, Collado and Zamora's indeque ratio conjecture for series-parallel graphs
status EXCLUDE_SOURCE_OWN_PUBLIC; credit 0
- literal: PASS
- source: Source 2512.18090v1 Theorem 1.5 statement and intro read; K4-minor-free result implies series-parallel
- ordinary: Not attempted, source proves it; internal proof not audited
- prior: Source itself
- novelty: Not new
- significance: Public, credit 0
- formal: NOT RUN; no Lean or checker in this lane
- independent: NOT DONE; author only
- acceptance: NONE; root alone adjudicates
- gap or exclusion: Exact public theorem in the assigned source
- provenance: mathdb-normalized-chunk-0012.jsonl line 1306, raw line with newline sha256 08c05b7c17e7a23334731d4a417ca92c65331b6f337fcec3e4de8c09a0b55891
