# pi-mathdb-primary-qualified-breadth-r339 — MathDB breadth screening batch (exact-50)

Lane: `frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/pi-mathdb-primary-qualified-breadth-r339`
Session UTC: 2026-10-30 (stamps in `sources/fetch-provenance.json`). Solo delegate, no children, root untouched.

## Scope and method

1. **Binding before science.** `work/bind_inputs.py` bound 26 flat immutable in-place references
   (r338 intake `reserved-ids.json` / `queue.json` / `coverage-delta.json`; inventory
   `manifest.json` + all 20 corpus chunks `mathdb-normalized-chunk-0001..0020.jsonl`; r304
   `accepted-exclusions.json` + `historical-dispositions.json`) into `bindings.json`, each with
   sha256+size, cross-checked against the corresponding manifests BEFORE any scientific content was
   read. No 169 MB corpus copies, no recursive historical trees. The r338 root manifest itself was
   re-verified first (`verify.py verify` on the intake lane: PASS, 283 reported reviews, 28 upstream
   hashes).
2. **Mandatory scope dedup (post-binding).** Zero overlap between the 50 reserved IDs and (a) the
   283 prior reported statement reviews in r338 `coverage-delta.json`, (b) r304
   `accepted-exclusions.json`, (c) r304 `historical-dispositions.json`.
3. **Literal statements.** All 50 full records were extracted verbatim to
   `sources/reserved-records.jsonl` from the bound chunks and read literally. Screening tags were
   not treated as technical review. All 50 received compact honest dispositions in
   `dispositions.json` (no large rejection dossiers).
4. **Access.** ZERO MathDB requests. Public primary HTTP and public web search only; no
   Google/GitHub API/raw/codeload/diffpatch/ScienceDirect; one Exa 429 routed (not retried); no
   browser/account actions. Abstract text was never treated as an inspected proof body; body-level
   claims only for files whose actual bytes are retained and hashed here.

## Outcome (counts unchanged: 9 additional / 39 total / next 40)

- **2 briefs promoted** (`proposals.json`), both with exact ID/URL/quantifiers, source and
  evidence level, full-scope mechanism, decisive small exact calculation, expected certificate
  size, formal dependencies, and the strongest classical-adaptation objection:
  - **394209** — prove `P_3(n) = 20·2^(n-6)` for all n ≥ 6 (optionally l=4). Alon–Lubetzky
    (arXiv math/0608173, Combinatorica 2009; **full PDF retained** in
    `sources/394209/`) prove the Ahlswede–Cai–Zhang conjecture only for all `l ≥ l0`
    (unspecified) and characterize extremal pairs; ℓ=1 follows from the Frankl–Rödl bound, ℓ=2 is
    Keevash–Sudakov; the paper states the all-ℓ case is open. Decisive control planned: exact
    `P_3(n)` for n = 6..8 by branch-and-bound.
  - **393907** — prove every (p,q)-core is contained in the maximal (p,q)-core `κ_pq`, via the
    beta-set downward-closure criterion + Anderson bijection monotonicity. **Decisive bounded
    computation run in-lane and retained** (`sources/core-containment-calculation.json`,
    `work/verify_core_containment.py`, guard-pinned, wall 3.0 s, peak RSS ≈ 11 MB): for all 15
    coprime pairs p<q≤13 with κ_pq ≤ 45, core counts match Anderson's formula exactly, max-size
    matches (p²−1)(q²−1)/24, and **every enumerated core is contained in the max core** — no
    counterexample. Control, not proof; prior-art status is record-level only (searches on
    2026-10-30 found uniqueness/max-size but no containment resolution; body-level re-verification
    of Olsson–Stanton is mandatory before acceptance).
- **10 rejected as publicly resolved**, with citations: 392840 (Chlebík–Chlebíková, APX-hardness
  MIS d-boxes d≥3; 2-page post-print extract retained), 393825 (Hougardy–Vinkemeier IPL 2006, NC
  (1−ε) weighted matching), 394494 (Bonciocat–Cipu–Mignotte, no D(−1)-quadruple, arXiv:2010.09200
  / JLMS; covers integer entries; sign-reduction argument recorded; abstract retained), 393754
  (DeMarco–Kahn arXiv:1206.1016; abstract retained), 393755 (same line, threshold up to
  constants), 393384 (Chattopadhyay–Zuckerman STOC 2016 line), 394345 and 394378 (the records'
  own statements report the solutions), 392847/392848 (statements match the known
  hereditary-property hardness line, record-level).
- **1 parked**: 392617 (Askey–Szegő 1F2 positivity) — the 2026 formal correction to Cho–Chung–Yun
  (Constr. Approx. 2019; arXiv:1805.11855) is the record's source, and arXiv:1801.02312 claims
  necessary-and-sufficient positivity conditions; needs a dedicated body-level source-qualification
  pass. Abstracts retained.
- **16 famous-hard, 15 programmatic, 5 source-gap, 1 routine** quick rejections (compact entries in
  `dispositions.json`). Source gaps recorded honestly: 390141 (`φ(g,n)` undefined in the record),
  393670 (OWR 2005/50 exact ILP not retrievable — extraction returned only the preface), 393824 /
  394837 (no exact claim), 394646 (scheme undefined in record).
- **Assigned work not duplicated**: 338062 tree-depth, 364119 Cayley, 347483 stack (n≤10), 375237
  Nim, 338289 Hermite, 371202 Fibonacci, 368302 CLT, 371547 edge-irregulator duplicate check,
  and the r335 HOLD/PARK items (389505, 388271, 384757) were all out of scope here.

## Failures (accurate)

- First core-enumeration run: `MemoryError` under the 512 MiB guard cap (all partitions ≤ 60 held
  in memory); fixed by streaming per-size generation at NMAX=45.
- Two logic bugs found and fixed en route (partitions of size exactly NMAX only; wrong s-hook
  beta-set criterion — corrected to `∃a∈β: a≥s, a−s∉β`), then validated by exact agreement with
  Anderson's counts on all 15 pairs.
- `core-containment-calculation.json` under `sources/` is the corrected artifact; the first buggy
  run was overwritten and is not retained.
- OWR 2005/50 full text not retrievable this session (393670 remains source-gapped).
- Exa MCP 429 (three query batches) — routed to DuckDuckGo; not retried.

## Payload integrity

`manifest.json` (built by `work/build_manifest.py`) covers EVERY payload file in this lane,
including the verifier `verify.py`, by sha256+size, excluding only `manifest.json` and
`verification-receipt.json` by exact relative name. The final verifier `verify.py` rehashes the 26
bound original references (against `bindings.json`), the retained source artifacts (against
`sources/fetch-provenance.json`), and every payload (against `manifest.json`), checks the exact
file set, re-checks the 50-ID/disposition/dedup invariants, and exits NONZERO on any failure;
success writes `verification-receipt.json`. Integrity is not mathematical or prior-art clearance;
all `source_scope_cleared`/`prior_cleared` flags remain false at root.
