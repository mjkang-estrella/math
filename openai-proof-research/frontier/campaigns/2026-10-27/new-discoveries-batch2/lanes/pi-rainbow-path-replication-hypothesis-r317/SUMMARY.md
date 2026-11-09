# Lane SUMMARY — MathDB 322922: odd-order exact formula for replication numbers of paths

Lane: `pi-rainbow-path-replication-hypothesis-r317` (solo hypothesis delegate; no children; root only orchestrates).
Date of work: 2026-10-30 → 2026-10-31 UTC. All helper runs under `helper_guard.py`
(512MiB AS / group RSS, 210s CPU, 230s wall, single-thread BLAS). Counts unchanged: 9 additional / 39 total / next40. No Lean, no manuscript work, no ledger/shared/sibling/git mutations.

---

## 1. Target (literal)

MathDB record 322922 (uuid `024f3268-35f3-41a9-bb13-fa2e666b111f`, canonical
`https://mathdb.com/p/322922/the-odd-order-exact-formula-for-replication-numbers-of-paths`,
status `open`, post_type `conjecture`, statement_completeness `full`):

> Let P_n be the path on n vertices, and let ρ_R(P_n) denote its replication number.
> For odd n ≥ 1: ρ_R(P_n) = n²/4 + n²/16 + 3n/8 + 5/16 if n ≡ 1 (mod 4), and
> n²/4 + n²/16 + 3n/8 + 1/16 if n ≡ 3 (mod 4).

Source: Szykuła & Kisielewicz, *Rainbow Induced Subgraphs in Replication Graphs*,
arXiv:1201.5340 (2012). r314 read only the abstract; **this lane read the full 14-page body** (hash-bound, §7).

**Rounding resolved (r314 residual):** the displayed fractions are exactly integral.
Writing n = 4m+1: value = 5m²+4m+1; n = 4m+3: value = 5m²+9m+4. Verified numerically
against the paper's own exact values (n=5:10, 7:18, 9:29, 11:42, 13:58, 15:76) and against
Conjecture 6.2 of the body, which the record paraphrases correctly.

## 2. Primary definitions recovered (body §§1–3, quoted structure)

- A **replication graph** G of H replaces each vertex v of H by a clique K_v (any size ≥ 1)
  and each edge uv by all edges between K_u and K_v.
- G **→_R H** iff **every proper vertex coloring** of G contains a rainbow induced copy of H
  with **exactly one vertex in each replication clique**. ρ_R(H) = min |G| over such G.
- **Theorem 2.1 (Hall-type, body §2):** G →_R H ⟺ for every S ⊆ V(H),
  χ(G[S]) ≥ |S|, where G[S] is the subgraph induced by the cliques of S.
- **Lemma 2.2 (Lovász [19]):** a replication of a perfect graph is perfect; paths are perfect,
  and in a path replication graph every maximal clique is a single K_v or K_i ∪ K_{i+1}.
- **Conjecture 6.2** (body §6) = the record statement; **Conjecture 6.3**: ρ_R(P_n) = 5n²/16 + O(n) for all n.
  Crucially, the body's exact values show the §3 upper bound is **tight for every odd n ≤ 15**
  but **loose for even n** (n=8: 23 < 24; n=10: 35 < 36; n=12: 49 < 51; n=14: 66 < 68):
  the odd case is the structured/tight case.
- **Theorem 4.3 lower-bound machinery is explicitly stated only for 2|n**; the odd case is
  untreated in the source. Known lower bound (Cor. 4.4, all n): ρ_R(P_n) ≥ n²/4 + n²/784 + n/2.

## 3. Exact reduction and why the finite criterion covers ALL proper colorings

Let a_1..a_n be the clique sizes of a replication graph of P_n. By Theorem 2.1 plus
perfectness (Lemma 2.2), G →_R P_n **⟺** for every S ⊆ [n]:

  |S| ≤ max( max_{i∈S} a_i , max_{i,i+1∈S} (a_i + a_{i+1}) ).   (∗)

Equivalently, for every k, the largest S with all a_i ≤ k−1 and no adjacent pair
(i,i+1) ∈ S with a_i + a_{i+1} ≥ k has size ≤ k−1; this is computable by an O(n)-DP over the
path per level k (body Lemma 6.1 states the O(n²) total test). This is an **exact criterion
over all proper colorings** (via the Hall characterization), not a bounded-coloring sweep,
and no finite-agreement-to-induction inference is involved. Hence ρ_R(P_n) = min Σ a_i over
positive integer sequences satisfying (∗) — a finite, exactly checkable extremal problem.

## 4. Prior art and scope assessment (explicit limits)

- No journal version found: Crossref query (2026-10-30) returns no matching published work;
  OpenAlex lists only the arXiv preprint, `cited_by_count = 0`
  (`prior/openalex2.json`); Semantic Scholar citations endpoint returned a genuine empty
  result `{"offset":0,"data":[]}` (`prior/s2-citations.json`); the S2 record endpoint was
  rate-limited 429 twice (`prior/s2-record.json`); DBLP bot-challenged (`prior/dblp.json`).
- Web searches (Exa, 2026-10-30) surface no resolution, successor, or citation of
  arXiv:1201.5340; nearest neighbor is the predecessors arXiv:1105.3712 / Fundamenta
  Informaticae 111 (2011) 437-451, which does not treat ρ_R.
- Duplication check: no other lane in this campaign references 322922 or rainbow/replication
  material (greps over `root-mathdb-accepted-exclusions-r304/accepted-exclusions.json` and
  `historical-dispositions.json`: no hits; campaign-wide grep for `1201.5340` hits only
  r314/r316 intake files and the immutable corpus).
- **Limits:** MathDB network on 429 hold (cached record only); S2 record 429; DBLP blocked.
  **No novelty claim is made from absence of search hits.** The open MathDB label and empty
  solutions array are not treated as novelty evidence; the substantive assessment below is
  content-based.

## 5. Verification performed (all logs in `results/`, all runs guard-bounded)

- **R1:** independent checker (exact criterion (∗)) accepts **every** minimal graph listed in
  the paper's §6 table (n=5..15) and rejects perturbed controls. n=9 sum-45 control correctly FEASIBLE.
- **R2:** source Thm 3.1 constructions reproduced exactly (n=13, 15, 16 match the paper's
  printed sequences byte-for-byte) and verified feasible for **all odd n ≤ 21** with the
  conjectured sums (4, 10, 18, 29, 42, 58, 76, 97, 120, 146) — the conjecture's upper-bound side
  is confirmed exactly and cheaply for these n.
- **R3:** independent exact minima (budget-free memoized search, `search3.py`):
  ρ_R(P_3)=4, P_4=7, P_5=10, P_6=14, P_7=18, P_8=23 — all matching the paper.
- **R4:** decision search (`search2.py`): Σ ≤ 28 infeasible at n=9 (120k nodes), Σ ≤ 41
  infeasible at n=11 (17.0M nodes, 49s CPU). So **ρ_R(P_9)=29 and ρ_R(P_11)=42 are
  independently re-established**. n=13 exceeded the 210s CPU cap (documented failure).
- **R5:** multiset relaxation test (see §6A).

Net: the source's data is fully consistent with the conjecture through n ≤ 16 (paper) and
independently through n ≤ 11 (this lane). No counterexample found; the open question is the
**lower bound for all odd n**.

## 6. Proof attempts (two mechanism families + exact search), and why they cap out

Write E := Σ a_i − Σ_{i=1}^n ⌈i/2⌉ ("extra vertices"; Σ⌈i/2⌉ = n²/4 + n/2 + O(1) is the base
bound from independent sets). The conjecture is exactly: **E ≥ m² for n = 4m+1 and
E ≥ m²+3m+2 for n = 4m+3.**

### Attempt A — counting / matching-mass necessary conditions (caps at the base bound)

Two necessary conditions follow rigorously from (∗) (level k = t+1, T = {i : a_i ≤ t},
n_t = |T|, m_v = #{i : a_i = v}):

- **C1:** n_t ≤ 2t. (α(H_{t+1}) ≥ ⌈n_t/2⌉ since H_{t+1} is a subgraph of a path; need α ≤ t.)
- **C2:** if n_t ≥ t: Σ_{v≤t} v·m_v ≥ n_t + (n_t − t)(t−1). (Feasibility forces a matching of
  ν ≥ n_t − t good pairs at level t+1 (König: α = n_t − ν ≤ t); matched pairs have both
  values ≤ t and sum ≥ t+1, so the small-value mass is ≥ ν(t+1) + (n_t − 2ν)·1 = n_t + ν(t−1).)

**Negative result:** the base profile (m = (2,2,…,2,1), i.e. a_i multiset {⌈i/2⌉}) satisfies
C1 with equality and **C2 with equality for every t < n/2** (n_t = 2t, mass = t(t+1) =
2t + t(t−1)). Hence C1 ∧ C2 imply nothing beyond Σ ≥ Σ⌈i/2⌉. Verified exhaustively for
n ≤ 13 (`results/R5`): min over C1∧C2-profiles = Σ⌈i/2⌉ exactly (49 at n=13 vs conjecture 58;
gaps m² / m²+m). Any lower-bound mechanism must therefore use the **arrangement** of good
pairs along the path, not just value multiset statistics.

### Attempt B — the source's own even-n window template, optimally tuned (factor ≥ 38 short)

Theorem 4.3 (body §4, stated for 2|n) yields extra ≥ min{cn(cn−1)/4, d(a−b)n²/4} under
b < a < a′ ≤ 1/2, a + (3/2)c + d ≤ a′, a + (2/3)c + d ≤ 2b. Optimizing the template:
a − b ≤ (a − 2c/3 − d)/2 ≤ (1/2 − 13c/6 − 2d)/2, so the second term ≤ d(A − 2d)/8·n² with
A = 1/2 − 13c/6; balancing with the first term (c n > 1 needed) gives a maximum extra of
**9n²/5476 ≈ n²/608** (at c = d = 3/37, a = 11/37, b = 8/37, a′ = 1/2), vs. the paper's own
Cor. 4.4 value n²/784. The conjecture needs extra ≥ m² ≈ n²/16 — a factor ≥ 38 beyond the
best possible use of the template. **The bridge from the source's even-n method to the odd
conjecture is therefore demonstrably not routine**: it requires a qualitatively new mechanism.

### Attempt C — exact search beyond n = 16 (compute-capped, documented failure)

- Budget-free exact memoized minimization (`search3.py`): state count grows ×8 per n;
  memory cap (512MiB) reached at n = 9 (n = 3..8 complete).
- Decision DFS with tight count-based suffix bounds (`search2.py`): complete for n ≤ 11;
  n = 13 exceeded 210s CPU. A C (no compiler on host) implementation or prefix-split
  multi-run batch would extend this but was out of proportion for this lane.
- Consequently the decisive next calculation (exact ρ_R(P_17), conjectured 97) **remains open
  in this lane**; only the upper-bound side (construction, 97, feasible) is confirmed.

## 7. Precise missing lemma (park recommendation)

**Missing lemma.** For n = 4m+1 (resp. 4m+3), every positive integer sequence satisfying (∗)
has Σ a_i ≥ 5m²+4m+1 (resp. 5m²+9m+4); equivalently E ≥ m² (resp. E ≥ m²+3m+2). What is
missing is a mechanism bounding E below using the **path-adjacency arrangement of good pairs**
(adjacent positions with a_i + a_{i+1} ≥ k) beyond: (i) matching-mass/multiset counting —
provably capped at the base bound by §6A; (ii) the source's window template — provably capped
at ≈ n²/608 by §6B. A candidate mechanism must, e.g., exploit that good pairs must be
*positionally disjoint along the path* while simultaneously covering the value-deficits
d_t = 2t − n_t at every level, with the odd-n parity structure of the tight examples
(values {1..m+1} interleaved with {m+1..2m+1} blocks).

**Recommendation: PARK** (do not credit, do not count). Justification: open since 2012 with
zero recorded follow-up; authors' own machinery even-n-only and quantitatively ≥38× short;
both natural ordinary mechanisms proven insufficient here; exact verification beyond n=11
exceeds lane caps. The target is a sharp all-n quadratic bound (5n²/16 vs proved
n²/4 + n²/784 + n/2) — a genuine research problem, not a low-certificate item. If revisited:
first extend exact verification to n = 13..21 (C implementation or split DFS batch), then
attack the arrangement-sensitive deficit mechanism; a counterexample at n = 17/19 remains
conceivable but is not supported by any current evidence.

## 8. Failures (preserved)

1. `artifacts/search.py` (v1): bad-set DP transition allowed appending through a *good* pair
   (wrongly used nd0+1) — produced false INFEASIBLE on paper graphs; kept for the record,
   superseded by search2/search3.
2. `search2.py` first version: shared mutable `ndp0/ndp1` arrays corrupted parent DP state
   across recursion → poisoned memo, false INFEASIBLE at n=17 T=97 despite a known feasible
   sequence; detected by construction cross-check, fixed (per-node copies).
3. `search3.py`: missing `i==n` base case (phantom positions) and memo key missing depth —
   both fixed; then hit the 512MiB state cap at n=9 (×8 state growth per n).
4. `search2.py` at n ≥ 13: exceeded 210s CPU guard cap (no result, run killed by guard).
5. Semantic Scholar record endpoint: 429 twice; DBLP: bot challenge; no retry/bypass.
6. `c1c2_test.py` enumeration hit the 5M-profile cap at n = 14; **only n ≤ 13 rows of R5 are
   complete** (later rows are truncated-order artifacts and are not evidence).

## 9. Provenance and bindings

- Inputs hash-bound **before reading** (`inputs/input-hashes.txt`): r314 frozen proposals
  (7cec1946…), r314 records-full (2a6a0689…), corpus chunk 0002 (d944c503…, record at line
  2457), accepted-exclusions set (f1883cb4…, 07f2dae9…, 36138273…, f56b9ce8…, d54b83bd…).
- Primary source retrieved 2026-10-30T22:52:00Z (UTC; file mtimes 2026-10-30 15:52:00 -0700):
  `sources/1201.5340.pdf` (sha256 31fb974c75371a4e…, arXiv v1, 14 pp),
  `sources/1201.5340.abs.html` (b20d0f7e…), extracted text `sources/1201.5340.txt`
  (435617f6…). Hashes in `sources/source-hashes.txt`; retrieval via lawful direct HTTPS
  (arxiv.org); no denied endpoints touched.
- Helper runs: all under
  `sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py` with
  OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1; per-run guard JSON in
  logs; no cap raises; failures preserved above.
- Manifest: `manifest.json` (SHA256 per exact path; excludes itself and
  `verification-receipt.json` by name). Verifier: `verify.py` — recompute-and-**compare**
  against the fixed manifest hashes, covers all payload files and both source bindings,
  exits nonzero on any mismatch or missing file. Receipt: `verification-receipt.json`.
