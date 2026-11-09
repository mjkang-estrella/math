# ACTUALBRIEF, lane expanded-corpus-r538

Author: Claude Opus 5.5, high effort, working personally with no subagents. Mathematics by hand: no program, enumeration, numerical test, CAS, solver or Lean. Root alone adjudicates; no acceptance or credit is claimed.

## Outcome

One author-complete candidate, not claimed as qualified.

**353552, tau(K_{2,l}) = Theta(sqrt l).** Proved: for m >= 4 and 2l <= (m-1)^2, every m-assignment of K_{2,l} has at least P(K_{2,l},m) proper colourings, so tau(K_{2,l}) <= max(4, ceil(1+sqrt(2l))). With the source's lower bound (Theorem 4) this is Conjecture 5. It also gives the exact constant: tau(K_{2,l})/sqrt(l) -> 1/(2 sqrt(ln 2)), where the proof is exactly tight on the source's balanced assignment. Full proof in FULLCANDIDATE.md, dormant formal plan in DORMANT-SOL-FORMAL-PLAN.md, no dispatch.

Mechanism: write the count by the number s_x of lists missing each colour and the joint-miss counts c_ab. Keep the diagonal and the A'xB' pairs apart. A single AM-GM over A'xB' with the averaged joint-miss bound F <= n/4 pays the deficit pQ from the missing diagonal; the rest reduces to one explicit inequality H >= 0.

Routine and reduction attempts, reported in FULLCANDIDATE section 7:
- General bounds (Thomassen, Wang-Qian-Yan, the |E|-1 bound) are linear or worse for this family.
- The follow-up paper 2207.04831 proves Lemma 5 (lists inside the union) and Lemma 6 (one colour difference); both are reused and reproved here. Its Theorem 9 applies AM-GM across all m^2 pairs, which cannot reach sqrt l; that paper says the conjecture needs "a novel refinement of our approach or an entirely new approach".
- No reduction to classical theory found. K_{s,l} for s >= 3 was NOT attempted; a reviewer should test whether this is a parameter instance.

Strongest objection: the proof is short and elementary, built on Bernoulli and AM-GM over two lemmas from the follow-up, and the extremal assignment and lower bound are the source's. Root or a reviewer may judge it a routine refinement. Strongest case: an explicitly posed conjecture, restated as out of reach of the follow-up's methods, is settled in full with the exact constant. No complete bridge from any printed theorem was found. Independent adversarial review is the next required step.

## Other routes

- **344764:** literal false at n = 16..21 and 24 by Table 3 of Czabarka et al. (arXiv 1905.06753), the work the source attributes the conjecture to; I checked n=17 by hand (W=259 > 258). Zero: a public-range correction. The range n >= 25 is open.
- **360343:** MathDB records sqrt(n)/2 where the source's Conjecture 3.16 appears to read sqrt(n/2); the source's Lemma 3.14 family refutes the recorded form. Zero: a transcription correction, unconfirmed visually. The intended exact-maximizer statement is open, gap recorded.
- 359433 and 373534 are source-own per their literals. The other fifteen are parked with their gap in the gates below. Their source bodies were unread, so these parks are not open-status certifications.

## Lean feasibility

353552: all finite combinatorics with elementary real inequalities, nothing missing from mathlib, specific imports only. Literal needs: a count formula from actual `SimpleGraph` proper list colourings, Theorem 1, a reproved lower bound (source Theorem 4 must not be assumed; balanced assignment suffices with a crude constant), and the tau definition with chi bridge. Main risks: Pi-type bookkeeping, real exponents, general-l arithmetic in the lower bound. 344764 and 360343 are zero credit and not routed. Parked targets: no route.

## Process record and disclosures

- First two commands run exactly. TASK.txt read completely, 155846 characters in 11 contiguous chunks (0-14000, then 15000 each to 149000, then to end). inherited-denials.json read completely, 318939 characters in 22 contiguous chunks of 15000 (last to end). The bootstrap's persisted display was not opened; the two AGENTS files were read through the runner, in read_agents. No other ancestor AGENTS file exists on the lane path per bootstrap.py's listing logic; root may confirm.
- Corpus: all twenty lines bound in corpus-bindings.json with chunk path/hash, line, raw-line hash with and without trailing newline, raw token and decoded statement hashes.
- Failed receipt retained: history_reconcile exited 1 with a TypeError before any file was opened, because the allowlist is keyed by path and my script assumed a list. Its stderr displayed allowlist path names only; no file was opened. Rerun with changed source as history_reconcile_v2.
- History: 949 allowlist entries; protected tokens filtered on every path component before open (3 skipped, deliberately overbroad including the substring 'hat' and 'loop'); 946 opened and token-scanned. No record mentions any of my twenty IDs. Three source-string hits are neighbours (355861, 360014, and a citation in another record), no transfer. read_allow_head printed the allowlist, and its full output is in the lane; I saw only the first 2KB.
- Network: 6 GET hops, all HTTPS 200 PDF; no denials, redirects or retries. Search: 3 calls, 3 query strings, each precharged, each response saved verbatim as the next tool call. See access-inventory.json.
- Not done: the campaign ledger, prior-campaign-context, the pinned OpenAI repository and comparison against the 97 accepted scopes were not read. Registry roots are closed by inherited denials, so no current registry head was checked. No figure or glyph was visually inspected; pdftotext only. Native tool peaks, transient and writer resource use are unknown; runner receipts record sampled telemetry.
- Prior art for 353552 is bounded: three standard searches, two source papers, one 2026 paper's opening. No citation index. Finals of 2202.03431 and 2207.04831 unread; the |E|-1 bound paper unread.

## Twenty ID-keyed gates (also in results.json)

### 353552
- binding: mathdb-normalized-chunk-0008.jsonl:2859 line sha 28b8e2f0ff762320
- literal: Read and PASS for scope: upper half proved, lower half source Theorem 4.
- source: 2202.03431v2 read in full. 2207.04831v2 partial (char ranges in FULLCANDIDATE section 8). 2607.16810 opening and pattern scan only.
- ordinary: AUTHOR-COMPLETE proof of the literal, in FULLCANDIDATE.md: tau(K_{2,l}) <= max(4, ceil(1+sqrt(2l))). Also tau/sqrt l -> 1/(2 sqrt(ln 2)). Lower bound attributed to source Theorem 4/Lemma 12, read and its Lemma 9 formula matched by hand.
- prior: Three standard searches, all saved, found no sqrt upper bound; follow-up restates the conjecture as open and says a novel refinement or new approach is needed. Bounded; no citation index; finals unread; |E|-1 paper unread.
- novelty: Not claimed; bounded search only.
- significance: See FULLCANDIDATE section 7. Strongest objection: short and elementary, atop follow-up Lemmas 5 and 6. Strongest case: explicit conjecture restated as out of reach, settled with exact constant. Root decides.
- formal: Dormant plan written; no Lean run; no dispatch.
- independent: UNPAID: needs independent adversarial review.
- acceptance: Author candidate only. Credit 0.

### 344764
- binding: mathdb-normalized-chunk-0006.jsonl:4140 line sha 2d75f952c38f9b07
- literal: Read. Literal bound for n >= 12.
- source: 1912.02846 Conjecture 4.2 (printed under the label 4-connected, n>=12) read in extract. 1905.06753v4 passage and Table 3 read in extract.
- ordinary: Literal false: Table 3 maxima 222, 259, 300, 342, 391, 444, 630 exceed the printed bound 220, 258, 295, 340, 388, 440, 629 at n=16..21, 24. Hand check of n=17: stack a, three 5-rings, b has W = 64 + 45 + 90 + 60 = 259 > 258. n >= 25 remains open; Table 3 reaches n=32. The stack is not extremal for larger n.
- prior: Refuting data is printed in the reference the source attributes the conjecture to.
- novelty: None.
- significance: Zero: range correction using a public table.
- formal: Not routed; would need planarity infrastructure.
- independent: UNPAID
- acceptance: NONE, credit 0

### 360343
- binding: mathdb-normalized-chunk-0009.jsonl:4594 line sha f74a0c6ef38624ee
- literal: Read. Transcription defect found: MathDB records n + sqrt(n)/2 + O(1).
- source: 2310.08552 Conjecture 3.16 and Lemma 3.14, Prop 3.15 read in extracted text. Extracted layout places the radical over n/2, i.e. sqrt(n/2); not visually confirmed.
- ordinary: Literal as recorded is false: Lemma 3.14 gives K = n-4+2/(r+2)+(n-1)(2r+3)/(2n+r^2+r-2), and r near sqrt(2n) gives n + sqrt(n/2) - O(1) > n + sqrt(n)/2 + O(1). This is a source-transcription correction. Intended statement PARK: precise gap is the exact maximizer over all threshold codes and an upper bound n + sqrt(n/2) + O(1) over the formula of Prop 3.8.
- prior: Source Lemma 3.14 is public.
- novelty: None.
- significance: Zero: transcription correction. Intended statement unproved.
- formal: Not routed.
- independent: UNPAID
- acceptance: NONE, credit 0

### 359433
- binding: mathdb-normalized-chunk-0009.jsonl:3693 line sha 04d66212d8bade64
- literal: Read. Literal itself says the source proves a stronger explicit bound and is resolved affirmatively.
- source: Assigned source body unread; literal only.
- ordinary: No work; source-own by the literal text.
- prior: Source-own per literal, not body-verified.
- novelty: None claimed.
- significance: Zero: source-own.
- formal: None; no route.
- independent: UNPAID
- acceptance: NONE, credit 0

### 355862
- binding: mathdb-normalized-chunk-0009.jsonl:156 line sha efa6163af4723998
- literal: Read: r(K_{n,n},C4,3) = 2n/3 + O(1) and equality infinitely often.
- source: Assigned source body unread; literal only.
- ordinary: PARK. Needs an exact near-perfect packing with bounded error; conflict-free hypergraph matching gives only o(n). Precise gap: bounded-defect design and infinitely-often exact equality.
- prior: Unchecked.
- novelty: None.
- significance: Unassessed.
- formal: Hard: design existence.
- independent: UNPAID
- acceptance: NONE, credit 0

### 340527
- binding: mathdb-normalized-chunk-0005.jsonl:4927 line sha be1d9c25fbe942a1
- literal: Read: lambda K_n^h decomposes into regular Hamiltonian cycles iff n | lambda C(n,h), large n.
- source: Assigned source body unread; literal only.
- ordinary: PARK. Needs a Baranyai-type all-h cycle-regular decomposition; precise gap: simultaneous regular cycle structure beyond factorization.
- prior: Unchecked.
- novelty: None.
- significance: Unassessed.
- formal: Hard.
- independent: UNPAID
- acceptance: NONE, credit 0

### 321035
- binding: mathdb-normalized-chunk-0002.jsonl:590 line sha ffffc98b1e58366a
- literal: Read: E[C_E(K_n)] = |E| + Theta(n).
- source: Assigned source body unread; literal only.
- ordinary: PARK. Source has O(n log n); precise gap: linear control of the end-phase bad-set growth.
- prior: Unchecked.
- novelty: None.
- significance: Unassessed.
- formal: Random process; expensive.
- independent: UNPAID
- acceptance: NONE, credit 0

### 360013
- binding: mathdb-normalized-chunk-0009.jsonl:4267 line sha 22dfb1f9f1674d52
- literal: Read: Jackson conjecture for all d>2, n <= 4d+1.
- source: Assigned source body unread; literal only.
- ordinary: PARK. Large n is source-own per literal; small-n/all-d remains; precise gap: mid-range d and n.
- prior: Source-own large n per literal.
- novelty: None.
- significance: Unassessed.
- formal: Hard.
- independent: UNPAID
- acceptance: NONE, credit 0

### 369268
- binding: mathdb-normalized-chunk-0011.jsonl:3438 line sha 44d978ad8e128f61
- literal: Read: r(K_n,F_k) = (1+o(1)) n^2/log n.
- source: Assigned source body unread; literal only.
- ordinary: PARK. k=1 is the R(3,n) asymptotic constant itself, a flagship open problem.
- prior: Unchecked.
- novelty: None.
- significance: Unassessed.
- formal: Out of reach.
- independent: UNPAID
- acceptance: NONE, credit 0

### 347656
- binding: mathdb-normalized-chunk-0007.jsonl:2013 line sha 6fd4a753d1cb574f
- literal: Read: k-connected monochromatic subgraph with n-2k+2 vertices beyond 5k - floor(2 sqrt(2k-1)) - 3.
- source: Assigned source body unread; literal only.
- ordinary: PARK. Precise gap: remaining Theta(sqrt k) window; no route attempted beyond the literal.
- prior: Unchecked.
- novelty: None.
- significance: Unassessed.
- formal: Unassessed.
- independent: UNPAID
- acceptance: NONE, credit 0

### 318758
- binding: mathdb-normalized-chunk-0001.jsonl:3334 line sha 00edc4d59d7dece8
- literal: Read: p_c([2]^d,r) = exp(-Theta(d^{1/2^{r-1}})), r fixed.
- source: Assigned source body unread; literal only.
- ordinary: PARK. Source says it cannot prove r=3.
- prior: Unchecked.
- novelty: None.
- significance: Unassessed.
- formal: Hard.
- independent: UNPAID
- acceptance: NONE, credit 0

### 325013
- binding: mathdb-normalized-chunk-0002.jsonl:4539 line sha 94d44773e799b0e2
- literal: Read: f(k) = N_k, MMS threshold.
- source: Assigned source body unread; literal only.
- ordinary: PARK. Precise gap: exact threshold for all k. Literal boundary at small k not checked.
- prior: Unchecked.
- novelty: None.
- significance: Unassessed.
- formal: Hard.
- independent: UNPAID
- acceptance: NONE, credit 0

### 344493
- binding: mathdb-normalized-chunk-0006.jsonl:3871 line sha af6f021aa9de410f
- literal: Read: growth rates of threshold languages converge to about 1.242.
- source: Assigned source body unread; literal only.
- ordinary: PARK. Needs uniform transfer between alphabet sizes.
- prior: Unchecked.
- novelty: None.
- significance: Unassessed.
- formal: Hard.
- independent: UNPAID
- acceptance: NONE, credit 0

### 322706
- binding: mathdb-normalized-chunk-0002.jsonl:2247 line sha a6c0743e9c5c20e5
- literal: Read: c_C(n) = Theta(sqrt n), complete simple games.
- source: Assigned source body unread; literal only.
- ordinary: PARK. Lower bound source-explicit; precise gap: general upper bound.
- prior: Unchecked.
- novelty: None.
- significance: Unassessed.
- formal: Unassessed.
- independent: UNPAID
- acceptance: NONE, credit 0

### 363099
- binding: mathdb-normalized-chunk-0010.jsonl:2328 line sha bf75c12abde9c304
- literal: Read: thresholds L, U for d-dependent random graphs.
- source: Assigned source body unread; literal only.
- ordinary: PARK after route thought. Union of independent d-dependent copies is d-dependent, so part (i) and the existence side of (iii) amplify by ratio. Precise gap: a.s. non-occurrence for p << U needs thinning that boosts to probability 1; intersection only amplifies by a power of p, and color-class thinning yields only a constant.
- prior: Unchecked.
- novelty: None.
- significance: Unassessed.
- formal: Unassessed.
- independent: UNPAID
- acceptance: NONE, credit 0

### 361779
- binding: mathdb-normalized-chunk-0010.jsonl:1017 line sha 9bb3c37248661b5a
- literal: Read: Erdos-Frankl-Furedi N*(t).
- source: Assigned source body unread; literal only.
- ordinary: PARK. Flagship open.
- prior: Unchecked.
- novelty: None.
- significance: Unassessed.
- formal: Hard.
- independent: UNPAID
- acceptance: NONE, credit 0

### 373534
- binding: mathdb-normalized-chunk-0012.jsonl:2656 line sha 3f15f7fd9f28d42a
- literal: Read. Literal says the source proves it.
- source: Assigned source body unread; literal only. Title of the assigned source states the result.
- ordinary: No work; source-own by the literal text.
- prior: Source-own per literal, not body-verified.
- novelty: None claimed.
- significance: Zero: source-own.
- formal: None; no route.
- independent: UNPAID
- acceptance: NONE, credit 0

### 374065
- binding: mathdb-normalized-chunk-0012.jsonl:3178 line sha 59b9adb98dff7ef1
- literal: Read: E[diam]/log N converges for randomly oriented divisor graphs.
- source: Assigned source body unread; literal only.
- ordinary: PARK. Needs a limit constant for a directed-distance process.
- prior: Unchecked.
- novelty: None.
- significance: Unassessed.
- formal: Random structure; expensive.
- independent: UNPAID
- acceptance: NONE, credit 0

### 364399
- binding: mathdb-normalized-chunk-0010.jsonl:3618 line sha cebadea11ec5e0dd
- literal: Read: smooth Dressian cells negligible.
- source: Assigned source body unread; literal only.
- ordinary: PARK. Precise gap: upper count of smooth cells; source notes a gap even at fixed rank.
- prior: Unchecked.
- novelty: None.
- significance: Unassessed.
- formal: Hard.
- independent: UNPAID
- acceptance: NONE, credit 0

### 352130
- binding: mathdb-normalized-chunk-0008.jsonl:1451 line sha 60c0748e4baf1456
- literal: Read: e(H) <= n^2/8 for B_k-free 3-graphs, large n. Literal and status field disagree (open vs solved).
- source: Assigned source body unread; literal only.
- ordinary: PARK. Precise gap: exact stability cleaning beyond the asymptotic.
- prior: Unchecked; status conflict recorded, not resolved.
- novelty: None.
- significance: Unassessed.
- formal: Unassessed.
- independent: UNPAID
- acceptance: NONE, credit 0
