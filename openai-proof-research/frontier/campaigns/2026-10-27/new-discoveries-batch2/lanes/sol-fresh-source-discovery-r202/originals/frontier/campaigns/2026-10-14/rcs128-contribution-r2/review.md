# RCS128 independent contribution and eligibility review, round 2

Original prose CC BY 4.0; original code MIT. Third-party bodies retrieved in this round are under `private/` only, with provenance, and must be excluded from any public release.

**Verdict: SUBSTANTIAL (narrowed) at the full, unchanged scope.** The verdict is for candidate SHA256 `ebfed67a43a306af4788c39300e2a418f82193c826bae130508fd87955d39137` exactly.

Credit is now concentrated in one matched package, with nothing else credited:

- the self-reversed-text **2k+1** forced-count rule (item 3);
- its **phase-specific even-tail pairing** of adjacent sorted layers (item 5, residual part only);
- the **odd-core 2k−1** processing at the lexmax phase (item 6).

The Goldberg–Karzanov §5 antecedent removes **all** separate credit from item 7 (spliced/anchored hosts). This is a downgrade from round 1's "secondary credit". Item 7 is now required technical support only.

This is a contribution/eligibility gate only. It is not a proof verdict, acceptance, count change, Lean or formal claim, manuscript PASS, publication recommendation or worldwide-priority certificate. Campaign count remains 12/20. Uploads remain stopped. No nested agents, staging, commits or shared-index edits were made.

## 0. Inputs, identity and what was and was not read

- **Input packet** `rcs128-contribution-inputs-r2/`.
  - I read `verify.py` first. It is read-only: lstat and hash only, and it rejects symlinks, hardlinks and nonregular objects.
  - With external anchor `88bdb8dd5e3273af13ca710d24f0729c5e80ef2d40e463f1bb59e83c487c2c02` it gives `PASS_INTEGRITY_ONLY`: 37 files, 2 directories, exit 0.
  - With an all-zero anchor it gives `REJECT external anchor mismatch`, exit 1.
  - A tamper control on a copy (outside the repository) is recorded in `controls.json`.
- **Prior review identity.** `prior-contribution-review.md` and `prior-contribution-reading-limits.md` are byte-identical (`cmp`) to `rcs128-contribution-r1/review.md` and `reading-limits.md`. The r1 manifest hashes to `3c5eb400…`, as stated.
- **Author packet** `fresh-structural-discovery-r37/` is unchanged, by direct sha256:
  - MANIFEST `a81ea233…`;
  - candidate `ebfed67a…`;
  - scope `7dfa38db…`;
  - checkpoint `3ab70804…`.
- **Proof review.** Per instruction, I did **not** read `rcs128-proof-r1/`. I only hashed its `MANIFEST.json`, which equals `50bf7355f464b4b043d62cdc1ade59d6f268d2d2ccc87f6125ba8b6992dc1a52`, the parent-stated anchor. I read `proof-findings.txt` (optional findings O1–O11) only for statement and attribution consistency. Its PASS verdict plays no role in the contribution classification below.
- **Read in full this round:**
  - `candidate.md` and `original-scope.txt`;
  - `contribution-and-limits.md`, `self-text-rule-and-host.md`, `folded-threshold.md` and `budget-counterexample.md`;
  - source `02-counts.tex` and `05-processing.tex` in full;
  - the `lem:host` statement and proof in `04-connections.tex`;
  - the lemma inventory of 03, 04 and 06;
  - the input packet: `parent-response.json`, `proof-findings.txt`, `provenance.json` and all of `comparison-r4/*.json`.
- **Primary bodies read directly this round:** listed in `reading-limits.md`.

## 1. Scope (unchanged)

The scope reviewed is `original-scope.txt` exactly:

- every explicitly encoded finite alphabet and involution, and every finite explicit family;
- deterministic polynomial bit complexity, including labels and the involution table;
- output containing s or ρ(s) for every s, with length ≤ 2·OPT_RC.

Fixed letters, palindromes, duplicates, substring redundancy, empty words and the empty family are all included. The candidate addresses each of these inside the single algorithm (§1, §7). There is no fixed-alphabet, bounded-length, nonpalindromic, promised-period or randomized substitute. The credited package is used precisely in the self-reversed case, which includes the identity-involution obstruction instance. So credit cannot be inherited by a narrowed class that excludes self-reversed texts.

The chronology is honest. The target appears in immutable r36. The scope record was made during exploration and is not claimed to predate it. Failures are retained: W6/OPT7, identical-profile multiplicity, direct-root shortfall, axis/lexmax mismatch and the fixed-v-only rule.

## 2. Operational credit ledger (fresh; round-1 credit not inherited)

"Paid" means present in the stipulated source, in a read primary antecedent, or a routine equivariant/finite-union template.

| # | Component | Paid antecedent (read) | Residual | Round-2 credit |
|---|---|---|---|---|
| 1 | Empty removal, orbit containment, ρ-closed V | source 02 preprocessing | trivial orbit version | none |
| 2 | Tagged T, ρ(T) domination of ordinary k+1 rules; orbit max; even rounding | source `lem:counts` proof on a disjoint union; **Y–S CPM 2026 Lemma 18** (averages an optimal solution with its reverse complement) | finite-union bookkeeping | none |
| 3 | **2k+1 rule at every phase of a ρ-self-reversed periodic text** | none found; the source rule is k+1; no read primary has forced occurrence counts with reflection surplus | new valid lower-bound inequality (see §3.1) | **core, in package** |
| 4 | τ-pairing of base edges; fixed-vertex even outdegree; τ-paired closed-walk decomposition with no τ-fixed cycle | source `lem:base`; Y–S WABI Lemma 12; **GK §3 symmetric decomposition and Tutte Cor. 3.2** (flow into a self-symmetric set is even); GK §2 (no self-symmetric paths or cycles) | routine adaptation to fixed vertices | none |
| 5a | Generic "symmetric pairing with no self-paired member ⇒ even count" | Tutte/GK Cor. 3.2; Y–S Lemma 12 | — | none |
| 5b | **Phase-specific** even tail #{i: z_i(t) ≥ t+l} surviving sorting (exit convention); adjacent sorted profiles share both axis vertices although profiles differ | source `lem:layers` sorting only | short deduction, replacing a *false* naive identical-profile claim | **core, only as part of the package** (standalone: technical) |
| 6 | **Odd core**: threshold #≤2k, core of 2k−1 layers in a connected 2k unit at the *lexmax* phase, K=kp via the `lem:collective` proof, mirror, saving 2p | source `lem:choose-k` and the `lem:collective` proof (k+1 ↔ k design) | parametric re-design whose arithmetic is matched to item 3 and connectivity matched to item 5b | **core, in package** |
| 7a | Splice two reflection-invariant closed walks at two common points into an exchanged pair (τ(E)=F) | **GK §5 (pp. 15–16)**: two self-symmetric cycles meeting at x and x′ are recombined by complementary halves into a symmetric pair | cut points are σ-fixed axis vertices instead of a mate pair; the algebra E ↦ σ(E)=F is identical | none |
| 7b | Shared-axis existence and staircase order of E, F | existence = item 5b; monotonicity of a concatenation of monotone staircase pieces is immediate | — | none separately |
| 7c | Unchanged anchor, whole-batch flips, reflected requests reclassified into the source trichotomy, deferred case-2 attachments, host on E plus mirror on F | source `lem:host` (one actual period-q path, records of distinct child groups); source case trichotomy (05) | hypothesis-meeting routing: f(a′) ≤ b′ by monotonicity; reapply source cases; mirror | **none: required technical support** |
| 8 | Baseline-pair versus short-record-member roles | source 05 baseline | small adaptation | none |
| 9 | Nonself orbits: lexmax over both orientations; mirrored source procedure | source 05/06; Y–S WABI Lemmas 7/9; CPM Lemma 11; Breslauer 1996 critical/extremal rotations | routine equivariant template | none |
| 10 | Two-port quotient functional graph, twisted lifts, self-loop via equal-period agreement, saving 2q | source `thm:connection`, `lem:cycle-contact`, `lem:agreement` | bookkeeping lift | none (support) |
| 11 | Half-Euler: one edge per τ-orbit | source 07; Medvedev 2007 §2.2 (bidirected balanced Euler); Kundeti 2010; GK bidirected correspondence | elementary; the factor-2 accounting depends on it | none (support) |
| 12 | Encoded bit complexity | source 07 | routine | none |

### Item 7 in light of Goldberg–Karzanov §5 (explicit reassessment)

I read GK §5 directly (arXiv math/0304290, PDF SHA `11e46d81…`, extraction lines 713–760). The operation there is this:

> two self-symmetric cycles C, D meeting at x (hence x′); concatenate the x→x′ path of C with the x′→x path of D, and the rests, giving a symmetric pair.

The candidate's E = D1[U,V]·D2[V,U+(p,p)] and F = D2[U,V]·D1[V,U+(p,p)] is the same exchange of complementary halves. In both settings σ (respectively R) maps each walk's first half onto its second half, which is all that τ(E)=F needs.

The only differences are that the cut points are σ-fixed axis vertices rather than a mate pair, and that the objects are periodic staircases. Neither is a new idea.

- **Existence of the two shared points** is exactly item 5b, which is already counted.
- **Validity of E, F as period-q monotone staircases** is immediate.
- **The anchored routing (7c)** does only what is needed to put the records of distinct child groups on one actual host path, which is the hypothesis of the stipulated `lem:host`. It does so by reapplying the source's own trichotomy, after a one-line monotonicity observation, and then mirroring.

That is the meaning of "routine adaptation to meet a source lemma's hypotheses". I therefore give **no residual credit** to item 7. The candidate's own text lists "spliced/anchored hosts" among "the new work". Any manuscript must narrow this (R3).

## 3. Why the remaining package is SUBSTANTIAL rather than TECHNICAL

### 3.1 The obvious equivariant template is certified false (independently recomputed)

`w_obstruction.py` was written this round from the `02-counts.tex` definitions and candidate §1. It imports no author or round-1 code.

- **Instance:** the identity involution on {b,c} with S = {bbcbbc, bcbbcb, cbbcbb}.
- **Naive symmetric system:** source k+1 rules, orbit max and even rounding at fixed words give **W_naive = 6**.
- **Candidate rule:** the 2k+1 rule gives **W = 12**.
- **Optimum:** exhaustive search gives **OPT_RC = 7** (witness `bbcbbcb`). This also follows by hand: two disjoint length-6 requirement orbits cannot both fit in a length-6 word.

Output is ≤ U/2 ≤ W_naive whenever the equivariant connection fits in budget W. So no same-budget equivariant connection exists for the naive counts. This is a logical refutation from one explicit instance, not a search result. The results are in `w-obstruction.json`.

Consequently the factor-2 RC theorem is **not** a robust transfer of the source: the lower-bound system itself must change. The generic composites read so far are all worse than 8/3:

- S ∪ ρ(S) gives 4;
- base + connection + mirror + half-Euler gives 3;
- Y–S WABI 2026 gives 8/3;
- Y–S CPM 2026 gives 3.75 and 2.875;
- Jiang–Li–Du gives 4, per two independent secondary descriptions.

### 3.2 The change has to be at three matched places, and the obvious single-place fixes fail

The source design is a matched pair: a k+1 surplus (count rule) consumed by a threshold of k (`lem:choose-k`) that keeps k layers within (k−1)p.

In a self-reversed group the layers and the cost both double (a link plus its mirror). An equivariant analogue therefore needs three things at once.

1. **(3)** A surplus of 2k+1 that is valid at the *lexmax* phase, which is generally *not* an axis phase. The new idea is to count the k shifted-phase copies of w inside ρ(v) in the other tagged component.
2. **(5b)** A reason why the 2k-th layer comes for free. That reason is phase-specific even tails, which give adjacent pairs sharing both axes even though profiles differ. The naive "identical profiles pair up" is false (r37 `bbcbbc` certificate).
3. **(6)** A threshold #≤2k whose failure yields an **odd** core of 2k−1 layers within (k−1)p. The `lem:collective` *proof*, not its statement, joins that core at K=kp, so that kp plus its mirror pays 2k layers and frees 2p.

The documented failures show each single-place fix is insufficient:

- the fixed-word-only 2k+2 rule applies only at axis phases and leaves the axis/lexmax mismatch (`folded-threshold.md`, with the explicit `(abcacb)^Z` example);
- the identical-profile pairing is false.

A construction that overcomes a certified obstruction and two concrete failed natural repairs, by a coordinated change to the lower bound and to the processing that consumes it, meets the campaign's standard for a genuine new construction. It is not a relabelled chain or a finite-union transfer.

### 3.3 Strongest TECHNICAL case, considered

Each credited piece is short:

- item 3 is one reflection paragraph on top of the source `lem:counts` proof;
- the parity in item 5 is the Tutte/GK pattern;
- item 6 is `lem:choose-k` with k replaced by 2k and an odd core.

Once the right numbers are guessed, a referee could call it "a careful adaptation". I take this seriously, and it is why the credit is **narrow**. It is still not decisive:

- Brevity is not the criterion. The question is whether a routine equivariant template suffices, and §3.1 shows it does not.
- None of the read antecedents supplies a forced-count surplus from reflection, or a phase-specific parity of sorted occurrence tails. Those antecedents are the source, Y–S WABI, Y–S CPM, GK §§2, 3 and 5, Medvedev, Kundeti, Breslauer 1996, Mucha and Collapsing §7.2.

**Contrary signal.** The source was published 2026-09-24, only weeks earlier. So "experts have not done it" carries no weight here, and I give it none.

### 3.4 Presentation limits

- By Y–S WABI Theorem 2, an RC β-approximation is an ordinary β-approximation. The RC theorem therefore *implies* the stipulated source theorem. It must not be presented as an independent proof of it, and it does not reprove it: it depends on it.
- The contribution is an equivariant count–connection interface inside the source's architecture. It is not a new approach to superstrings.

## 4. R1–R5 disposition (round 2)

### R1. Proof contingency

**Resolved for the contribution gate, by parent report only.**

- The parent reports PASS_FULL_RCS128 with no required repairs on exactly `ebfed67a…`, with proof manifest `50bf7355…`. I confirmed that hash and did not read the content, per instruction.
- What remains is the standing contingency: any repair or replacement of items 3, 5b, 6, or the support items 7c, 10 and 11, voids this verdict and requires a new contribution round. It is **not** inherited by any edited candidate or manuscript text.

### R2. Attribution

**Open: specified, pending manuscript.** The parent's R2a–R2d specification is adequate as a *specification*, with these round-2 amendments:

- **R2b′:** add Y–S CPM 2026 Lemma 18 (averaging a solution with its reverse complement) as an antecedent of the T/ρ(T) tagged-pair viewpoint.
- **R2e (new):**
  - Credit Goldberg–Karzanov (arXiv math/0304290; journal version 2004) §5 for the exchange-of-halves splice.
  - Credit §§2–3 (Tutte's decomposition and Corollary 3.2 parity; no self-symmetric paths or cycles) for the paired-decomposition and parity pattern.
  - Note that GK's involution is fixed-point-free, so the fixed-vertex case is handled explicitly by the candidate. This is not a black-box application.
- **R2f (new):** credit Medvedev et al. 2007 §2.2 and Kundeti et al. 2010 for bidirected balanced Euler tours, as context for half-Euler.
- **R2c:** cite Jiang–Li–Du 1992 only as in the R4 disposition below.

The R2a proof-reuse list must explicitly add the odd-core use of `lem:choose-k`'s proof pattern. Optional proof finding O8 (counting A-aligned starts) belongs to that same item.

### R3. No-novelty boundary

**Open: specified, pending manuscript; amended.**

- The parent's R3 list already includes generic cycle splicing. Round 2 strikes the residual clause "and any residual anchored routing beyond antecedent splicing". **No** anchored-routing credit remains.
- The residual claim is exactly items 3, 5b and 6 as one matched package.
- Item 5a parity is uncredited, as are half-Euler and the bidirected representation.
- The candidate's "new work" sentence (statement section) and `contribution-and-limits.md` table must not be copied into a manuscript unchanged.

### R4. Comparison bodies

**Resolved for contribution disposition; two manuscript conditions remain.**

- **Read with sufficient operative coverage** (parent checkpoint plus my direct reading recorded in `reading-limits.md`):
  - Y–S CPM 2026;
  - Medvedev 2007;
  - Kundeti 2010;
  - Goldberg–Karzanov (§§2, 3 and 5);
  - Breslauer–Jiang–Jiang 1996 report;
  - Mucha 2013;
  - Collapsing §7.2.

  None supplies items 3, 5b or 6. GK §5 removes item 7 credit, as above.
- **Jiang–Li–Du 1992 body remains UNREAD.** This round's bounded retrieval failed: the ScienceDirect page returned HTTP 403 again, and an extended web search found citations only. This is **not** evidence that the paper lacks any relevant content.

  *Materiality decision.* Two independent secondary sources that I read directly describe the paper consistently:
  - Fici et al., arXiv 1511.08431, lines 36–37 and 101–103: "a greedy-like algorithm with length approximation ratio 4" and an unproved NP-hardness remark;
  - Y–S CPM 2026, lines 77–83 and 235–245: an MGREEDY-RC extension of Blum et al. and a cycle-cover view, 4-approx, with TGREEDY 3 noted.

  It is a five-page 1992 note. The credited items are interfaces to a forced-occurrence-count recursion and its sorted-layer and lexmax processing architecture, which first appears in the 2026 stipulated source. Its hierarchical-graph ancestry dates from 2014 and later. Anything in a greedy cycle-cover note would bear on items already given zero credit (orientation and cycle selection).

  I therefore find the gap **not material to the contribution disposition**. It is **not** a reason to block. It remains a **manuscript attribution condition**, and the R4 body requirement may be met in one of two ways:
  - **(a)** read the body (preferred: via institutional access or the authors);
  - **(b)** a justified substitute. JLD is cited only for claims stated in the secondary sources, explicitly sourced as "as described in [Fici et al.; Yamano–Shibuya CPM 2026]". No ratio is transcribed from the search-rendered abstract, and a limitations sentence records that the original body was not consulted.

  Silently treating the paper as read is forbidden.
- **Breslauer–Jiang–Jiang 1997 journal version: equivalence to the 1996 BRICS report is NOT established.** The parent read the full report. Its relevant tools (critical and lexicographically extremal rotations, overlap-versus-period bounds) bear only on items 9 and 10, which have zero credit. No conceivable version difference can increase the candidate's credit or create a duplicate of items 3, 5b or 6. So the gap is **not material to disposition**.

  *Manuscript condition:* cite the journal version bibliographically. Any lemma statement or number taken from the report must be labelled "technical-report version (BRICS RS-96-21)" unless checked against the journal text.
- **The original R4 "before manuscript" requirement is preserved for both items**, in the satisfiable forms above. Neither is waived by me. The parent has not waived it either.

### R5. Motivation boundary

**Open: specified, pending manuscript.** The parent's R5 text is correct and is retained. My recomputation confirms the W6/OPT7 numbers it relies on. The {aaa,aab,abcaa,accc} instance refutes only arbitrary minimum-cover tie-breaking for the W certificate. I did not recompute it this round, and it remains round-1 reviewer evidence.

## 5. Findings

### Required (conditions on SUBSTANTIAL)

- **Q1 (R1).** The verdict applies to candidate `ebfed67a…` only. A repair to items 3, 5b or 6, or to support items 7c, 10 or 11, needs a new contribution round.
- **Q2 (R3, amended).**
  - Item 7 (splice and anchored routing) gets **no** novelty credit. Attribute the splice to Goldberg–Karzanov §5.
  - Item 5a parity is the Tutte/GK pattern.
  - The residual claim is exactly the matched package 3 + 5b + 6.
- **Q3 (R2, amended).** Attribution as R2a–R2d, plus R2b′ (CPM Lemma 18), R2e (GK §§2, 3 and 5, with the fixed-point-free caveat) and R2f (Medvedev/Kundeti). Also add explicit statement-versus-proof reuse for `lem:choose-k`, `lem:collective`, `lem:host` and `lem:cycle-contact`.
- **Q4 (R4).** Before manuscript, meet the Jiang–Li–Du condition by (a) reading the body, or (b) the explicitly flagged secondary-source citation. For Breslauer–Jiang–Jiang, cite the journal version and label any report-only content. Never mark either body as read.
- **Q5 (R5).** Keep the motivation boundary as specified. Present W6/OPT7 as refuting a same-W symmetric connection only.
- **Q6.** No worldwide-priority claim. The literature reading is bounded (§6).

### Optional

- **P1.** In a manuscript, present items 3, 5b and 6 together as a single "doubled surplus ↔ doubled threshold" lemma pair, mirroring the source's k+1 ↔ k. That is where the contribution lies.
- **P2.** Fold the proof-gate optional clarifications O1–O11 into the manuscript. O2 (τ(E)=F at window/edge level only), O3 (vacuous case 1) and O9 (least-period child among surviving case-3 requests) also shrink item 7c's apparent complexity, which is consistent with Q2.
- **P3.** Remark that in GK the cut points are a mate pair, whereas here they are σ-fixed axes. Both depend only on σ exchanging the two halves.
- **P4.** As before, a small end-to-end diagnostic implementation would help readers. It is not required for contribution.

### Apparent mathematical issues

None new. I found no blocking mathematical or contribution issue to escalate to the parent early.

## 6. Limits

Reading, search and check limits are in `reading-limits.md`. The finite recomputation is a diagnostic about the naive route, not mathematics of the candidate. No Lean code was run. This review neither adopts nor contradicts the proof-gate verdict. Integrity checks establish bytes, not mathematics.
