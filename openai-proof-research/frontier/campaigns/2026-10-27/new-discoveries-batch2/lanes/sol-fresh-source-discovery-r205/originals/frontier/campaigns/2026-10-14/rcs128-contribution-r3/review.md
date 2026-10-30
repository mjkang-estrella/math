# RCS128 independent contribution and eligibility review, recovery round 3

Original prose CC BY 4.0; original code MIT. Reviewer: delegated review sub-agent (Factory Droid, Opus 5.5 high, normal service). This directory is the only thing written by this round.

**Verdict: SUBSTANTIAL at the full, unchanged scope, with narrower credit than round 1.** Credit now rests on one interlocking package: the self-text 2k+1 count rule (item 3), the sorted-layer shared-axis pairing lemma (item 5b), and the matched odd-core processing (item 6). Spliced/anchored host routing (item 7) loses its round-1 secondary credit. Phase parity as such (item 5a) earns no credit. The verdict is conditional on the required findings in §7, which are not all satisfied.

This is a contribution and eligibility gate only. It is not a proof verdict, acceptance, count change, Lean or formal claim, manuscript approval, publication recommendation, or worldwide-priority certificate. Campaign count remains 12/20. Uploads remain stopped. Only the parent accepts.

## 0. Round history and what this round relied on

- Round 1 (`rcs128-contribution-r1/`, manifest `3c5eb400…`) returned SUBSTANTIAL. I read its findings and limits only as they appear in the frozen input packet. I did not adopt its verdict; every ledger entry below was reassessed.
- Round 2 failed terminally with "Claude API rate limit reached. Try again later." It wrote no review directory and no verdict. That failure is preserved here as a fact. I did not look for or rely on any round-2 material, and none exists at `rcs128-contribution-r2/`.
- The separate full-proof review (`rcs128-proof-r1/`) was **not read**. I only confirmed that its `MANIFEST.json` hashes to `50bf7355f464b4b043d62cdc1ade59d6f268d2d2ccc87f6125ba8b6992dc1a52`, matching the brief. I used the optional-findings excerpt `proof-findings.txt` from the input packet only for statement and attribution consistency, as the brief permits. The proof verdict did not decide contribution.
- The formal review (PASS_SCOPED_SUPPORT, shallow finite lemmas) provides no contribution evidence and was not consulted.

## 1. Identity and integrity

| object | anchor | result |
|---|---|---|
| input packet `rcs128-contribution-inputs-r2/manifest.json` | `88bdb8dd5e3273af13ca710d24f0729c5e80ef2d40e463f1bb59e83c487c2c02` | `verify.py` read first (read-only; it hashes files and walks the tree). PASS_INTEGRITY_ONLY, 37 files, 2 directories. All-zero anchor: REJECT (mismatch). On a `/tmp` copy, one appended byte in `parent-response.json`: REJECT (changed file). |
| author packet `fresh-structural-discovery-r37/MANIFEST.json` | `a81ea2335db99c097423af9baf5abd272fa556ab6f08d870b8d184ee23bb96a6` | `verify.py` and `checks.py` read first; the only write path is `check-new-interfaces.py --write`, never invoked. `--replay` PASS: 51 payloads, 13 pinned sources, 1 primary body, 4 contexts. Last-digit-changed anchor: FAIL (anchor mismatch). `git status` of the author directory was the same before and after. |
| candidate.md | `ebfed67a43a306af4788c39300e2a418f82193c826bae130508fd87955d39137` | matches the brief |
| original-scope.txt | `7dfa38dbfdc0298863bbd29c76af27061d9f033cf67aa0800979e3310de1eb60` | matches |
| checkpoint.md | `3ab70804621cccba5319e45b18f21b267b3ac8d3cf15deb1aa59f8d415085bf0` | matches |
| contribution-and-limits.md | `55bc1c355f3b33fc54f329d8ebf044d6f6e0b45c4a2d4b15c0397f5070ab7eab` | matches round 1 |

The details are in `input-verification.json`. These checks establish identity and finite author diagnostics only. They are not mathematics.

**Claim reviewed.** The claim is `original-scope.txt` verbatim, with no narrowing:

- every explicitly encoded finite alphabet and involution;
- every finite explicit family;
- a deterministic algorithm, polynomial in total encoded bit size;
- output containing s or ρ(s) for each s, with length ≤ 2·OPT_RC.

Fixed letters, palindromes, duplicates, substring redundancy, empty words and the empty family are all included. The candidate (§§1 and 7) treats each of these inside the single algorithm. I found no restricted substitute.

## 2. Paid antecedents (reassessed)

- **Pinned source family128** (stipulated true; `fd4aeeb2…`). It already provides:
  - forced occurrence counts with the k+1 period rule, and the balanced graph (§02);
  - sorted layers, matching windows, agreement and max-rotation (§03);
  - ordered windows, bands, the collective link and the single-path host lemma (§04);
  - the processing threshold `#{l_i(t) ≥ H−kp} > k`, with "at most k identical alignments, so one record elsewhere" and the trichotomy (§05);
  - free period and cycle contact (§06);
  - extraction and complexity (§07).

  I reread §05 in full this round to test whether the odd-core rule is a relabelled §05.
- **Yamano–Shibuya WABI 2026** (LIPIcs 390:2). It pays for:
  - the arbitrary-involution formulation and formal copies;
  - the reversed-pair cycle selection (Lemma 12);
  - both-orientation comparisons (Lemmas 7 and 9);
  - the 8/3 ratio;
  - Theorem 2 (RC ⇒ ordinary).
- **Yamano–Shibuya CPM 2026** (LIPIcs 369:15). It pays for:
  - the 3.75 and 2.875 greedy ratios;
  - Lemma 11, inequivalence across orientations;
  - Lemma 18, which considers the reverse complement of the entire optimal superstring to bound the share of reversed occurrences.

  Lemma 18 is a further antecedent for the generic device of "use both T and ρ(T)". This is new relative to round 1's ledger. It lowers nothing that was credited, because item 2 was already uncredited, but it constrains how item 3 may be described.
- **Goldberg–Karzanov** (arXiv math/0304290; journal 2004). I read lines 176–215 and 470–529 directly: §2 shows there are no self-symmetric paths or cycles, and §3 gives Theorem 3.1 (symmetric decomposition) and Corollary 3.2 (Tutte parity). I also read lines 710–784 directly: all of §5. GK pay for:
  - paired decomposition with no self-symmetric cycle (item 4);
  - parity of symmetric integer flows across self-symmetric sets (item 5a);
  - **the exchange-of-halves splice**: "suppose two self-symmetric cycles C and D meet at a node x. Then they meet at x′ as well"; the x→x′ part of C is concatenated with the x′→x part of D, and the rests form the mate (§5, extraction lines 746–749).
- **Medvedev et al. 2007 and Kundeti et al. 2010** (parent-read with recorded limits). They pay for the bidirected signed-incidence walks and the balanced connected Euler criterion. This is the antecedent genre for item 11.
- **Breslauer–Jiang–Jiang** (1996 BRICS report read by the parent; I checked it for symmetry terms only), **Mucha 2013** and **Crochemore**. They pay for critical, Lyndon and lexicographically extremal rotations and overlap-versus-period estimates (items 9 and 10).
- **Collapsing framework §7.2** pays for the separation of cycle-cover lower bounds from hierarchical connectivity.

A keyword screen of the BRICS report and the Collapsing paper for reverse, reversal, complement, palindrome, involution, skew, odd and parity found no hits. Mucha's only hits are a reversed alphabet order. None of the read bodies has a forced-count rule for reverse complements, a phase-labelled layer parity, or odd-core processing.

## 3. Operation credit ledger (this round)

| # | Component | Paid by | Residual | Credit (r3) | Change vs r1 |
|---|---|---|---|---|---|
| 1 | Empty removal, orbit containment, ρ-closed V | source §02; WABI WLOG | trivial | none | = |
| 2 | Tagged T, ρ(T) domination of ordinary rules; orbit max; even rounding; W ≤ 2·OPT_RC | `lem:counts` on a disjoint union; CPM Lemma 18 (use RC of the whole optimum) | bookkeeping | none | = (antecedent added) |
| 3 | **Self-text 2k+1 rule** at every phase of a self-reversed periodic text, with the blocked-case argument (nonfixed partner r has the same positive Δ; fixed r has even Δ ≥ 2) | none for the specific inequality; the generic "reflect into ρ(T)" device is paid (item 2) | a new valid forced-count inequality, strictly stronger than the symmetric source system | **core (package)** | narrowed wording |
| 4 | τ pairing, fixed-vertex even outdegree, paired closed walks, no τ-fixed cycle | `lem:base`; WABI Lemma 12; GK §2 and Thm 3.1 | routine | none | = |
| 5a | Even count of occurrences at a fixed phase over paired walks | GK Cor 3.2 (Tutte) type orbit parity; elementary | none | none | **split out, no credit** |
| 5b | **Parity transferred to sorted exit-order statistics; adjacent sorted profiles share both axis vertices although they may differ** | `lem:layers` sorting only | a new structural lemma about the source's layers; replaces the false identical-profile claim (`bbcbbc` certificate) | **core (package)** | narrowed |
| 6 | **Odd core**: lexmax start, threshold `#≤2k`, core of 2k−1 layers inside a 2k-layer unit made connected by 5b; collective proof with K=kp on 2k−1 layers; mirror; saving 2p | §05 threshold design; proof of `lem:collective`; `lem:free-period` | a new processing rule arithmetically matched to item 3 | **core (package)** | = |
| 7 | Spliced E/F hosts, unchanged anchor, whole-batch flips, reclassification into the source's three cases, host on E and mirror on F | **GK §5 exchange-of-halves splice**; `lem:host`; the source individual trichotomy | an orientation choice per child orbit, then application of source cases; proof-finding O3 shows reclassification case 1 is vacuous | **none (required support)** | **secondary credit withdrawn** |
| 8 | Baseline member versus short-record member | §05 baseline | small adaptation | none | = |
| 9 | Nonself orbits: canonical lexmax over both orientations; mirrored source procedure | §05/§06; WABI Lemmas 7/9; CPM Lemma 11; BJJ/Mucha | routine template | none | = |
| 10 | Two-port quotient functional graph, twisted lifts, equal-period self-loop, saving 2q | `thm:connection`, `lem:cycle-contact`, `lem:agreement` | bookkeeping lift | technical support only | = |
| 11 | Half-Euler, one edge per τ-orbit | §07; Medvedev Lemma 1; Kundeti §6; GK bidirected correspondence | elementary; fixed vertices (ε and palindromes) differ from GK's fixed-point-free setting, but the argument is elementary | none (required support) | = |
| 12 | Encoded complexity | §07 | routine | none | = |

### 3.1 Why item 7 loses credit

GK §5 assumes two self-symmetric cycles that meet, and exchanges complementary halves to obtain a mate pair. The candidate's E/F construction is the same exchange. Its meeting points U and V are each fixed by the reflection, and the reflection swaps the two arcs. In GK, the two meeting points x and x′ are swapped. This difference is a routine relabelling of the same principle.

What remains specific to item 7 is:

- choosing which spliced member carries an unchanged anchor;
- reflecting whole child batches;
- re-running the source's three individual cases on reflected requesters before one application of `lem:host`, then mirroring.

These are orientation bookkeeping followed by verbatim source operations. The proof review's optional finding O3 (case 1 is vacuous) confirms that the reclassification adds no new geometric case. Item 7 is therefore required support, with no novelty credit.

The one thing GK does **not** supply is the *existence* of the two shared meeting vertices for two individually reflection-fixed but possibly different staircase profiles. In GK, meeting is a hypothesis. In the candidate, it is a conclusion of the even-tail argument on sorted exit-order statistics. That conclusion is credited once, under 5b, and not again under 7.

### 3.2 Why phase parity itself (5a) earns nothing

An involution without fixed walks pairs occurrences at a reflection-fixed phase, so their number is even. This is the same orbit-counting fact as Tutte's parity corollary (GK Cor 3.2). The new part is narrower. The phase-specific count equals `#{i : z_i(t) ≥ t+l}` under the **exit** convention, so it survives the source's re-sorting. It then forces adjacent order statistics to agree on every fixed-phase threshold indicator, and hence to visit the same axis vertices. That is item 5b.

## 4. Is the residual package (3 + 5b + 6) still substantial?

### 4.1 The routine equivariant template is impossible

Take the identity involution on {b,c} and S = {bbcbbc, bcbbcb, cbbcbb}. The source counts symmetrized by orbit max and even rounding give W_sym = 6. Any equivariant connection plus half-Euler would then output a word of length ≤ W_sym. However, OPT_RC = 7.

- I recomputed OPT_RC = 7 myself by exhaustive search over all words (`opt_bruteforce.py`; witness `bbcbbcb`; 2 optimal words).
- W_sym = 6 is replayed by the author verifier (the assertion `W_sym==6` passed in my run). It was independently recomputed by round 1. I did not reimplement the count recursion this round.

So the factor-2 theorem cannot come from any same-budget equivariant transfer of the source. The lower bound itself has to change. This is a logical refutation of the template, not search evidence about the candidate.

### 4.2 The change is not a mechanical "double every constant"

The chronology preserved in r37 shows that the obvious doublings fail.

- **Fixed-v-only 2(k+1) rule** (`strengthened-fixed-rule.md`, `folded-threshold.md`). This rule is valid and is dominated by N. But it gives a surplus only at actual fixed-axis vertices. The source cycle-opening argument needs the lexicographically maximal start, and the two need not coincide. The witness in `folded-threshold.md`: A = (abcacb)^ℤ, with axis vertices at starts 0 and 3 but unique lexmax at 4.
- **Identical-profile pairing.** This is false (`bbcbbc` certificate).

The adopted mechanism is specific. There are three linked choices:

1. **Item 3.** An *odd* surplus 2k+1 that holds at *every* phase of a self-reversed text. This removes the axis requirement and lets the threshold run at lexmax.
2. **Item 6.** The threshold `#≤2k`, together with the 2k+1 surplus, forces exactly one different-alignment record. The previous failed threshold then gives only 2k−1 qualifying layers, which is an odd core, not 2k.
3. **Item 5b.** This is the only reason the odd core connects to the full 2k-layer paired unit. Without it, the budget accounting `2kp` total, `2(k−1)p` internal and `2p` freed does not close.

None of the three is a relabelling of a source lemma. Each is fixed by the failure of the simpler alternative, and the arithmetic closes only with all three together.

### 4.3 Strongest case for TECHNICAL, considered expressly

The case for TECHNICAL runs as follows:

- each of the three pieces is short;
- item 3 is "the source's k+1 copies plus k reflected copies";
- item 6 is the §05 threshold with 2k in place of k;
- item 5b is order-statistic bookkeeping on an elementary parity;
- after this round, item 7 and item 5a no longer contribute, and the remaining credit is narrower than in round 1.

I accept every factual part of that description. I still do not find it decisive, for three reasons:

1. The campaign standard asks whether the result needs a new construction or a paid routine template. §4.1 certifies that the routine template fails. §4.2 shows that the two most natural non-routine repairs also fail.
2. Item 3 is a new valid lower-bound inequality. It is not implied by applying `lem:counts` to T ⊔ ρ(T); that gives only k+1. Its blocked-case proof uses the RC structure: the partner's equal Δ, and even Δ at fixed r.
3. Item 5b proves the meeting hypothesis that GK §5 must assume.

The package is a new equivariant count–connection interface inside the source architecture. It is not a new approach to superstrings. The substantiality is real but narrow. If the full-proof gate or a later repair altered item 3, 5b or 6, I would expect the classification to be at risk.

### 4.4 DUPLICATE, INELIGIBLE, BLOCKED

- **DUPLICATE: not found.** Among the bodies read, none has an RC forced-count rule, layer parity, or odd-core processing. These bodies are: the source, WABI 2026, CPM 2026, GK §§2–5, Medvedev, Kundeti, the BJJ 1996 report, Mucha, and Collapsing §7.2 (the last several via the parent's records and my spot reads).
  - Bounded web searches this round found nothing beyond the Yamano–Shibuya papers.
  - A public problem listing (tangle-solve ALGO-000168, committed 2026-10-12, label "unverified") still describes factor two for RC superstrings as open. This is weak, unverified context only. It is not a priority certificate and must not be cited as one.
  - The campaign-history screen and upstream checks are inherited from round 1 and the author packet. I did not repeat them.
- **INELIGIBLE: no.** The scope is the full original target, recorded during exploration and honestly labelled. The failures are retained. No accepted finding is relabelled. RC ⇒ ordinary (WABI Theorem 2) means the result must not be presented as an independent proof of the stipulated ordinary theorem. The candidate does not do that.
- **BLOCKED: no.** The unread bodies (§6) do not prevent disposition, for the reasons given there. They remain manuscript conditions.

## 5. Scope

The verdict applies at the full scope only. Fixed letters and words, the identity involution (the obstruction instance is of this type), empty input, duplicates, containment and bit complexity are all inside the one algorithm. A restricted class would not inherit this verdict automatically, and none is claimed.

## 6. R4 reading gaps: explicit dispositions

| body | status | decision for contribution disposition | manuscript condition |
|---|---|---|---|
| Yamano–Shibuya CPM 2026 | parent read the whole extraction; I spot-read lines 60–119, 232–236, 295–303 and 472–480 | satisfied | cite Lemma 18 as the "use RC of the whole optimum" antecedent |
| Medvedev 2007; Kundeti 2010 | parent read with recorded page limits | satisfied (affects only items 4 and 11, which are uncredited) | cite for bidirected Euler; do not import their spectrum theorem |
| Goldberg–Karzanov | §§2–5 (parent); §2 opening, §3.1–3.2 and §5 (me); journal 2004 PDF corrupt, arXiv used | satisfied; **causes the item-7 downgrade** | cite §5 splice and Cor 3.2 parity; distinguish meeting hypothesis from 5b existence |
| Mucha 2013; Collapsing §7.2 | parent read | satisfied | cite as rotation and cycle-cover antecedents |
| **Breslauer–Jiang–Jiang 1997 (journal)** | **journal body unread.** The 1996 BRICS RS-96-21 report was read in full by the parent. Journal metadata: J. Algorithms 24:340–353. MPG.PuRe journal record, fetched this round, has no file. | **Not material.** The report and the journal abstract give the same two ratios (8/3 and 2+25/42 = 109/42). The report contains no reverse/complement/palindrome/parity terms. The candidate's credited items are not rotation tools. A version difference could change the wording of rotation lemmas, not the credited package. Inability to retrieve is not evidence of absence; this is a justified substitute for disposition only. | **OPEN (minor):** cite the 1997 journal version as the archival reference and state explicitly that the operational comparison used the 1996 report; or read the journal body. Do not attribute exact lemma numbering to the journal from the report. |
| **Jiang–Li–Du 1992 (IPL 44:195–199)** | **body unread.** This round: the publisher abstract page returned HTTP 200 (abstract and a partial reference list only; full text paywalled). The abstract describes "a simple greedy algorithm" with an approximation bound rendered as "4n" (glyph-corrupted). Independent descriptions: Fici et al. 2015 (arXiv 1511.08431 abstract: "greedy-like algorithm with length approximation ratio 4", for reversals); CPM 2026 body (MGREEDY extension 4-approx, TGREEDY remark 3, "considered reversals"); WABI 2026 body ("presented a 3-approximation"). | **Not material.** The credited package is defined over the forced occurrence counts, sorted layers and lexmax processing of a September 2026 source. A five-page 1992 greedy note whose visible references end in 1991, independently described by three later primary texts as a greedy merge analysis, cannot plausibly pay items 3, 5b or 6. A remark about self-reversed strings in JLD could at most touch uncredited items 1–2. This is a justified substitute for disposition, **not** a reading. | **OPEN:** before any manuscript, either obtain and read the body, or cite JLD only "as described by [Fici et al. 2015; Yamano–Shibuya 2026]" with an explicit note that the body was unavailable. Never transcribe the ratio from the corrupted abstract. Reconcile the WABI "3" and CPM "4 (+ remark 3)" descriptions. Contacting authors or using paid access is an outward action that needs the parent's or user's decision; I did neither. The parent has not waived R4; this review does not waive it either. |

## 7. Findings

### Required (conditions on SUBSTANTIAL)

- **RQ1 (R1, proof contingency).** The parent reports PASS_FULL_RCS128 with no required repairs on exactly candidate `ebfed67a…`, at proof-review manifest `50bf7355…`, authenticated and replayed by the parent.
  - **Status: SATISFIED AS REPORTED BY THE PARENT, NOT INDEPENDENTLY CHECKED HERE.** I verified only the manifest hash. I did not read the review.
  - SUBSTANTIAL attaches only to candidate `ebfed67a…`. Any repair or replacement of items 3, 5b or 6, or of supporting items 4, 7, 10 or 11 in a way that changes them, requires a fresh contribution round. Credit is not inherited.
- **RQ2 (credit boundary; R3 update).** The residual novelty claim is exactly the package 3 + 5b + 6, stated as one interface.
  - No novelty may be claimed for item 7 (splicing, anchors, batch flips, reclassification) or for phase parity as such (5a). This is in addition to the parent's list (1, 2, 4, 8, 9, 10, 11, 12, generic splicing).
  - The candidate's "The new work is …" sentence and the host, cycle and output rows of `contribution-and-limits.md` must not be copied into a manuscript.
  - **Status: specified here; not implemented** (no manuscript exists).
- **RQ3 (R2, attribution).** R2a–R2d stand as specified in the parent response: proof-level reuse of `lem:collective`, `lem:host` and `lem:cycle-contact`; Yamano–Shibuya WABI and CPM; parent author roles. Add:
  - Goldberg–Karzanov §5 for the exchange-of-halves splice. State that GK assume the meeting, while 5b proves it.
  - GK Cor 3.2 (Tutte) for the parity principle.
  - CPM Lemma 18 for reflecting the whole optimum.
  - Medvedev 2007 and Kundeti 2010 for bidirected Euler extraction.
  - BJJ, Mucha and Crochemore for extremal rotations.

  **Status: specified; not implemented.**
- **RQ4 (R4, bodies).** All R4 items are satisfied or not material for disposition (§6). Two manuscript conditions stay **OPEN**:
  - the Jiang–Li–Du 1992 body;
  - the BJJ 1997 journal-version citation.

  Neither prevents this disposition. Neither is waived.
- **RQ5 (R5, motivation).** Use W6/OPT7 only to refute a same-W symmetric connection and to motivate changing the counts. Use `{aaa, aab, abcaa, accc}` (a↔b, c fixed) only to show that arbitrary minimum-cycle-cover tie-breaking can fail the W certificate; it is not an impossibility of orientation selection.
  - I independently confirmed OPT_RC = 7 and OPT_RC = 10 by exhaustive search.
  - I did **not** recompute W = 11 or W = 9 for the second instance; they come from round 1.
  - **Status: specified; not implemented.**

### Optional

- **O1.** Present items 3, 5b and 6 as one theorem-level interface ("odd phase-free surplus ↔ odd core ↔ shared-axis completion"). Include the (abcacb)^ℤ axis/lexmax example, so readers see why the fixed-v 2(k+1) rule is not enough.
- **O2.** State in the manuscript that `lem:collective` is used via its proof with 2k−1 layers and K=kp, and that `lem:host` is applied only after its hypotheses are re-established on E (round 1 finding, retained).
- **O3.** Present the splice at the level of labelled edges and windows, matching proof-finding O2 and GK's flow-level splice. Avoid copy-level τ(E)=F language.
- **O4.** A small end-to-end executable diagnostic (hosts, cycles, output) would help readers. It is not evidence of correctness.
- **O5.** Do not cite the tangle-solve listing or any search outcome as evidence of priority.
- **O6.** Fix the §1 comma splice in the definition of g.

## 8. Apparent mathematical points

I found no new blocking mathematical or contribution issue, so there was nothing to escalate to the parent early. The round-1 pointers (§6 there) were for the proof gate, which the parent reports has passed. I did not re-audit the proof.

One observation is relevant to contribution only. The phase-freedom of item 3 depends on choosing the offset δ inside ρ(v), at the translated phase, so that k copies of w fit (proof-finding O8 refines the counting phrase). If that phase-free step failed, the package would collapse back to the fixed-v rule, and the axis/lexmax mismatch would return. The credit depends on it.

## 9. Limits

See `reading-limits.md` and `search-log.json`. The finite checks are diagnostics about the motivating instances, not mathematics of the candidate. No worldwide-priority claim is made.
