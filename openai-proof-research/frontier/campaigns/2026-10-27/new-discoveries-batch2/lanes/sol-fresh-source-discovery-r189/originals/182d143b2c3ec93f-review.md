# RCS128 independent contribution and eligibility review, round 1

**Verdict: SUBSTANTIAL at the full, unchanged scope. This is conditional on the separate full-proof gate passing the frozen candidate as written.**

This is a contribution and eligibility gate only. As the role requires, I assumed the candidate correct for classification. I did not read the separate proof review (`rcs128-proof-r1/`). I only saw its file names in a search listing. This review is not a proof verdict, acceptance, count change, Lean or formal claim, publication recommendation, or worldwide-priority certificate. Campaign count remains 12/20. Uploads remain stopped.

## 1. Reviewed claim and identity

The author packet is `frontier/campaigns/2026-10-14/fresh-structural-discovery-r37`. It was left in place and unmodified.

| file | SHA256 |
|---|---|
| MANIFEST.json (external anchor) | `a81ea2335db99c097423af9baf5abd272fa556ab6f08d870b8d184ee23bb96a6` |
| candidate.md | `ebfed67a43a306af4788c39300e2a418f82193c826bae130508fd87955d39137` |
| original-scope.txt | `7dfa38dbfdc0298863bbd29c76af27061d9f033cf67aa0800979e3310de1eb60` |
| checkpoint.md | `3ab70804621cccba5319e45b18f21b267b3ac8d3cf15deb1aa59f8d415085bf0` |
| contribution-and-limits.md | `55bc1c355f3b33fc54f329d8ebf044d6f6e0b45c4a2d4b15c0397f5070ab7eab` |
| verify.py | `b1257d66599e6a8713f60f0f8bfea8d45e515c1da74cae0a6d5b79c5fc2a3882` |

Before running anything I read `verify.py`, `checks.py`, `check-new-interfaces.py`, `explore.py` and `search-budget.py`. The only write path is `check-new-interfaces.py --write`, and the replay never invokes it.

- **Correct anchor with `--replay`:** PASS, exit 0. It reports 51 payload files, 13 pinned source bodies, 1 primary PDF and 4 context snapshots.
- **All-zero anchor:** fails with `FAIL: external manifest anchor mismatch`, exit 1.
- **Anchor with the last hex digit changed:** fails the same way.
- **Side effects:** `git status` of the author directory was the same before and after.

`author-identity-replay.json` records this. It establishes identity and author finite diagnostics only.

**Claim reviewed (= `original-scope.txt`, no narrowing).** The scope is:

- every explicitly encoded finite alphabet Σ and involution cm;
- every finite explicitly listed family S;
- a deterministic algorithm, polynomial in total encoded bit size including labels and the involution table;
- output containing s or ρ(s) for every s ∈ S, with length ≤ 2·OPT_RC(S).

Fixed letters, ρ-palindromes, duplicates, substring redundancy, empty words and the empty family are all included. Candidate §§1 and 7 address each of these items. I found no fixed-alphabet, bounded-length, nonpalindromic, promised-period or randomized substitute anywhere in the candidate.

## 2. What is already paid

### 2a. Pinned source (family128 at `fd4aeeb2…`, all of `build/sections/01–07` read)

The source already supplies the following:

- **§02:** the blocking functional, the extension and `(eq:period-rule)` k+1 rules, `lem:counts` (occurrence domination), and `lem:base` (balanced graph, W up/W down).
- **§03:** `lem:recorded`, `lem:layers` (sorted exit-end order statistics), `lem:matching-window`, `lem:agreement` (including equal-period <p), and `lem:max-rotation`.
- **§04:** `lem:ordered-windows`, `lem:band`, `lem:collective` and `lem:host`, the last with child-period ordering, clamped targets and a minimum-period child paying a short contact.
- **§05:**
  - baseline lower-layer rooting with a <2p record;
  - easy root/band branches;
  - threshold search `#{l_i(t)≥H−kp} ≤ k` (`lem:choose-k`);
  - at most k identical-alignment occurrences, so one record lies on a different alignment;
  - collective/individual/request trichotomy;
  - `prop:partition`.
- **§06:** `lem:free-period`, `lem:cycle-contact` (lexmax, b−t<q, list `[a,b),[x,b),[x,F),[a+K,b+K)`) and `thm:connection`.
- **§07:** Euler extraction, the suffix invariant and bit-complexity bookkeeping.

The key architectural fact is that the source is already a **matched pair**: the k+1 surplus of the count rule is exactly what the k-threshold of the connection consumes.

### 2b. Yamano–Shibuya, WABI 2026, LIPIcs 390 art. 2 (DOI 10.4230/LIPIcs.WABI.2026.2)

I read the whole retained extraction (lines 1–739): §§1–6 including Theorems 1–3, 11 and 13, Lemma 12, and the §5.2 DNA encoding. It already pays for:

- **Problem setting.** The SCS-RC problem for an arbitrary involution on a finite alphabet, including the identity (pure reversal).
- **Fixed-word convention.** Formal copies s⁺/s⁻, distinct even when s = rc(s).
- **Reversed-pair cycle selection.** Constrained cycle covers with exactly one orientation per pair. The reverse-complement image F̄ of the matching edges is used. **Lemma 12** shows that no induced cycle contains both u and ū: walk forward from v₁ and backward from v̄₁ until an edge v→v̄ appears, and no such edge exists. So cycles come in reversed pairs and one is chosen from each pair.
- **Both-orientation periodicity.** Lemma 7 (all four orientation pairs inequivalent) and Lemma 9 (critical rotations bounding ov(rc(t_d), t_c)).
- **Orientation-dependent cycle breaking.** Algorithm 1, step 4.
- **Ratio and hardness.** The ratio 8/3. **Theorem 2** gives an exact SCS → SCS-RC reduction. Consequently, any β-approximation for SCS-RC is a β-approximation for SCS.

The candidate uses none of the cycle-cover, critical-rotation or matching-gadget operations.

### 2c. Generic and folklore operations (no credit)

- **Symmetrization.** Running the ordinary algorithm on S ∪ ρ(S) gives 4·OPT_RC (r36).
- **Base plus mirrored connection.** The symmetric base, plus the ordinary source connection B, plus its mirror τ(B), followed by half-Euler extraction, gives 3·OPT_RC (r37 `connection-interface.md`).
- **Orbit-wise maxima.** Even rounding at fixed words.
- **Tagged-component domination for the ordinary k+1 rules.** This is finite-union bookkeeping: the source proof applied to the disjoint pair T, ρ(T).
- **Mirroring of operations on nonself orbits.** This is a routine equivariant template.
- **Elementary quotient Euler extraction.** Euler tours in bidirected and skew-symmetric quotient graphs are a known genre in assembly and graph theory (Medvedev et al. 2007, Kundeti et al. 2010, and the skew-symmetric graph literature). I did **not** read those bodies.

Both generic routes give ratios (3, 4) that are *worse* than the primary 8/3. Every improvement from 8/3 down to 2 must therefore come from material that is neither in the source nor in the primary.

## 3. Operation ledger

| # | Candidate component | Paid antecedent | Residual | Credit |
|---|---|---|---|---|
| 1 | Remove empty words, orbit containment, explicit ρ-closed V | source §02 preprocessing; Y–S substring-free WLOG | trivial orbit version | none |
| 2 | Tagged T, ρ(T) domination of ordinary k+1 rules; orbit max; even rounding; W ≤ 2·OPT_RC | `lem:counts` applied to a disjoint union | bookkeeping | none |
| 3 | **Self-text surplus 2k+1** at *every* phase of a ρ-self-reversed periodic text: an unblocked v gives k+1 copies, and its reflection into the other tagged component gives k more, shifted by δ; unblocked status transfers by reflecting a bracket; the case analysis uses symmetric/even Δ | none: the source rule is k+1; Y–S has no forced counts | a new valid lower-bound inequality, strictly stronger than the symmetric source system (W 6 → 12 on the template obstruction, §4.1) | **core credit** |
| 4 | Balanced graph, τ pairing, fixed-vertex even outdegree, τ-paired closed-walk decomposition with no τ-fixed cycle | `lem:base`; the Y–S Lemma 12 argument pattern | routine adaptation | none |
| 5 | **Phase-specific even tails**: reflection-fixed sorted profiles, adjacent pairs sharing *both* axis vertices although the profiles differ | `lem:layers` sorting only | a new structural lemma replacing a *false* naive claim (identical-profile multiplicity, refuted by `bbcbbc` in r37) | **core credit** |
| 6 | **Odd core**: threshold `#≤2k`, core of 2k−1 layers inside a connected 2k-layer unit, the 2k+1 rule leaving one different-alignment record at the *lexmax* phase, the collective *proof* applied to 2k−1 layers with K=kp, mirror, saving 2p | `lem:choose-k`, the proof of `lem:collective`, `lem:free-period` | a new processing rule whose arithmetic is exactly matched to item 3; it resolves the axis-versus-lexmax mismatch recorded in `folded-threshold.md` | **core credit** |
| 7 | **Spliced, anchored hosts**: E/F splice at shared axes with τ(E)=F; an unchanged anchor; whole-batch flips; reclassification of reflected right-anchored requests into the source's three cases; host on E and mirror on F | `lem:host` (one monotone path), source individual cases | a new routing construction that meets `lem:host` hypotheses in the equivariant setting | credit (secondary) |
| 8 | Baseline-member versus short-record-member distinction | §05 baseline step | small adaptation | none separately |
| 9 | Nonself orbits: canonical lexmax over both orientations; mirrored source group procedure | §05/§06 plus mirror; Y–S Lemmas 7/9 both-orientation comparisons | routine equivariant template | none |
| 10 | Two-port quotient functional graph, twisted lifts, quotient self-loop A→ρ(A) handled by the equal-period agreement bound, omitted-target saving 2q | `thm:connection`, `lem:cycle-contact`, `lem:agreement` | a necessary but largely bookkeeping lift of the source cycle argument | technical support only |
| 11 | Half-Euler: one edge per τ-orbit, giving U/2 ≤ W ≤ 2·OPT_RC | Euler extraction (§07); bidirected/skew-symmetric Euler genre | elementary lemma; the factor-2 *accounting* depends on it | no novelty credit; required support |
| 12 | Full encoded complexity | §07 | routine | none |

## 4. Why the residual is a genuine new construction, not a paid equivariant template

### 4.1 The obvious template is provably false, and I recomputed this independently

Consider the naive equivariant transfer: symmetric source counts (orbit max, even rounding, ordinary k+1 rules), plus any same-budget equivariant connection, plus half-Euler extraction. This would output a word of length ≤ W_sym.

For the identity involution on {b,c} and S = {bbcbbc, bcbbcb, cbbcbb}, my own implementation (`independent_checks.py`) computes W_sym = 6. It does not import any author code and was written from the `02-counts.tex` definitions. An exhaustive search over all words gives OPT_RC = 7 (witness `bbcbbcb`).

Hence **no** such equivariant connection exists for the naive counts. This is a logical refutation and does not rest on search. With the candidate's 2k+1 rule, the same code gives W = 12 ≤ 2·OPT_RC = 14.

The factor-2 RC theorem is therefore *not* obtainable by symmetrizing the source construction: the lower bound itself must change. This disposes of the "routine robust transfer" objection more decisively than an absent statement would.

### 4.2 The obvious composite of paid results does not give the theorem

The candidate's theorem would follow if an orientation with W(orientation) ≤ OPT_RC could be found in polynomial time: the ordinary source would then give 2W ≤ 2·OPT_RC. The natural paid candidate is the orientation of a Yamano–Shibuya minimum constrained cycle cover (Theorem 13).

A seeded bounded probe (400 substring-free instances, seed 20261017) found that this fails for arbitrary tie-breaking. Take cm: a↔b, c fixed, and S = {aaa, aab, abcaa, accc}. Then:

- OPT_RC = 10, by brute force over all 3¹⁰ words (witness `aaabcaaccc`);
- the minimum constrained cycle-cover cost is 10;
- the minimum-cost orientation class {0110, 1001} has W = 11 > OPT_RC (and ordinary optimum 12).

So "Y–S orientation + source" does not certify factor 2. Whether some polynomial tie-breaking works is open: the other minimum class {0000, 1111} has W = 9 ≤ 10, and in r36's instance every minimum-cost orientation has W ≤ OPT_RC = 18 (W = 17, 18, 18, 17, recomputed in `independent-checks.json`). The probe found no instance where *every* minimum-cost orientation fails. That is a bounded negative, not evidence that the route works. Either way, the composite route would itself need a new theorem, and none is known. The candidate bypasses orientation selection altogether: the half-Euler step chooses orientations implicitly.

### 4.3 The new inequality and the new processing are matched

Item 3 is not a free-standing count tweak. It provides **2k+1** occurrences, and the threshold `#≤2k` caps identical-alignment occurrences across 2k layers at 2k. Exactly one different-alignment record is therefore forced, while the odd core (2k−1 layers) still has the source's band inequalities. Paired adjacent profiles (item 5) make the 2k-layer unit connected, so linking the odd core links the whole unit within 2kp and frees 2p.

This is the equivariant counterpart of the source's k+1 ↔ k design. It is the decisive new mechanism, and it is what removes the axis-versus-lexmax obstruction documented before assembly (`folded-threshold.md`). The superseded fixed-word 2(k+1) rule did not remove that obstruction, because it applies only at axis phases.

### 4.4 Self-reversed groups require new structure

The source's sorted layers carry no reflection structure. The naive expectation that reflection-fixed profiles come in identical pairs is false (r37 `bbcbbc` certificate). The phase-tail parity and shared-axis pairing replace it. Splicing (item 7) is needed because `lem:host` requires all records on *one* monotone path, while equivariance forces records onto either member.

### 4.5 TECHNICAL considered expressly

The strongest case for TECHNICAL runs as follows:

- every geometric primitive is a source lemma, or a source proof reused;
- the 2k+1 argument is one reflection paragraph;
- half-Euler is elementary;
- items 9–12 are bookkeeping.

I agree with that description of items 1, 2, 4 and 8–12, and they earn nothing. What lifts the package is different. The direct equivariant transfer is *certified impossible* (§4.1). The available composites are worse than the primary (3, 4) or are uncertified (§4.2). The candidate supplies a new, strictly stronger lower bound together with a processing rule tailored to consume it exactly (items 3, 5 and 6, with 7 supporting). By the campaign's standard, this is a new construction rather than a relabelled chain or a finite-union transfer.

The novelty is **narrow**. It is a new equivariant count–connection interface inside the source's architecture, not a new approach to superstrings. By Y–S Theorem 2, the RC theorem implies the ordinary one, so it must not be presented as an independent proof of the source theorem.

## 5. Scope and eligibility at full scope

- **Full scope only.** The verdict applies only at the full scope. Every scope item is handled inside the one algorithm:
  - fixed letters and fixed words: even rounding, required count 2, fixed-vertex parity, self-text rule;
  - identity involution: the obstruction instance is of this type;
  - empty words and family: §1;
  - duplicates and containment: orbit reduction;
  - bit complexity: §7.

  No part of the credit depends on a restricted class. A restricted class (e.g. fixed-point-free involutions without palindromes) would not inherit this verdict automatically, and no such class is claimed.
- **Chronology.** The target first appears in immutable r36 (manifest `cab89551…`). The scope record was made during exploration, before assembly, and is honestly labelled as not predating exploration. The pre-assembly failures are retained, not hidden:
  - W6/OPT7;
  - identical-profile multiplicity;
  - direct-root shortfall;
  - the axis/lexmax mismatch;
  - the fixed-v-only rule.

  The candidate's g-rule is precisely stated (2k+1 for self-reversed texts, k+1 otherwise; fixed-v 2k+2 is omitted).
- **History.** No developed campaign chain other than r36/r37 addresses RC superstrings or family128 extensions. No accepted finding is relabelled (`history-search.json`).
- **Upstream.** At the pin, the only superstring family is 128, with no companion manuscript (complete nontruncated `preprints-tree.json`; catalogue search). After the pin, upstream has only two PR-lock commits (2026-10-12). Code search for "reverse complement" in openai/math finds nothing. The upstream `lean/OAI/Computability/Superstring/*` files exist and were not read.
- **Literature (bounded).** I found no factor-2 SCS-RC result:
  - the best published ratios are 8/3 (WABI 2026) and 23/8 (CPM 2026, arXiv 2601.15814);
  - the Fici–Kociumaka–Radoszewski–Rytter–Waleń reversal result is a *compression* ratio of 1/2, not length factor 2;
  - buberlo/veriscs packages only ordinary family128.

  This is not a priority certificate.

## 6. Apparent mathematical points, flagged separately

These are pointers for the independent proof gate, not objections and not another review's verdict. Under my role's assumption, none changes the classification. Any repair that alters items 3, 5, 6 or 7 requires a new contribution round.

1. **§5 and §6, collective proof with 2k−1 layers.** `lem:collective` is *stated* for k layers with K=kp; the candidate uses its *proof* with 2k−1 layers and K=kp. I re-read the source proof: it uses only Y=max(b,r_H), the three inequalities, pointwise order and K∈pℤ. The extension looks sound, but the manuscript must cite the proof, not the statement. The same applies to the `lem:cycle-contact` list on the odd core.
2. **§1, case 1.** The reflected bracket must be the nearest-mismatch bracket of the original v *relative to the same alignment of A*. This needs ρ(A) to be a translate of A for the chosen, possibly nonleast, period p. The proof gate should check the δ-offset and alignment carefully when p is not least.
3. **§2, phase parity.** Occurrences are counted modulo each original walk's turn length before normalization to p. The pairing of occurrences between C and τ(C) at the reflected phase should be checked under that modulus. The candidate's use of the exit convention, rather than entry, is essential.
4. **§2, R preserves the pointwise order of profiles.** This is asserted via upper regions. The individual R-fixedness of each order statistic depends on it.
5. **§4, batch flips.** After a flip, the child text becomes ρ(child). `lem:host` needs child texts that differ up to translation from each other and from the host. This holds because the orbits are distinct and child periods are less than q, and it should be stated explicitly.
6. **§1, editorial.** The definition of g is a run-on sentence ("…translate of itself, The actual algorithm…"). This is harmless but should be fixed before any manuscript.

## 7. Findings

### Required (conditions attached to SUBSTANTIAL; none is satisfied by this review)

- **R1. Proof-gate contingency.** SUBSTANTIAL attaches only to candidate SHA `ebfed67a…` and requires an independent full-proof PASS. That pass must cover items 3, 5, 6 and 7 together with the supporting items 10 and 11. If any credited item is repaired or replaced, rerun this gate; credit is not inherited.
- **R2. Exact attribution in any manuscript.**
  - (a) The work is an equivariant extension of OpenAI, *A Polynomial-Time 2-Approximation for Shortest Common Superstring* (Sept 24 2026), pinned at `fd4aeeb2…`. Name the lemmas used verbatim and those used via their proofs (`lem:collective`, `lem:cycle-contact`, `lem:host`).
  - (b) Credit Yamano–Shibuya WABI 2026 for the arbitrary-involution SCS-RC formulation, the formal-copy convention for fixed words, the reversed-pair cycle-selection argument (Lemma 12), which the τ-paired decomposition parallels, the both-orientation comparisons (Lemmas 7 and 9), the 8/3 prior bound, and Theorem 2's implication RC ⇒ ordinary.
  - (c) Credit Jiang–Li–Du 1992 and Yamano–Shibuya CPM 2026 for the prior RC ratios.
  - (d) Credit the parent's substantial proof ideas (new-count reflection argument, odd-core rule, spliced hosts, cycle accounting, baseline distinction, outdegree correction) according to campaign convention.
- **R3. No novelty claim** for items 1, 2, 4, 8, 9, 11 and 12. In particular, the half-Euler lemma must be presented as elementary and placed against the bidirected/skew-symmetric Euler literature.
- **R4. Comparison bodies to read before any manuscript.** Read the following and record results:
  - Yamano–Shibuya CPM 2026 (LIPIcs 369:15; arXiv 2601.15814), full body;
  - Jiang–Li–Du, IPL 44 (1992) 195–199;
  - Medvedev–Georgiou–Myers–Brudno, WABI 2007;
  - Kundeti et al., arXiv 1006.4828;
  - a skew-symmetric-graph Euler/matching reference (e.g. Goldberg–Karzanov);
  - Breslauer–Jiang–Jiang 1997 and Mucha 2013, for extremal-rotation precedents;
  - the Collapsing-framework hierarchical cycle-cover discussion (revised §7.2), for any prior equivariant treatment.

  None of these was read here. Any one could narrow the credit, though nothing found so far suggests a duplicate.
- **R5. Honest motivation.** Retain W6/OPT7 as the reason the lower bound must change. Present the composite-route instance (§4.2) only as "arbitrary tie-breaking fails the W certificate", never as an impossibility of orientation-selection approaches.

### Optional

- **O1.** Add the §4.2 instance and its brute-force check to the manuscript's comparison section.
- **O2.** Fix the §1 run-on and state explicitly where source *proofs*, rather than statements, are reused (§6.1).
- **O3.** Add a small end-to-end executable implementation (diagnostic only). It would help reviewers and readers, since the current replay covers counts and splices, not hosts, cycles or output.
- **O4.** Remark that the fixed-vertex parity condition parallels the self-complementary (even-k) nuisance in bidirected de Bruijn graphs.
- **O5.** State that W ≤ 2·OPT_RC, not ≤ OPT_RC: the factor 2 comes from up cost ≤ 2W *halved* by the half-Euler selection. Without this, readers will expect a 4.

## 8. Limits

Reading, search and check limits are listed in `reading-limits.md`. The finite checks in `independent-checks.json` are diagnostics about routes, not mathematics of the candidate. This review does not adopt or contradict any proof-gate verdict.
