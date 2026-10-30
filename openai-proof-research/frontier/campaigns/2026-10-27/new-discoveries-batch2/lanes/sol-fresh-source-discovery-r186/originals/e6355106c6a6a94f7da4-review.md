# T165P135 independent substantial-contribution review, round 1

Provenance: Factory Droid / claude-opus-5-5 / high, 2026-10-20. Reviewer author of original prose: Myeongjin
Kang (no affiliation), CC BY 4.0; original code MIT. Role: contribution review only, CONDITIONAL ON
CORRECTNESS, at the ENTIRE unchanged frozen scope. No correctness verdict, acceptance, count, priority or
worldwide-novelty finding is assigned here; a separate adversarial correctness review has not been dispatched
at the time of writing. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is stipulated true, including its
operative proof operations (per AGENTS.md, upstream truth is not audited).

## Verdict

**SUBSTANTIAL** (conditional on correctness), at the entire unchanged frozen scope.

After the strongest actual reduction (the pinned complete-bipartite preprint's real-signed machinery, its
complete-graphs companion, and the classical Tutte/Levow/Pach-Toth/Szekely parity algebra), no located
statement or composition yields the frozen theorem: exact odd/pair crossing values for K_{m,n} in the
even-adjacent class are absent from every primary body read in full, and the two characteristic-0 operations
that carry the pinned proof (two-sided shift averaging, which divides by 2; the signed detector input
(x_p - x_q)/(Pi'Pi')) fail verbatim in characteristic 2. The author pays the residue with a genuine
characteristic-2 transport whose load-bearing steps are not shadows of the pinned text: a one-sided shift
with exact diagonal bookkeeping replacing the unavailable averaging (Lemma 3), a 0/1 order matrix with an
additive row flip replacing the signed detector input (Lemma 8), and the identification of the even-adjacent
hypothesis with the diagonal-block invertibility condition that makes the rank argument fire (Section 8).
This sits with the campaign's SUBSTANTIAL precedents (t205m, t117q, t088p133) and is distinct from the
TECHNICAL ones (t184i134, where the operative step was literally Kang's Lemma 2.2; t106o133, an archived
routine transfer). REDISCOVERED is not warranted within the bounded searches recorded below: no prior
statement of the theorem, of ocr±/ocr+/pcr+(K_{m,n}) = d_m d_n, or of the transport was found.

## 1. Frozen claim reviewed (entire, unchanged)

Frozen statement SHA-256 1000a115e013b3bc28247fdc03f33b8d4ae3ee8ee2a41ce4da55c79e1081a99d; proof SHA-256
a12854336cc118cc9a49dd96bb72aeb142e618ab3466a2e1dc648ff77bf98f10; detached author anchors FINAL
9e01e0dbcdab7665d6ce58c904291cb3caeaef9e54f5befb023336abe21f6be6, MANIFEST
6b997e3d8605220fc4845528d8213356c792e7d674eab50d7be9d16d4730eae5, REPORT
4ecc09d4de9fe7e2f5e095b7b0ac2215a6665438898378e6ee8c91de6b0e037e. All matched the actual bytes at review
start and again at sealing (Section 10); the author root was never written.

**Theorem (verbatim scope).** For all positive integers m, n, with d_r = floor(r/2) floor((r-1)/2): every
even-adjacent drawing D of K_{m,n} (adjacent edge pairs cross an even number of times; BFK's "weakly
semisimple" class; frozen conventions: distinct vertices, simple continuous edge arcs, finitely many proper
transverse double crossings, no tangencies/triple points) has at least d_m d_n oddly crossing unordered edge
pairs; and a balanced-axis drawing realizes equality. Corollaries within scope: ocr±(K_{m,n}) =
ocr+(K_{m,n}) = pcr+(K_{m,n}) = d_m d_n = cr(K_{m,n}), the last equality by the pinned thm:main. Explicitly
not claimed: unrestricted ocr/iocr/pcr of K_{m,n}; any Harborth tripartite formula. This review assesses
exactly that scope: no narrowing, no renaming, no substitute target. The corollaries are consequences of the
frozen statement plus definitions and are not counted as extra findings.

## 2. Strongest actual reduction and what was unpaid

**Strongest project antecedent: the pinned bipartite preprint** (The-crossing-number-of-complete-bipartite-
graphs-September-23-2026, stipulated true). I read, from the author's authenticated copies (receipts verified
against preprints-tree.json, 13223 entries, truncated=false, tree hash matching), the full bodies of
introduction.tex, intersections.tex, subspaces.tex, detector.tex, conclusion.tex, normalization.tex,
paper.tex, README, references.bib. Its operative machinery, all in characteristic 0:

- (P1) signed intersection matrix J with the 1/2 sigma sigma^T_v vertex correction, and the chord formula
  eq:chord-formula expressing crossing signs through endpoint comparison bits;
- (P2) two-sided (left + right) shift averaging producing a matrix annihilated by the cycle pairing
  z^T J y = 0 — the averaging divides by 2;
- (P3) the additive block relation lem:additive;
- (P4) the subspace intersection bound lem:subspace over R (polynomial filtration / minor multiplicity) and
  cor:rank-sum;
- (P5) the rank detector lem:detector: two-triangle interpolation lem:triangular-basis, B_pq =
  ((x_p - x_q)/(Pi'(x_p) Pi'(x_q))) h h^T, barycentric vanishing, row-subtraction H -> H' onto the Q_s
  support, and the A_Q D_Q A_Q^T factorization;
- (P6) assembly with the even-n vertex-deletion identity n d_{n-1} = (n-2) d_n and the balanced-axis
  drawing.

The pinned paper contains no parity, mod-2, odd-crossing, or restricted-class content; it counts crossings,
not crossing parities, and its theorem is about cr.

**Second payment of the same machinery: the pinned complete-graphs companion**
(The-crossing-number-of-complete-graphs-September-23-2026/build/main.tex), which I fetched independently from
the pinned raw URLs and Git-blob authenticated (fetch_pinned.py; six files OK), and read in full. It proves
cr(K_n) = Z(n) via the same signed cycle-pairing (quoting the bipartite companion's Lemma 3.1) plus a
four-variable polynomial evaluation/total-isotropy argument and an even-node detector. It contains NO parity
or odd-crossing content and no K_{m,n} parity statement. Its existence means the signed machinery (P1)-(P5)
is doubly paid, and that its K_n instance did not by itself produce any odd-crossing consequence.

**Earlier project use.** fresh-substantial-discovery-r2 (candidate cr(K_n - e), independent proof PASS,
contribution review pending, not accepted) used the complete-graphs companion's real-signed machinery,
including its prop:odd subspace argument, over R. No parity/odd-crossing transport appears there.
t184i134-contribution-r1 (TECHNICAL) concerned the same bipartite preprint's ordinary crossing content.
No project antecedent of any odd/pair/parity crossing statement for K_{m,n} was found (Section 8).

**Strongest literature antecedents, actually read** (bodies and extents in Section 7):

- Tutte 1970 and Levow 1972: bodies not obtainable (paywalled; recorded failures). Per the DS21 survey
  (footnote 65; [319] with comment), Tutte's theory is the independent ALGEBRAIC crossing number over Z with
  adjacent coefficients zeroed, and Levow's binary-field version "is not precise enough to decide" whether
  its parameter is the algebraic or the odd crossing number. The classical GF(2) theory, on the record
  available, never decided an exact crossing value for K_{m,n}.
- Pach-Toth 2000 (full text): defines ocr and pcr; Theorem 1 (even edges removable), Theorem 2
  (cr <= 2 ocr^2), Theorem 3 (crossing lemma for ocr), and Lemma 4.1 (idea of Tutte): over GF(2) the
  realizable odd-pair vectors are exactly X̄_C + Gamma + Phi, generated by a reference drawing, edge-over-
  vertex pulls Ȳ_{v,g}, and rotation changes Z̄_{v,sigma}. No exact K_{m,n} values; the general relation
  cr <= 2 ocr^2 yields only a square-root lower bound, never exactness.
- Szekely 2008 (full text, six pages): Theorem 1 gives a correlation-inequality criterion, over all vertex-
  set assignments A_e, equivalent to CR-IODD-optimality of a given drawing, with CR = CR-IODD if the drawing
  is nice. Szekely explicitly records that verifying the criterion is hard and names Zarankiewicz's drawing
  of K_{m,n} as "a natural candidate" — without verifying it. No value is computed for any K_{m,n}. Even a
  verified criterion would conclude iocr-optimality of one drawing; combined with the literature's ignorance
  of cr(K_{m,n}) (Zarankiewicz open), it yields no number. The frozen theorem is not a corollary.
- Szekely 2004 (via Szekely 2008 Section 3's restatement): the ±1 Q-function algebra and formula (6)
  expressing crossing parity of an independent edge pair as a product of four Q-values against a fixed
  cyclic order OC. This is the classical signed parity shadow of (P1); it is a formula about a given
  drawing, not a lower-bound mechanism.
- Fulek-Pelsmajer-Schaefer-Stefankovic 2012 (full text): introduces the frozen hypothesis class itself
  (Rule ±, ocr±; even-adjacent drawings) and ocr+/pcr+; proves separations (iocr < ocr; acr- < acr;
  mon-ocr < mon-ocr+) via monotone ordered graphs; Remark 12 records the ocr± translation question as open.
  No exact values for K_{m,n}.
- Balko-Fulek-Kyncl 2015 (full text): Theorem 1.1 gives mon-ocr±(K_n) = mon-ocr+(K_n) = mon-cr(K_n) = Z(n)
  for MONOTONE drawings of COMPLETE graphs, handling weak semisimplicity by eliminating even adjacent
  crossings. Monotone, K_n only: nothing for unrestricted drawings, nothing bipartite.
- DS21 survey (2017): the ocr/iocr/pcr values rubrics list no exact odd or pair crossing values for K_{m,n};
  the ocr± entry records definitions and separations only.
- arXiv:2610.25204v1 (18 Oct 2026, pre-pin flag-algebra bound 0.96936 Z(n,n)): body grep confirms zero
  parity/odd/semisimple/pair-crossing/Hanani content.

**What was unpaid after the strongest reduction.** A proof that every even-adjacent drawing of K_{m,n}
carries at least d_m d_n oddly crossing edge pairs, with exactness, for all positive m, n. No located source
contains such a statement, and the natural composition — "reduce the pinned proof mod 2" — is blocked at two
load-bearing points, not by notation: (a) the two-sided shift average (P2) divides by 2, an operation that
does not exist over GF(2), so the pinned cycle-pairing step has no mod-2 shadow; (b) the detector input (P5)
uses signs and division ((x_p - x_q)/(Pi' Pi'), half-sign matrices), so the pinned detector has no mod-2
shadow either. The classical GF(2) frameworks that DO exist (Tutte/Levow/Pach-Toth Lemma 4.1) are exactly the
ones the survey records as insufficient to decide exact values.

## 3. The characteristic-2 transport (the actual contribution)

(i) **Parity chord bit (proof Section 2, Lemma 2).** For two properly embedded arcs in a disk, the
alternation parity of the four boundary endpoints equals the sum of four comparison bits. This is the mod-2
shadow of eq:chord-formula; at chord level, parity is classical (Tutte; Szekely's (6); Pach-Toth). Routine
in isolation. (A correctness attention item — an apparent t(u1,·) = 0 typo whose terms cancel mod 2 — is
recorded by the parent and is NOT this review's gate; Section 6.)

(ii) **One-sided shift with exact diagonal bookkeeping (Section 3, Lemma 3).** The matrix J_2(e,f) =
chi(e,f) + t̃_v(e,f) over GF(2) is built from a ONE-sided (left) shift of closed walks; the two-sided average
is unavailable because 2 = 0. The price is tracked exactly: the diagonal J_2(e,e) acquires nonclassical
values (a sum of gap bits delta), and the proof carries them until Section 7, where Phi annihilates diagonal
matrices and Section 4 evaluates only off-diagonal blocks. Lemma 3 (z^T J_2 y = 0 for cycle indicators z, y)
is proved by a direct geometric shift argument, not by citing the pinned averaging. This replacement —
one-sided shift plus an exact accounting of the diagonal junk it creates, with a downstream annihilator
matched to that junk — is not a line-by-line shadow of any located text.

(iii) **Additive block relation (Section 4, Lemma 4).** The mod-2 block relation R_ik + R_i1 + R_1k + R_11
= 0 parallels pinned lem:additive; in characteristic 2 it yields the difference form R_ik = X_i + Y_k
directly. Near-shadow; the char-2 simplification is honest but small.

(iv) **Subspace bound over an infinite characteristic-2 field (Section 5, Lemma 5; Section 6,
Corollary 6).** Pinned lem:subspace is characteristic-free except for one "vanishing on an infinite set"
step; the author moves to an infinite field F of characteristic 2 and transfers the polynomial filtration /
minor-multiplicity proof line by line. This is the routine part of the transport, and it is labelled as a
transfer in the packet.

(v) **Order-matrix detector input (Section 7, Lemmas 7-8).** Two-triangle interpolation (Lemma 7) transfers
to F. The detector (Lemma 8) keeps the pinned skeleton — barycentric identity (7.1), rank-1 blocks B_pq,
support bound, the A_Q D_Q A_Q^T factorization — but replaces the signed input with the 0/1 strict-order
matrix T_≺ (T_≺(p,q) = 1 iff p ≺ q), using x_p + x_q = x_p - x_q ≠ 0 and B_pp = 0 (since 2 x_p = 0) in
characteristic 2, and proves Phi(T_≺) invertible. Choosing the order matrix as the char-2 avatar of the
pinned half-sign input, and verifying the factorization survives, is a genuine substitution, not a
transcription: the pinned B_pq formula divides by Pi'(x_p) Pi'(x_q) and separates points by sign, neither of
which has a mod-2 meaning.

(vi) **Hypothesis-class identification (Section 8).** The even-adjacent hypothesis is used exactly once and
exactly where it is needed: for the diagonal blocks, chi(ip, iq) = 0 forces J_2^{ii} = T_i + Delta_i, an
order matrix plus a diagonal, and (v)'s Phi(T_i) invertibility plus diagonal annihilation make every R_ii
invertible. The off-diagonal blocks are pure crossing-parity matrices bounded by oc_ik via Lemma 8(ii), and
Corollary 6 closes 2 d_m d <= sum rank R_ik <= 2 oc(D). The recognition that "adjacent pairs cross evenly"
is precisely the algebraic condition making the diagonal blocks carry full rank is the conceptual hinge of
the whole transport; it has no counterpart in the pinned paper (where the hypothesis class does not exist)
or in the classical parity literature located (where no such rank mechanism exists).

(vii) **All-positive-m,n completion (Sections 9-10).** The even-n vertex-deletion identity
n d_{n-1} = (n-2) d_n (integer arithmetic, hereditary hypothesis) and the balanced-axis upper bound are
elementary and are the same closing operations as the pinned paper's (P6); credited routine.

## 4. Operation-by-operation table

| # | Frozen-scope operation | Pinned antecedent | Classical antecedent | Verdict on the step |
|---|---|---|---|---|
| 1 | Normalization preserving crossing parities (Lemma 1) | normalization.tex | standard | routine transfer; correctness attention item (round-disk/no-reentry for arbitrary continuous arcs) is the correctness gate's, not this review's |
| 2 | Parity chord bit (Lemma 2) | eq:chord-formula (mod-2 shadow) | Tutte; Szekely 2004 (6); Pach-Toth | classical at chord level |
| 3 | One-sided shift + diagonal bookkeeping, cycle pairing (Lemma 3) | P2 two-sided averaging (NOT a shadow: /2 unavailable) | — | NONROUTINE replacement |
| 4 | Additive block relation, difference form (Lemma 4) | lem:additive | — | near-shadow, char-2 simplification |
| 5 | Subspace bound over infinite char-2 field (Lemma 5, Cor 6) | lem:subspace, cor:rank-sum | — | routine transfer (one infinite-set step repaired) |
| 6 | 0/1 order matrix detector input; Phi(T_≺) invertible; diagonal annihilation (Lemmas 7-8) | lem:triangular-basis, lem:detector skeleton | — | NONROUTINE substitution on a paid skeleton |
| 7 | Even-adjacent = diagonal-block invertibility; assembly (Section 8) | — (class does not exist there) | FPSS define the class; no rank mechanism | NONROUTINE identification |
| 8 | Even-n deletion n d_{n-1} = (n-2) d_n; axis exactness (Sections 9-10) | (P6) identical closing | — | routine, credited |

The paid skeleton (rows 1-2, 4-5, 8) is extensive. The unpaid residue (rows 3, 6, 7) is small in volume but
load-bearing: row 3 exists precisely because the pinned averaging has no characteristic-2 image, and row 7
is the observation that makes the frozen hypothesis class the exact invertibility condition. The verdict
rests on rows 3, 6, 7 jointly, not on any single line.

## 5. Why not TECHNICAL; why not REDISCOVERED; calibration

**Not TECHNICAL.** The campaign criteria exclude results whose conclusion follows by composing located
statements, and assign TECHNICAL where the operative step is a literal prior statement or a routine transfer
of a paid method. Neither fits. (a) No located statement — in the pinned corpus, the project history, or the
primary literature read in full — asserts or implies an exact odd/pair crossing value for K_{m,n} in any
drawing class. (b) The reduction "take the pinned proof mod 2" is not available: its two-sided averaging
divides by 2 and its detector input is signed; both fail in characteristic 2, so the transport required
constructing replacements (Section 3 (ii), (v)) whose validity is not implied by the pinned theorems, and an
identification (Section 3 (vi)) with no antecedent. (c) The classical GF(2) tradition (Tutte 1970; Levow
1972; Pach-Toth Lemma 4.1) supplies the realizability space X̄_C + Gamma + Phi — which the author's Phi map
dovetails with (diagonal junk is exactly Phi-annihilated) — but on the record located it never produced an
exact crossing value for any K_{m,n}; the survey's own comment on Levow is that the binary theory "is not
precise enough to decide". (d) BFK's weakly-semisimple theorem is monotone and complete-graph only; FPSS
introduced the class with the translation question open; Szekely's criterion is unverified for
Zarankiewicz's drawing and computes no values. Unlike t184i134 (operative step = Kang's Lemma 2.2, a prior
statement performing the exact operation) and t106o133 (archived routine transfer), the operative steps here
are constructed, not cited.

**Not REDISCOVERED.** REDISCOVERED requires a prior actual statement. Bounded searches (Sections 7-8) found
no statement of the frozen theorem, of ocr±/ocr+/pcr+(K_{m,n}) = d_m d_n, of any exact parity-restricted
crossing value for K_{m,n}, or of the one-sided/diagonal char-2 transport. If such a statement later
surfaces (most plausibly in the crossing-number literature I could not reach, e.g. Levow 1972's body, or
specialist weakly-semisimple work after 2017), the verdict should be revisited; that is a disclosed limit,
not an UNRESOLVED analysis.

**Calibration within the campaign.** This sits with the SUBSTANTIAL precedents in which the inherited
machinery was extensive but the residual bridge was new and load-bearing (t088p133: HNBUE bridge plus a new
sharp inequality closing a recognized open case; t205m, t117q). The contribution here is narrower than a new
theory: it is a characteristic-2 transport of a pinned mechanism, landing an exact evaluation in a named,
previously valueless class (even-adjacent K_{m,n}, FPSS 2012). The transport is not routine because the two
steps that fail in characteristic 2 are the mechanism's engine and its detector, and because the hypothesis
identification (row 7) is the content that connects a topological drawing class to linear algebra.

## 6. Honest residual limits (not verdict changes)

- Every ingredient is individually small: a mod-2 chord parity, a one-sided shift with diagonal tracking,
  a 0/1 order matrix, a line-by-line field transfer. A reader who weighs "no new tool; the pinned mechanism
  does the lifting" heavily could argue TECHNICAL. My judgment is that the two genuinely blocked steps and
  the class identification constitute the nonroutine operation the criteria ask for; the contrary weighting
  is recorded here honestly.
- The transport leans on the pinned mechanism twice over (the complete-graphs companion pays the same signed
  machinery again), so the marginal method-over-method novelty is the char-2 adaptation alone.
- Correctness is NOT assessed. Parent-recorded attention items include: Lemma 2's apparent t(u1,·) = 0 typo
  (terms cancel mod 2); Lemma 1's round-disk/no-reentry normalization for arbitrary continuous arcs. Either,
  if fatal and unrepairable, would be a correctness matter; this verdict is conditional on correctness and
  assigns none.
- The statement is a restricted-class evaluation: nothing follows for unrestricted ocr/iocr/pcr of K_{m,n},
  and the frozen packet says so. The lower bound oc(D) >= d_m d_n for even-adjacent D is, however, a
  quantitative statement about a drawing class, stronger than a pure crossing-number evaluation.
- Chronology note (preserved as disclosed, not re-certified): the author recorded the freeze at
  2026-10-20T18:22:29Z with substantial characteristic-2 feasibility established prefreeze; I make no
  independent timing certification.

## 7. Comparison sources actually consulted (versions, extents, failures)

All files local under primary/ with hashes in work/acquisition-register.json (recorded 2026-10-20T19:15:25Z).

- Pach-Toth 2000 (math.nyu.edu author copy): FULL text read — definitions, Theorems 1-3, Lemma 4.1
  (realizable odd-pair vectors = X̄_C + Gamma + Phi over GF(2); vertex pulls Ȳ, rotations Z̄).
- Fulek-Pelsmajer-Schaefer-Stefankovic 2012 (JGAA, via DOI): FULL text read — Rule ± / ocr± definitions,
  separation constructions, Remark 12 (ocr± translation open).
- Balko-Fulek-Kyncl 2015 (arXiv:1312.3679): FULL text read — Theorem 1.1 (mon-ocr±(K_n) = mon-ocr+(K_n) =
  mon-cr(K_n) = Z(n)), weakly-semisimple elimination, monotone restriction. An earlier fetch of
  arXiv:1310.5868 returned an unrelated astrophysics paper (mis-typed identifier); discarded.
- Szekely 2008, Ars Math. Contemp. 1(1) 32-37 (amc-journal.eu article 43/30): FULL text read (6 pages) —
  Theorem 1 criterion, formula (6)/(9) restating Szekely 2004, the "natural candidate" remark on
  Zarankiewicz's drawing with no verification. Acquisition failures recorded: amc.imfm.si TLS hostname
  mismatch (not bypassed), people.math.sc.edu copy 404, archive.org wayback 429.
- Schaefer DS21 survey 2017 (byte-identical to the author's receipt, sha256 a03758b9...): read the ocr
  entry (text lines 3216-3256), iocr entry (2511-2543), pcr entry (3278-3334), Levow [319] bib (4850-4852)
  and comment (3224-3228), Szekely [443]/[445] passages, and the cr values rubric. No exact K_{m,n} parity
  values anywhere in the survey.
- arXiv:2610.25204v1: body read; grep confirms zero parity/odd/semisimple/pair-crossing/Hanani content;
  explicitly pre-pin state.
- Tutte 1970 (JCT 8, 45-53) and Levow 1972: bodies NOT obtained (paywalled / no open copy located by
  bounded web search). Relied on: Pach-Toth Lemma 4.1 (restating Tutte's GF(2) coboundary machinery),
  Szekely 2008 Section 3, and the DS21 survey entries including the Levow comment. Recorded as access
  failures, not as content claims.
- Bounded web searches (2026-10-20): "odd crossing number" complete bipartite exact value Zarankiewicz
  parity; "odd crossing number" bipartite weakly semisimple even adjacent; "monotone" "odd crossing number"
  "complete bipartite". Findings: only BFK (already read), the DS21 survey (already read), and generic
  crossing-number pages. No exact parity-restricted K_{m,n} value located.
- Pinned upstream: the bipartite preprint's nine build files read in full from the author's authenticated
  copies (receipts verified); the complete-graphs companion independently fetched from pinned raw URLs and
  Git-blob authenticated against preprints-tree.json (13223 entries, truncated=false) — six files, main.tex
  read in full.

## 8. Project history searches

Actual searches (rg -uu, hidden and ignored included; exclusions per the brief: active
fresh-arithmetic-discovery-r100, t088p133-proof-r1 and any T088 recovery root, other live work, the author
and parent roots of this nominee, this root, .git):

- Alias passes: "odd crossing", "oddly crossing", "even-adjacent", "weakly semisimple", "semisimple",
  "Hanani", "pair crossing", "Zarankiewicz", "Levow", "Pelsmajer", "Balko", and word-boundary ocr/iocr/pcr.
- Operative hits found: (a) this nominee's own roots (excluded as subject matter); (b) NEW-TEN index entries
  describing this nominee (not prior art); (c) fresh-substantial-discovery-r2 (candidate cr(K_n - e); uses
  the complete-graphs companion's real-signed machinery over R, including prop:odd; no parity transport;
  not accepted); (d) t184i134/r134 (ordinary crossing content of the same bipartite preprint; no parity);
  (e) cdf098-contribution-r1/ocr.py — optical character recognition (tesseract), unrelated; (f)
  restricted-host-mixing-r1 (K_n minus a matching, alternating-cycle Markov moves; unrelated); (g) copied
  corpora (literature surveys s.txt/clancy.txt inside r2, catalogue CONTENTS.md copies, family-title lists)
  — copies, not project operations; (h) fresh-structural-discovery-r106 "semisimple degree-zero part" —
  homological algebra, unrelated.
- Conclusion: no project antecedent states, proves, or attempts any odd/pair/parity crossing value for
  K_{m,n}, and no project antecedent performs a characteristic-2 transport of the pinned machinery.

## 9. Positioning requirements for any later manuscript/acceptance record (do not change the verdict)

- PQ1. Keep the restricted-class labelling exactly: even-adjacent (weakly semisimple) drawings of K_{m,n}.
  Never present this as determining unrestricted ocr/iocr/pcr of K_{m,n}.
- PQ2. Novelty wording: "new to this project; no antecedent found in the bounded searches recorded". No
  "first" or worldwide-priority phrasing.
- PQ3. Credit: the pinned bipartite preprint for the mechanism and the cr(K_{m,n}) value; the complete-
  graphs companion (same machinery, no parity content); FPSS 2012 for the ocr± class; BFK 2015 for the
  monotone K_n weakly-semisimple theorem; Pach-Toth 2000 Lemma 4.1 (Tutte's idea) for the GF(2)
  realizability space; Szekely 2004/2008 for the signed parity algebra and the (unverified) optimality
  criterion; Tutte 1970 and Levow 1972 via the survey record (bodies not read).
- PQ4. State that the proof is a characteristic-2 transport of the pinned mechanism, with the one-sided
  shift/diagonal bookkeeping and order-matrix detector input as the new steps.
- PQ5. Keep the correctness-attention items (Lemma 2 typo, Lemma 1 normalization) visible until the
  correctness review disposes of them.

## 10. Evidence and integrity (this review)

- Author inputs: 20 key input files (author anchors, frozen statement/proof/reports/limits/rights/notes,
  verifiers; parent assessment/intake/task-status/handoff/replay/snapshot/brief; common brief; AGENTS.md;
  upstream.json; preprints-tree.json) SHA-256 recorded at sealing in work/input-hashes.txt; the detached
  author anchors FINAL/MANIFEST/REPORT and the frozen/proof hashes match the actual bytes.
- Whole-tree integrity: check-originals.py (in this root) compares the ENTIRE author root against the
  parent original-snapshot.json (paths, modes, nlink, sha256). Result at sealing: exact match; copied input
  unchanged; author root unchanged after controls (integrity-report.json).
- Copied controls in this root (artifact checks, not mathematical gates): author verify.py on a full copy
  reports ARTIFACTS_VERIFIED (11 source bodies, 3 primary receipts, 28 payload files) against the detached
  anchors; author sanity.py on the copy passes checks (a)-(h), including randomized GF(2) identity checks;
  the complete-graphs companion fetch authenticates six files by Git blob SHA-1 and size against the pinned
  tree; the parent replay's external dependencies are unchanged. Originals were never executed or modified.
- This root only: all downloads, scratch, controls and outputs were written inside
  frontier/campaigns/2026-10-14/t165p135-contribution-r1/. No nested agents, no git/shared-index writes, no
  publication/uploads/contacts/browser UI, no formal/manuscript/release work. Private primary/upstream
  bodies remain local under their original rights, separate from this review's original prose (CC BY 4.0)
  and code (MIT).
