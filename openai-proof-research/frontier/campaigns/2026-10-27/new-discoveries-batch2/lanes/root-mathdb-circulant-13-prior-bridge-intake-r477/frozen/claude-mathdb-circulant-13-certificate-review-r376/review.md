# r376 independent adversarial review: MathDB 372627 (Holub–Kopřiva Conjecture 11)

Reviewer: Claude Opus 5.5 (solo, no children). This is an independent review, not a continuation of the
author lane (r360). Scope is 372627 only. No credit, acceptance, Lean, or manuscript work.
Counts are unchanged: 9 additional / 39 total / next 40.

## Hypothesis under review

MathDB 372627 (statement sha256 `be1fd18e…ea27371`; record created 2026-08-11, status open, 0 solutions,
from corpus chunk 0012 line 1758):

> Let n be even with n ≥ 142, and let G = C_n({1,3,n−3,n−1}). Then λ_(3,2,1)(G) = 11 if 12 | n, and 12
> otherwise.

Source: Holub and Kopřiva, arXiv:2601.12574v2, Conjecture 11. The source states only the case 12 ∤ n ⇒ λ = 12.
The record merges in Theorem 6 (12 | n ⇒ λ = 11) and Theorem 10 (λ ≤ 12 for even n ≥ 142). The only open
content is therefore the lower bound **λ ≥ 12 for even n ≥ 142 with 12 ∤ n**.

## Verdict summary

| Gate | Verdict |
|---|---|
| SOURCE | PASS. Statement, definitions and quantifiers were read in the frozen primary v2 PDF. Live arXiv still shows v2 as latest. The DMGT published version was not reached. |
| MATH | PASS. The full-scope proof is a proved general bridge plus an exact finite certificate. All of it was reimplemented independently and reproduces. Two minor presentation objections, neither blocking. |
| SUBSTANTIVE | Not excluded, for root to adjudicate. It resolves an explicitly posed open conjecture, and no applicable published bridge or endpoint was found. The method is classical and the certificate is tiny; that is a depth caveat, not an exclusion. Family-credit overlap with 372628 and source Conjecture 20 must be decided jointly. |
| NOVELTY | Bounded and not cleared. No prior or successor resolution was found in arXiv (5 queries) or 2 web searches. Not checked: DMGT published version (TLS failure), citing literature, MathDB solution pages (429 HOLD). |
| FORMAL FEASIBILITY | Good. Structured enumeration is small (3,543 DFS nodes for 12 labels; the largest layer has 960 words). No 12^9 brute force is needed. The main cost is the graph-distance ↔ offset bridge in Mathlib. Not started. |

## SOURCE gate

**Freeze before content.** The `input-bindings.json` file (status PASS, 0 failures) was written before any
scientific content was opened. It hash-verified:
- all 82 intake manifest files, with the exact file set;
- all 78 bindings, both the original and the copy;
- all 72 r360 payloads in the intake copy and in the immutable r360 original lane.

The root `verify.py` was not run, because it writes into the intake lane.

**Primary source.** The PDF is `frozen/.../sources/c372627-pdf/body`, sha256
`5c57e3ef6dcdcf67c4d7eef15ab13d825a1da3a0b5ae4c9a4f15a0f03515e0ee`, 713,991 B, arXiv:2601.12574v2 (12 May 2026).
I re-extracted it myself to `work/c372627-pdf-layout.txt` (`pdftotext -layout`) and did not rely on r360's text.

Read in the source:
- the definition of L(3,2,1)-labelings, |f(x)−f(y)| ≥ 4 − dist for dist ≤ 3 (p. 3);
- the span convention: labels start at 0 and λ is the largest label, so span s means labels {0,…,s}, i.e. s+1
  symbols;
- the circulant definition;
- Proposition 5, Table 1, Theorem 6, Proposition 7, Theorem 8, Observation 9, Theorem 10;
- the remark that λ = 13 for n ∈ {38, 64, 114, 118, 140};
- the test "all even n ≤ 500" and Conjecture 11;
- Corollary 14;
- §5 on computation: backtracking per n plus a MILP check, with no general certificate;
- Conjecture 20 and the §4 statements, for family overlap only.

**Live version check (2026-10-31, about 07:45 UTC; `sources/`, each with URL, UTC, status and sha256 in
`record.json`).**
- The arXiv abs page is byte-identical to the r360 freeze (sha `01ee0a56…`).
- The arXiv API `id_list` returns v2, updated 2026-05-12, with no journal_ref.
- The authors' tool page `iti.zcu.cz/Holub/L3,2,1-labelingsofcirculants/` contains only tools: a verifier, an
  existence tester and a MILP generator.
- The CSGT 2024 abstract and the ZČU seminar text are earlier and contain no resolution.
- The DMGT homepage failed with a curl TLS verification error (`error-000`). It was not retried and no TLS bypass
  was used, so the published DMGT version is **not inspected**.

**Wording note.** The record's phrase "the preceding theorem" refers to source Theorem 10. The record's "11 if 12|n"
is a source theorem, not part of the conjecture.

## MATH gate

### Claimed theorem (r360 brief) and status after review

For n ≥ 19, every L(3,2,1)-labeling of C_n(1,3) with labels in {0..11} exists iff 12 | n. No labeling with labels
in {0..10} exists. For even n ≥ 142, labels in {0..12} suffice.

Hence for even n ≥ 142, λ = 11 if 12 | n and λ = 12 otherwise. This is exactly the record's statement, over its
full quantifier range. I reproduced every component independently; status: **verified**.

### Proof as re-derived by me

**(B1) Distance bridge, proved generally.**
- A walk of length ≤ 3 in C_n(1,3) lifts to a walk in Z with steps ±1, ±3 and displacement |e| ≤ 9.
- BFS on Z gives the integer distances
  `{1:1, 2:2, 3:1, 4:2, 5:3, 6:2, 7:3, 9:3}`. Offset 8 has distance 4, and |e| ≥ 10 is unreachable in 3 steps.
- So dist_{C_n}(i, i+r) = min over lifts e ≡ ±r (mod n) with |e| ≤ 9 of dist_Z(e), whenever that minimum is ≤ 3.
- For n ≥ 19, two distinct lifts e ≢ e′ in [−9, 9] cannot be congruent mod n, since |e − e′| ≤ 18 < n. So each
  unordered pair {i, j} at cyclic offset in {1..7, 9} gets exactly one requirement:
  |f(i) − f(j)| ≥ 4 − d with `{1:3, 2:2, 3:3, 4:2, 5:1, 6:2, 7:1, 9:1}`.
- Every other pair is unconstrained.

This confirms the brief's offset table, its threshold n > 6t = 18, and that no edges are missing. Checked
mechanically against BFS on the actual C_n for every n ∈ [19, 400].

Caveat on my small-n test: the field `distance_equivalence_fails_for_small_n: []` uses min-over-lifts, which is
valid for every n. It does **not** show that the window model breaks for n ≤ 18. Breakage there would come from
lift collisions such as offset 9 ≡ 0 when n = 9. This is irrelevant to n ≥ 142.

**(B2) Words ↔ closed walks, proved generally.**
- By (B1), for n ≥ 19 a map f: Z_n → {0..K−1} is a labeling iff every cyclic 10-window satisfies the pairwise
  offset constraints.
- Let V_K be the set of 9-words over K symbols that are valid under offsets ≤ 8. Put an edge v → u when
  v·a is a valid 10-word and u = (v·a) without its first letter.
- Since n ≥ 10, a cyclic word of length n is exactly a closed walk of length n in this graph. Each state is
  determined by the previous 9 letters.

A randomized differential test checked cyclic window validity against labeling validity on the actual circulant:
3,000 words, n ∈ [19, 60], K ∈ {12, 13, 14}, all agreeing. Only 22 of the words were valid, so positive-case
coverage is thin. This test is corroboration, not the proof; (B1) and (B2) are the proof.

**(C1) Exhaustive states.**
- The constraints are pairwise and hereditary, so DFS over prefixes enumerates all valid 9-words.
- A second method, left-extension layer closure, gives the identical set for K = 11, 12, 13.
- Counts: |V_11| = 6, |V_12| = 152, |V_13| = 1,908. Edges: 4 for K = 11 and 128 for K = 12, matching the brief.
- Layer sizes for K = 12: 12, 90, 448, 960, 768, 608, 312, 192, 152.
- As data only, I loaded the r360 certificate JSON. Its state sets equal mine for K = 11 and K = 12; the r360
  code was not used.

**(C2) Lower bound.**
- K = 12: Tarjan finds exactly two nontrivial SCCs. Both are simple directed 12-cycles with constant step +5,
  resp. +7 (mod 12).
- Potential certificate: φ = BFS level mod 12, and every intra-SCC edge satisfies φ(u) = φ(v) + 1. Every
  cross-SCC edge respects the condensation order.
- A closed walk stays in one SCC, so its length is ≡ 0 (mod 12). Hence labels {0..11} force 12 | n for every
  n ≥ 19, odd n included.
- By-product: for n ≥ 19 the only span-11 labelings are f(i) ≡ c ± 5i (mod 12).
- K = 11: the graph is acyclic (no nontrivial SCC), so λ ≥ 11 for n ≥ 19. This replays Proposition 5 on that
  range.

**(C3) Upper bound, independent of the source.**
- Take K = 13 and s0 = (0,5,10,3,8,1,6,11,4). I constructed, by backward layered reachability, explicit closed
  walks at s0 of length 12 and of every even length 142…164.
- Each emitted cyclic word was **validated on the actual circulant** by all-pairs BFS distance.
- Concatenating closed walks at s0 gives closed walks at s0. Writing n = b + 12k with b ∈ {142, …, 152} covers
  every even n ≥ 142, since the six even residues mod 12 are all represented.
- I also materialized and validated the concatenated word for every even n ∈ [142, 400].
- The words are stored in `runs/indep_check.json` (`witness_words`), so the upper bound is reproducible from data
  without any search.
- For n ≡ 0 (mod 12), the 12-cycle word gives span 11.

**(C4) Direct cross-check without windows.**
- Cyclic backtracking on the actual C_n with BFS distances, using f(0) = 0 WLOG by vertex-transitivity and
  downward shift.
- K = 12: a labeling exists iff 12 | n, for n ∈ [19, 40] ∪ {48, 50, 60, 62, 72}.
- K = 11: no labeling exists for n ∈ [19, 30].

This is testing of finitely many n and is corroboration only.

**(C5) Source construction replay.**
- The Observation 9 patterns (n = 50, 76, 126, 130, 152), parsed from my own extraction, are valid labelings with
  maximum label 12.
- The Theorem 10 construction (12-pattern ×k followed by the g(r) pattern) is valid for every even n ∈ [142, 400].
- So the source's upper bound is also usable, and the source construction is sound on this range.
- Source typo: the proof's index ranges are written u_{10k}, but the construction uses 12k.

**Negative tests.** The checker rejected 40 corruptions:
- 39 single-letter corruptions of the witness words;
- the 12-label pattern of length 26.

It accepts the length-24 period.

### Objections (non-blocking)

1. **Threshold wording.** The brief's "n > 6t" lemma should state both uses of n ≥ 19:
   - lifts are unique, so there is exactly one constraint per pair;
   - window states are well defined, which needs n ≥ 10.
   The brief should not suggest that distances themselves change at n ≤ 18.
2. **Witnesses not retained by r360.** The r360 upper runs report `witness_words_valid: true` but do not keep the
   words. This review now supplies explicit, re-validated words.

The brief's claim "agrees with Table 1" holds only for the 12-label existence question. Table 1's values of 13
(the K = 13 infeasibility for small n) were not replayed by anyone and are not needed.

No mathematical error was found. Remaining dependencies: none for the stated endpoint beyond (B1), (B2) and the
finite certificate.

## SUBSTANTIVE gate (root adjudicates)

- **Endpoint.** This is the exact open lower bound of a conjecture explicitly posed in a 2026 paper, now proved
  over the full quantifier range. The proof also gives a stronger and cleaner range, n ≥ 19 including odd n, plus
  the characterization of span-11 labelings.
- **Bridge applicability.** No known theorem or published bridge was found that yields this endpoint. The source's
  own computations are per-n backtracking and MILP up to n ≤ 500, which explicitly left the conjecture open. That
  rules out "known result" status for the endpoint as far as checked.
- **Depth caveat.** Window transfer graphs and period arguments for labelings and colorings of distance graphs and
  circulants are classical. The certificate here is 152 states with two 12-cycles, and the obstruction is
  structurally simple. Under the batch standard this is not an automatic exclusion: shortness and method
  familiarity do not equal a complete applicable prior bridge. The risk is the "routine corollary" judgment, which
  belongs to root.
- **Family overlap.** The same method plausibly targets 372628 (C_n(1,5) odd case) and source Conjecture 20
  (C_n(1,4), modulus 16). Treat these as one method-family for credit. I did not investigate either. The r360
  period run for t = 5 with 14 labels shows non-12 periods, so 372628 differs in shape. That is an observation
  only, not a review of 372628.

## NOVELTY gate (bounded; not cleared)

Checked:
- arXiv API, all returning only the source:
  - id_list 2601.12574;
  - abs:"L(3,2,1)" AND abs:circulant;
  - all:"L(3,2,1)" sorted by date, descending;
  - au:Kopriva AND au:Holub.
- arXiv abs page: unchanged, v2 latest.
- Authors' tool page.
- CSGT 2024 abstract and ZČU seminar text.
- Two web searches (`work/search-log.json`), with no resolution found.

Not cleared:
- the DMGT published version (TLS failure, no bypass);
- citing literature after May 2026;
- MathDB solution pages (zero requests, 429 HOLD);
- zbMATH and MathSciNet, not attempted.

Caveat: the arXiv `all:"L(3,2,1)"` query returning only one paper is suspicious given known L(3,2,1) literature;
the API phrase search likely tokenizes poorly. It is not evidence of absence.

## FORMAL FEASIBILITY

Route:
1. Define L(3,2,1) via `SimpleGraph.dist` on a circulant over `ZMod n`.
2. Bridge lemma for n ≥ 19, following (B1): dist ≤ 3 ⇔ residue in ±{1..7, 9} with the stated distances. This
   needs walk lifting and lift uniqueness, and is the main cost.
3. Cyclic-word ↔ closed-walk lemma, following (B2).
4. Structured completeness of V_12 by prefix-layer enumeration: about 3.5k nodes and 152 × 12 edge checks.
   Kernel `decide` on a verified DFS function, or a layer-by-layer list lemma, is feasible. No `native_decide`.
5. Potential lemma: the two cycles together with the acyclic remainder imply 12 | length.
6. Upper bound: explicit words of length ≤ 164, checked by `decide`, plus a concatenation lemma.

Estimate: moderate, about 1–2k lines, dominated by the distance bridge. Not started, per instruction.

## Provenance, coverage, failures

- Guard: `helper_guard.py` sha256 `825ee0d4…fa45`, with fixed limits (512 MiB, CPU 210 s, wall 230 s) that were
  never raised. Runs used `python3 -B -I` with single-threaded BLAS/OMP. Every run passed in under 3 s; see
  `runs/*.stderr`.
- r360 failure logs reviewed:
  - the v1 brute force that hit the CPU cap;
  - the K = 15 / t = 5 MemoryError and CPU cap (372628 only);
  - n = 45 / 15 labels being inconclusive;
  - the logger delimiter bug;
  - the false-positive challenge flag.
  None is load-bearing for 372627.
- My failures:
  - the DMGT TLS error;
  - one shell `grep` regex-complexity error while scanning the abs page. This was cosmetic; versions were taken
    from the API.
- Zero MathDB, Google, GitHub API/raw, or ScienceDirect requests; no browser use; no external messages.
- Coverage: this is a review of the single reserved record 372627. No coverage counts were changed.

## Files

- `input-bindings.json`: hash refs for the inputs.
- `tools/freeze_inputs.py`, `tools/fetch.py`, `tools/indep_check.py`, `tools/extra_checks.py`.
- `runs/`: stdout, stderr and JSON for each run.
- `sources/<name>/{body,headers,record.json}`.
- `work/`: the source extraction, slide text and search log.
- `manifest.json`: sha256 and size of every lane file except `manifest.json` and `verification-receipt.json`.
- `verify.py`: exits nonzero on any mismatch. `python3 -B -I verify.py` checks the lane manifest and the input
  bindings against the actual originals and intake copies. `--replay` re-runs both checkers under the guard into a
  temporary directory and compares their JSON to the stored outputs.
