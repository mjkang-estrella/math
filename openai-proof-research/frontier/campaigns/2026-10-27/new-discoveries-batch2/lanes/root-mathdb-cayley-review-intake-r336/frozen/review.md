# Independent adversarial review — MathDB 364119 (Cayley-avoidance maximum inequality, Conjecture 8.8)

- Reviewer lane: `pi-cayley-avoidance-preliminary-review-r333` (SOLO, no children)
- Reviewed at: 2026-10-31T01:21Z–2026-10-31T01:55Z (real UTC clock throughout)
- Input: frozen delivery `root-mathdb-breadth-intake-r332/frozen/`, hash-verified **before** content review (63/63 files match the root manifest, including the documented-excluded `verification-receipt.json`, hashed separately). Flat immutable refs reused in place; no recursive copies. See `work/frozen-delivery-manifest.json`.
- Candidate: refutation of Conjecture 8.8 of Cerbai–Claesson–Ernst–Golab, *Pattern-avoiding Cayley permutations via combinatorial species*, with witness p=1122, q=1112 (same length 4, max 2 = 2), |Cay_5(1122)|=520 < 522=|Cay_5(1112)|, total Cayley words of size 5 = 541.

Verdict summary: **SOURCE: PASS-WITH-CORRECTIONS · MATH: VALIDATED · SUBSTANTIVE: SUBSTANTIVE · NOVELTY: NO-PRIOR-REFUTATION-FOUND (not adopted as new-to-literature) · FORMAL-FEASIBILITY: FEASIBLE · DISPOSITION: INVEST.** No acceptance or count changes (9 additional / 39 total / next 40 unchanged).

---

## 1. SOURCE — literal primary definitions in both retained versions

### 1.1 Definition of pattern containment

**arXiv:2407.19583v1** (retained `sources/2407.19583v1.html`, Section 4, element `S4.p2.m6`; excerpt preserved in `evidence/arxiv-v1-definition-excerpt.txt`): w contains p if there is a subsequence w_{i_1}…w_{i_k} with

- LaTeX annotation, verbatim: `i_{1}\leq i_{2}\leq\ldots\leq i_{k}` — **nondecreasing**,

that is order-isomorphic to p (w_{i_a} < w_{i_b} ⟺ p_a < p_b and w_{i_a} = w_{i_b} ⟺ p_a = p_b).

**Published AJC PDF** (retained `sources/ajc_v94_p267.pdf`, p. 280, journal page; PDF page 14; excerpt preserved in `evidence/ajc-p280-definition-excerpt.txt`), same sentence with:

- **i_1 < i_2 < · · · < ik — strictly increasing.**

The two retained versions **disagree**. This is the exact point the root flagged (r332 DECISION.md): the proposal says "indices nondecreasing allowed", the root asked whether the source requires strictly increasing distinct positions.

**Resolution (explicit, against the arXiv v1 typo):** the *published* definition requires **strictly increasing indices — distinct positions; a tied pair of pattern letters is realized by two equal letters at two distinct positions**. Three independent grounds:

1. The published PDF (authoritative, later: PDF CreationDate 2026-02-17, volume 94(2) (2026)) corrected `≤` to `<`.
2. The arXiv nondecreasing reading is self-refuting inside the source: it would let one position serve two tied pattern letters, making every word contain 1^k (choose i_1=…=i_k), contradicting the paper's own Example 4.1 (Cay(1^k) = L(E_1+…+E_{k−1}) ≠ ∅), and it would give |Cay_3(112)| = 4, contradicting the paper's own Corollary 6.8 (|Cay_n(112)| = (n+1)!/2, giving 12 at n=3). The strict reading reproduces both.
3. My independent recomputation reproduces Corollary 6.8 exactly (n=2..6) under the strict reading and fails under the collapsed reading (§2).

**Neither implementation copies the typo:** both frozen scripts (`scripts/decisive_cayley.py`, `scripts/verify_cayley_indep.py`) enumerate subsequences with `itertools.combinations` (strictly increasing indices, distinct positions) and preserve ties (rank-type / pairwise equality). So the two implementations use the same literal definition as the published source. The **proposal and disposition text** ("indices nondecreasing allowed, i.e. i_1≤…≤i_k") is a faithful quotation of the arXiv v1 typo and is **wrong**; it must be corrected in any accepted record. Per instructions this typo/domain correction earns **no credit** — but it also does not invalidate the counts, which correspond to the published strict definition.

Other definition pins (all resolved consistently in both versions): Cayley permutations are packed words (letter set = [1..max]); avoidance is over *all* Cayley words of the given length (no restriction on pattern lengths or alphabet beyond packedness); the §8 preamble "Let p and q be two Cayley permutations of the same length. Can we prove or refute any of the following conjectures?" scopes Conjectures 8.5–8.8 — the witness pair satisfies same-length. `Cay_k(p)[n]` (max letter exactly k) and `[k]^n(p)` are distinct notions; Conjecture 8.8 uses `|Cay_n(p)|`, an otherwise-undefined shorthand whose only consistent reading is |Cay(p)[n]| (avoiders of any max letter). The certificate works under that reading; under a max-letter-restricted reading the inequality direction can also be checked (not needed for the counterexample as stated).

### 1.2 Conjecture 8.8 as published

AJC p. 296 (excerpt preserved in `evidence/ajc-p296-conjecture-8.8-excerpt.txt`), verbatim: "Conjecture 8.8. If max(p) ≤ max(q), then | Cay_n (p)| ≥ | Cay_n (q)|." It is the last item before the references; **no resolution, retraction, or counterexample appears in the published version**. The arXiv v1 states it identically.

### 1.3 Citation corrections required (no credit; record hygiene)

1. **Year:** the proposal/disposition cite "Australas. J. Combin. 94(2) (2025) 267–299". The published running head and AJC landing page say **Volume 94(2) (2026), pages 267–299** (received 2025-03-15). Correct citation year: **2026**.
2. **Page:** the disposition's evidence level says "AJC 94(2) p.295"; Conjecture 8.8 is on **p. 296** (journal numbering).
3. **Definition sentence:** "indices nondecreasing" → "indices strictly increasing (published); arXiv v1 has a `≤` typo".

## 2. MATH — independent re-derivation (fresh implementation, exact finite universe)

Script: `scripts/independent_cayley_check.py`, run under the pinned helper guard (`sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py`), `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1`. Guard report: **exit 0, peak group RSS 18,669,568 B, wall 2.16 s** (limits 512 MiB / 230 s). Written from the published strict definition **before** opening the candidate's scripts; the candidate scripts were read only afterwards (§1.1) to pin their semantics.

**Method A (brute force, two independent containment predicates).** Enumerate all words in [m]^n, m=1..n, keep packed words (|letter set| = m) — the complete universe, no generation gap. Containment checked (i) by pairwise comparison against the pattern and (ii) by value-rank normalization (the paper's std map) of every 4-element subsequence; both predicates agree word-by-word on every input used. Totals match the Fubini numbers for n=1..7 (541 at n=5, 4683 at n=6).

**Results (exact):**

| n | total | avoid(1122) | avoid(1112) |
|---|-------|-------------|-------------|
| 4 | 75 | 74 | 74 |
| 5 | **541** | **520** | **522** |
| 6 | 4683 | **4340** | **4394** |

520 < 522 at n=5 and 4340 < 4394 at n=6 — the claimed counterexample **reproduces exactly**, including the persistence claim.

**Method B (human-readable counting certificate, complete case analysis).** For n=5, classify by max letter m (counts: m=5: 5!=120; m=4: 4!·S(5,4)=240; m=3: 3!·S(5,3)=150 (profiles 3+1+1: 3·20, 2+2+1: 3·30); m=2: 2^5−2=30; m=1: 1; total 541). Under strict indices:

- **Contains 1122** ⟺ ∃ i<j<k<l with w_i=w_j=a, w_k=w_l=b, a<b, i.e. two letters a<b of multiplicity ≥2 with an a-pair entirely before a b-pair.
  - m∈{1,4,5}: impossible (m=1: no a<b; m=4: one doubled letter only; m=5: all distinct). m=3 profile 3+1+1: only one doubled letter → impossible.
  - m=2, two 1s + three 2s: need both 1s with ≥2 twos after the later 1 ⟺ later 1 at position j≤3: arrangements C(5,2)=10, j=2: 1, j=3: 2 → **3**.
  - m=2, three 1s + two 2s: need two 1s before the first 2 ⟺ first 2 at position p≥3: (p,q)=(3,4),(3,5),(4,5) → **3**.
  - m=3, profile 2+2+1 (single letter s∈{1,2,3}, 30 arrangements each): condition "second smaller-doubled letter before first larger-doubled letter"; by direct enumeration of position pairs: **5 of 30** for each s (e.g. s=1: {1-pos}⊂… pairs (A,B), max A < min B: 3+1+0+1 = 5) → **15**.
  - **Total contain(1122) = 3+3+15 = 21 → avoid = 541−21 = 520.**
- **Contains 1112** ⟺ ∃ i<j<k<l with w_i=w_j=w_k=a, w_l=b>a, i.e. a letter of multiplicity ≥3 with a larger letter after its 3rd occurrence.
  - m=2, three 1s + two 2s: 3rd 1 before some 2 ⟺ 3rd-1 position < max(2-position); (p,q)=2-positions: holds iff q=5 → **4**.
  - m=2, four 1s + one 2: need 3 ones before the 2 ⟺ 2 at position ≥4 → **2**. (Two 1s + three 2s: 0.)
  - m=3, triple 1 (1,1,1,2,3; 20 words): contains ⟺ last 1 not at position 5; last-1-at-5: C(4,2)·2=12 → **8**.
  - m=3, triple 2 (1,2,2,2,3; 20 words): contains ⟺ 3rd 2 before the 3; 3 at position r: r=4: 1, r=5: 4 → **5**. (Triple 3: 0 — no larger letter.)
  - m=1 (11111): no larger letter → 0. m=4 (2+1+1+1), m=5: no letter of multiplicity 3 → 0.
  - **Total contain(1112) = 4+2+8+5 = 19 → avoid = 541−19 = 522.**

Both totals are cross-checked inside the script (Method B vs Method A: `matches_method_A: true`, `expected_21_19: true`). The certificate is complete — every multiplicity profile is accounted for; no case is skipped.

**Symmetry cross-check:** the reverse/complement orbits agree with the computed table: {1122,1212,1221,2112,2121,2211} all avoid-count 520; {1112,1121,1211,2111,1222,2122,2212,2221} all 522; 1111 → 530. Consistent with the paper's Proposition 8.1-style orbit equivalences.

**Source-known controls (all exact):**
- C2: |Cay_n(112)| = |Cay_n(122)| = (n+1)!/2 for n=2..6 (Cor. 6.8): 3, 12, 60, 360, 2520. ✓
- C3: |Cay_n(13442)| = |Cay_n(14233)| for n ≤ 7 (the paper's own Conjecture 8.6 computational check): 1, 3, 13, 75, 540, 4640, 46078. ✓
- C1: totals = Fubini n=1..7. ✓
- Sanity: permutations of size 5 avoiding 132 = 42 = C_5. ✓

**Adversarial controls:**
- The arXiv-typo (nondecreasing/collapsed) semantics gives avoid counts **16 and 16** at n=5 — decisively different from 520/522, so the delivered counts are not an artifact of the typo reading.
- The witness is not an isolated artifact of my predicates: I re-checked **all 60 same-length violation records** in the candidate's delivered sweep slice against my own machinery — every n=5 entry matched exactly, and the n=6 entries re-checked exactly (4337/4338/4340).
- **My own two implementation bugs, found and fixed during the review, are preserved** (`scripts/reproduce_reviewer_bugs.py`, `work/preserved-failures.json`): (F1) first-appearance normalization is not an order-isomorphism invariant — it wrongly makes 2211 contain 1122; (F2) tuple-vs-list comparison silently disabled a predicate. Both are documented with exact reproducers; neither survives in the final checker.

**Candidate evidence defects (recorded, none affecting the decisive counts):**
1. `frozen/work/decisive-cayley-validation.json` contains a **failed control**: the |Cay_n(112)| row has `"ok": false` with counts equal to Fubini totals (3, 13, 75, 541, 4683) — its containment predicate never fired for that pattern; and its 13442/14233 check reports `equal: false` with q-side counts equal to totals (broken containment for 14233). This is a stale/buggy earlier run delivered as evidence. My independent C2/C3 runs confirm the *correct* values, so the defect is cosmetic to the refutation but must not be presented as a passed control.
2. `frozen/scripts/verify_cayley_indep.py`'s `fubini5_check` enumerates `product(range(1,5), …)` — letters 1..4 only — yielding 421, not 541; the label is wrong (missing the 120 words with max letter 5).
3. `frozen/work/decisive-cayley-sweep.json` reports 45,324 "violations" of Conjecture 8.8 without applying the §8 same-length hypothesis; most are out-of-scope pairs. The same-length slice is consistent (checked above), but the raw count must not be quoted as "45,324 counterexamples".

## 3. NOVELTY / DEDUP — exact historical and accepted-scope check

- **In-project:** `frozen/frozen/r304-accepted-exclusions.json` and `frozen/frozen/r304-historical-dispositions.json`: **zero** occurrences of Cayley / 2407.19583 / Cerbai / Claesson. A grep over all campaign lanes: only the proposing lane (pi-mathdb-primary-qualified-breadth-r327) and r332 reference 2407.19583; the "cayley" hits in Jacobi-era lanes are unrelated Cayley objects. **No in-project duplicate.** 364117 (automaton retirement lead) and 371547 (edge-irregulator overlap flag) were not touched; they remain separate.
- **Closest predecessor (primary body):** Section 8 of the same paper — Prop 8.1's equivalence classes, Conjectures 8.5–8.7, and the 13442/14233 witness for 8.6. None of these states or implies the 8.8 counterexample; the paper explicitly leaves 8.8 open (verified verbatim in the published PDF, p. 296).
- **Named follow-ups, fetched lawfully (actual URLs/UTC in `evidence/provenance.json`):**
  - Cerbai–Claesson, *Counting fixed-point-free Cayley permutations*, arXiv:2507.09304 (v4 2026-03-14; journal DOI 10.1017/S0013091526101436): **no mention, resolution, or refutation of Conjecture 8.8** (its Section 8 is unisort species; open problems there are unrelated).
  - Cerbai–Claesson, *Hertzsprung patterns in Cayley permutations* (akc.is paper 054, dated 2026-10-26 — five days before launch): different containment notion (Hertzsprung/consecutive); **no mention of Conjecture 8.8**; its Wilf question concerns self-overlap polynomials and the increasing pattern.
  - Cerbai–Claesson, *Simple Cayley permutations*, arXiv:2609.19078: no mention (abstract-level check).
  - Golab MS thesis (May 2024, danaernst.com): predates the paper; treats only lengths 2–3; **no max-monotonicity conjecture and no 1122/1112 pair** — no priority displacement.
- **Open search** (web_search/exa, 3 query angles, 2026-10-31, responseId in provenance): no published or preprint refutation of Conjecture 8.8 found. Golab's thesis and the AJC landing page surfaced; nothing else relevant.
- **Boundaries:** an open-source label and "no hits found" do **not** establish novelty. Bounded gaps, stated explicitly: (i) I did not exhaustively scan the ~50 papers in the source's own bibliography for implicit refutations (the two most-cited word-equivalence antecedents, Jelínek–Mansour [43] and Burstein/Kasraoui, concern *equivalence*, not the max-inequality, and the paper's Section 8 already digests them); (ii) non-indexed or closed-access venues (the AJC PDF itself was checked; no ScienceDirect access attempted, none needed); (iii) preprints posted within days of the review (the Hertzsprung paper is one; checked and disjoint); (iv) MathDB record 364119's own citation graph was not independently re-crawled beyond the frozen sources. The "new-to-literature" label is **not adopted**; the defensible statement is: *no prior refutation found in the retained and lawfully fetched sources as of 2026-10-31, with the published AJC version (2026) leaving the conjecture open.*
- **Chronology:** AJC published version (volume dated 2026, PDF built 2026-02-17) retains the open conjecture; the earliest known statement is the paper itself (arXiv July 2024 / thesis May 2024 has nothing relevant); the refutation record is later than all of these. Chronology favors novelty but is not mathematical evidence, and integrity checks are not priority evidence.

## 4. SUBSTANTIVE

This is a genuine refutation of a published open conjecture with a **complete finite certificate**: the negation of "∀ same-length p,q with max(p)≤max(q), ∀n: |Cay_n(p)| ≥ |Cay_n(q)|" is existential, so (1122, 1112, n=5) plus the two exact integers is a complete witness. Replay cost: enumeration of 541 words (sub-second; my full sweep incl. all controls ran in 2.16 s under the guard). The result is not a routine corollary of anything in the source: the paper's own tooling (species equations for length ≤3) does not reach length-4 patterns, and the paper's authors checked the analogous 8.6 pair to n ≤ 9 without recording an 8.8 counterexample — so this is not merely "their computation redone"; it is a new complete witness. The one soft spot is the usual one for computational counterexamples: correctness rests on the exactness of the enumeration, which is here established by three mutually independent routes (two containment predicates over the explicit universe + the analytical profile certificate + the source's own controls), all agreeing exactly.

## 5. FORMAL-FEASIBILITY (plan only — no builds)

Feasible as a finite certificate with no new axioms (propext, Classical.choice, Quot.sound allowed; none actually needed beyond decidable equality):

- `def CayleyWord := List Nat` with `decidable` packedness (letter set = [1..max]).
- `def Contains (p w : List Nat) : Prop := ∃ idx : Fin (w.length ≥ p.length → …)` — concretely: existence of a strictly increasing index list `idx` of length `p.length` with `p = normalize (idx.map w.get)` where `normalize` is the value-rank map (paper's `std`); provide the `Decidable` instance by bounded enumeration over `Fin (w.length)` combinations.
- `def CayAvoid (n : Nat) (p : List Nat) : Nat := (Finset.univ.filter (fun w : Fin n → Nat => isPacked w ∧ ¬ Contains p (toList w))).card` — or enumerate the 541-element set explicitly; n=5, letters ≤ 5 keeps everything in `Nat`/`Fin 5 → Fin 5` territory; `decide`/`native_decide`-style evaluation closes it.
- Certificate to formalize: `max (1122) = max (1112) = 2`, both length 4, `CayAvoid 5 [1,1,2,2] = 520`, `CayAvoid 5 [1,1,1,2] = 522`, `520 < 522`. Optionally the n=6 persistence pair (4340 < 4394) and the Cor.-6.8 control `CayAvoid n [1,1,2] = (n+1)!/2` for n ≤ 6 as a machinery sanity lemma.
- Estimated effort: small (days); no classical analysis; no infinite objects. The only mild care point is defining `normalize` by value rank (not first appearance — see preserved failure F1).

## 6. Verdicts

| Dimension | Verdict |
|---|---|
| SOURCE | **PASS with corrections** — published definition is strict-index (arXiv v1 `≤` is a typo); citation year 2026 not 2025; conjecture on p. 296 not p. 295; record text "nondecreasing" must be fixed. Counts correspond to the published definition; no credit taken for corrections. |
| MATH | **VALIDATED** — independently recomputed exactly (520 < 522; 4340 < 4394; total 541), with a complete analytical certificate (21 = 6+15 containers of 1122; 19 = 6+13 containers of 1112) and all source-known and adversarial controls passing. |
| SUBSTANTIVE | **SUBSTANTIVE** — complete finite refutation of a published open conjecture; not a routine adaptation of source machinery. |
| NOVELTY | **NO PRIOR REFUTATION FOUND** — r304 + all campaign records clean; both named follow-ups and the thesis checked and disjoint; open search negative. "New-to-literature" **not adopted**; bounded gaps stated in §3. |
| FORMAL-FEASIBILITY | **FEASIBLE** — finite decidable certificate; Lean plan above; no builds performed. |
| DISPOSITION | **INVEST** — route to acceptance pipeline with the §1.3 text corrections applied by root. No acceptance/count changes: **9 additional / 39 total / next 40 unchanged.** |

## 7. Remaining obligations

1. Root applies the three record corrections (definition sentence, year, page) to proposals/dispositions **before** any acceptance; the corrected record should cite the AJC PDF p. 280 definition (strict) and quote the arXiv v1 typo explicitly.
2. Root should not quote the candidate's `decisive-cayley-validation.json` as a passed control (its 112 row is a recorded failure) nor the sweep's 45,324 raw violations (same-length scope not applied); use this review's independent artifacts.
3. Acceptance and any count changes remain with root; this lane made none.
4. 364117 (automaton lead) and 371547 (overlap flag) remain untouched and separate.
5. If accepted, the Lean endpoint (§5) is a separate build task — not started here.
6. Novelty remains bounded by §3's gaps; a cheap closing step at acceptance time is a re-check of the follow-up authors' pages for anything posted after 2026-10-31.

— Review lane pi-cayley-avoidance-preliminary-review-r333, 2026-10-31T01:55Z UTC.
