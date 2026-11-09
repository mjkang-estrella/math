# Certificates E — τₖ thresholds, min-lex factorizations, level feasibility

**Verifier:** subagent E (test). **Date:** 2026-10-19. **Machine:** mj-framework,
Python 3.14.7, stdlib only. **Total compute:** ≈ 14 s wall (A: 0.04 s, B: 13.4 s,
C: 0.3 s + spot checks) — far inside the 15-minute budget; no parallelism needed.

**Artifacts:** `src/certA_thresholds.py`, `src/certB_minlex.py`, `src/certC_levels.py`
(the scripts; all re-runnable) and the machine-readable outputs
`results/threshold_certificates.json`, `results/minlex_certificates.json`,
`results/level_feasibility.json`.

**Library used (read-only):** `src/persistence.py` — `persistence`,
`persistence_naive`, `is_7smooth`, `digit_product`, `len23_table`, `len_of_smooth`.

---

## Certificate A — thresholds τₖ = min{7-smooth m : P(m) ≥ k}, k = 1..10

### Result

| k | τₖ | factorization (a,b,c,d) | P(τₖ) | \|{7-smooth m < τₖ}\| | max P on that domain | attaining witness |
|---|-----------------|-------------------------|-------|----------|----------|------------|
| 1 | 10 | (1,0,1,0) = 2·5 | 1 | 9 | 0 | 9 |
| 2 | 25 | (0,0,2,0) = 5² | 2 | 18 | 1 | 24 |
| 3 | 49 | (0,0,0,2) = 7² | 3 | 29 | 2 | 48 |
| 4 | 378 | (1,3,0,1) = 2·3³·7 | 4 | 90 | 3 | 375 |
| 5 | 2 688 | (7,1,0,1) = 2⁷·3·7 | 5 | 210 | 4 | 2 646 |
| 6 | 27 648 | (10,3,0,0) = 2¹⁰·3³ | 6 | 471 | 5 | 27 440 |
| 7 | 338 688 | (8,3,0,2) = 2⁸·3³·7² | 7 | 968 | 6 | 337 500 |
| 8 | 4 478 976 | (11,7,0,0) = 2¹¹·3⁷ | 8 | 1 805 | 7 | 4 465 125 |
| 9 | **438 939 648** | (12,7,0,2) = 2¹²·3⁷·7² | 9 | 4 499 | 8 | 437 582 250 |
| 10 | **4 996 238 671 872** | (19,4,0,6) = 2¹⁹·3⁴·7⁶ | 10 | 18 050 | 9 | 4 994 157 772 800 |

* **τ₉ = 438 939 648** and **τ₁₀ = 4 996 238 671 872** — **CONFIRMED** (both were
  the stated expectations).
* **Monotonicity τ₁ < τ₂ < … < τ₁₀: VERIFIED** (strictly increasing; see below it
  is also forced a priori).
* Chain consistency: Π(τ₁₀) = 438 939 648 = τ₉ exactly — the top of the cascade
  steps down onto the next threshold.
* The sweep domain {7-smooth m < τ₁₀} contains **18 050** lattice points (the
  task's "~13k" estimate; exact count 18 050, cf. asymptotic
  (ln x)⁴/57.24 ≈ 12.8k which omits lower-order terms).
* P-histogram of the domain: P=0: 9, P=1: 15 967, P=2: 1 633, P=3: 267, P=4: 113,
  P=5: 37, P=6: 11, P=7: 6, P=8: 5, P=9: 2.
* Link to OEIS A003001: τ₁ = 10 = a(1), τ₂ = 25 = a(2), and for k ≥ 3
  **τₖ = Π(a(k+1))** — the digit product of the next record setter
  (49 = Π(77), 378 = Π(679), 2 688 = Π(6 788), 27 648 = Π(68 889),
  338 688 = Π(2 677 889), 4 478 976 = Π(26 888 999), 438 939 648 = Π(3 778 888 999),
  4 996 238 671 872 = Π(277 777 788 888 899)). This is forced in one direction
  (Π of anything is 7-smooth and drops P by one) and the sweep proves the minimality
  direction for k = 3..10.

### Method and coverage argument

1. **Candidate.** τ₁₀-candidate = 2¹⁹·3⁴·7⁶ = 4 996 238 671 872; verified 7-smooth
   (`is_7smooth`) with **P = 10 exactly**, agreed by `persistence()` and
   `persistence_naive()` (the zero-digit shortcut path and the naive path).
2. **Exhaustive domain.** We enumerate every (a,b,c,d) with
   2^a·3^b·5^c·7^d **<** τ₁₀. Float logs a·ln2+b·ln3+c·ln5+d·ln7 < ln τ₁₀ are used
   *only* to bound loop ranges (each single-prime maximum taken with +2 slack, and
   asserted 2^amax, 3^bmax, 5^cmax, 7^dmax > τ₁₀); **every boundary decision is an
   exact integer comparison** (inner loops break on `product ≥ τ₁₀` exactly), so
   float error cannot include or exclude a single point. Since factorization into
   primes is unique, (a,b,c,d) ↔ m is a bijection: no duplicates, no gaps; (0,0,0,0)
   ↦ m = 1 is included.
3. **Exact P everywhere.** `persistence()` evaluated on all 18 050 points and
   cross-checked against `persistence_naive()` on **100 %** of them (identical).
4. **Reading off τₖ.** Points sorted by exact integer value; τₖ = first m with
   P ≥ k (τ₁₀ = the candidate itself). For each k the prefix {m < τₖ} must have
   **max P = k−1 exactly** — this simultaneously proves (a) no 7-smooth m < τₖ has
   P ≥ k (minimality of τₖ) and (b) some m < τₖ attains P = k−1, i.e. τₖ₋₁ < τₖ
   (strict monotonicity). All ten checks passed with the table above.
5. **Independent completeness check.** A Hamming-heap enumeration (multiplying
   popped values by 2,3,5,7 — a completely different algorithm from the lattice
   loops) produced exactly the same **set** of 18 050 7-smooth values < τ₁₀.
6. **Robustness.** Had the sweep found max P ≥ 10 below the candidate, the
   candidate would have been corrected and the sweep repeated (not triggered).

A priori monotonicity (why strict increase *must* hold, cross-checking the data):
for k ≥ 2, Π(τₖ) < τₖ (theory.md Lemma 0) and P(Π(τₖ)) = P(τₖ) − 1 ≥ k−1, so
τₖ₋₁ ≤ Π(τₖ) < τₖ. Consistently, P(τₖ) = k exactly for every k (if P(τₖ) ≥ k+1
then τₖ₊₁ ≤ τₖ < τₖ₊₁, absurd).

---

## Certificate B — min-lex minimal factorizations F(a,b), Theorem C.2

### Claim verified

For **all 241 × 161 = 38 801 pairs** (a,b) with 0 ≤ a ≤ 240, 0 ≤ b ≤ 160, the
closed form of Theorem C.2,

| a mod 3 | b mod 2 | F(a,b) (sorted digit multiset) |
|---|---|---|
| 0 | 0 | {8^(a/3), 9^(b/2)} |
| 1 | 0 | {2, 8^((a−1)/3), 9^(b/2)} |
| 2 | 0 | {4, 8^((a−2)/3), 9^(b/2)} |
| 0 | 1 | {3, 8^(a/3), 9^((b−1)/2)} |
| 1 | 1 | {6, 8^((a−1)/3), 9^((b−1)/2)} |
| 2 | 1 | {2, 6, 8^((a−2)/3), 9^((b−1)/2)} |

satisfies (i)–(iii) below. **Zero counterexamples.**

* Worked examples (from the run): F(3,0)={8}, F(4,0)={2,8}, F(5,0)={4,8},
  F(0,1)={3}, F(4,1)={6,8}, F(5,1)={2,6,8}, F(19,4)={2,8⁶,9²},
  F(240,160)={8⁸⁰,9⁸⁰}, F(239,159)={2,6,8⁷⁹,9⁷⁹}.
* **Record-holder consistency:** F(19,4) ∪ {7⁶} = {2, 7⁶, 8⁶, 9²} — exactly the
  digits of 277777788888899 = Π⁻¹(2¹⁹·3⁴·7⁶). ✓

### The three checks

**(i) length(F) = len23(a,b).** `len23_table(240,160)` from `src/persistence.py`,
cross-checked through `len_of_smooth(a,b,0,0,·)`. 0 failures.

**(ii) ∏ digits(F) = 2^a·3^b.** Exact exponent bookkeeping (Σ 2-exp and Σ 3-exp of
the digits) on all 38 801 pairs, plus 201 full big-integer product checks
(including (19,4) and 200 seeded-random pairs). 0 failures.

**(iii) F is lex-minimal among ALL minimal-length factorizations.** Three layers:

* **(iii-a) Prescribed local search.** For r ∈ {2,3}, every sub-multiset
  R ⊆ F with |R| = r (deduplicated), and every digit multiset S over {2,3,4,6,8,9}
  with ∏S = ∏R and |S| = s ≤ r (s = 1..r, all exhaustively enumerated — the
  exponent system is a tiny bounded composition): the replacement F − R + S is
  examined. If s < r the factorization could be *shortened* — impossible because
  len(F) = len23(a,b) is minimal (**0 such replacements found**, as required);
  if s = r the sorted string must be ≥ sorted(F) (**0 lex-smaller replacements
  found**). The search is iterated to a fixpoint; the fixpoint equals F for all
  38 801 pairs. (Digits 1 are impossible in a minimal-length factorization — a 1
  could be deleted — and 5,7 cannot divide 2^a·3^b; the s < r cases subsume every
  1-padded variant.)
* **(iii-b) Independent global check.** Exact greedy lex-min construction:
  among length-L factorizations of 2^a·3^b, more 2s ⟹ lex-smaller sorted string
  (first difference falls at a 2 vs ≥3), hence lex-min = maximize #2s, then #3s,
  then #4s, then #6s, then #8s. Implemented over the exact solution parametrization
  (each candidate re-verified against all three defining equations: length,
  2-exponent, 3-exponent). **F equals the global lex-minimum on all 38 801 pairs.**
* **(iii-c) Ground truth.** Full pruned-DFS enumeration of *all* minimal-length
  factorizations for a ≤ 36, b ≤ 24 (925 pairs): min-lex = F everywhere; plus 40
  seeded-random pairs over the whole range via a second, independent complete
  enumeration: min-lex = F everywhere.

**Validation of the len23 DP itself** (it is load-bearing for (i)): on all 38 801
pairs the bracket max(⌈a/3⌉, ⌈b/2⌉) ≤ len23(a,b) ≤ ⌈a/3⌉ + ⌈b/2⌉ holds (0
violations); on a ≤ 36, b ≤ 24 the DP value equals the exact DFS minimum (0
mismatches). Together with test_core.py's independent branch-and-bound gate, the
DP is confirmed on the whole working range.

### Coverage argument

Every minimal-length factorization of 2^a·3^b uses only digits {2,3,4,6,8,9}
(1 deletable; 5,7 ∤ 2^a·3^b). The local search enumerates *all* sub-multisets of
F of size 2 and 3 and *all* equal-product replacements of size ≤ 3 — this covers
every single replacement that could produce a same-length lex-smaller multiset or
a shorter factorization. Because the closed form is a *count vector* (at most 3
distinct digit values), local optimality here is verified against the complete
replacement set, not a heuristic sample; and the global greedy (proved exact by
the exchange argument above) plus the exhaustive enumerations in (iii-c) remove
any reliance on local-optimality ⟹ global-optimality in the first place: **F is
certified to be the lex-minimal minimal-length factorization itself.**

---

## Certificate C — level-feasibility snapshot for Theorem D (D = 13..26)

### Result

maxs(D) = max digit sum over all 7-smooth m with exactly D decimal digits;
n(D) = how many such m exist. R(D) = D·τ₁₀^{1/D} (τ₁₀ = 4 996 238 671 872),
R₂(D) = D·τ₉^{1/D} (τ₉ = 438 939 648). "maxs < R" is decided by **exact integer
arithmetic** (maxs^D vs D^D·τ) and only displayed in float for readability.

| D | n(D) | maxs(D) | 9D | argmax m | R(D) | level (τ₁₀ req.) | R₂(D) | level (τ₉ req.) |
|----|--------|-----|-----|-----------------------------------------|--------|------------|--------|------------|
| 13 | 5 002 | 90 | 117 | 5787889918776 = 2³·3¹⁶·7⁵ | 123.243 | **INFEASIBLE** | 60.08 | feasible |
| 14 | 6 187 | 90 | 126 | 98872937296875 = 3¹⁷·5⁶·7² | 113.025 | **INFEASIBLE** | 58.00 | feasible |
| 15 | 7 545 | 108 | 135 | 948899895648768 = 2⁹·3⁸·7¹⁰ | 105.358 | feasible (margin 2.64) | 56.53 | feasible |
| 16 | 9 081 | 108 | 144 | 9495756897991875 | 99.491 | feasible | 55.50 | feasible |
| 17 | 10 815 | 108 | 153 | 96939788818359375 | 94.935 | feasible | 54.81 | feasible |
| 18 | 12 759 | 117 | 162 | 878834858949781776 | 91.359 | feasible | 54.38 | feasible |
| 19 | 14 927 | 126 | 171 | 9827753886889279488 | 88.533 | feasible | 54.15 | feasible |
| 20 | 17 323 | 127 | 180 | 79650864925599858688 = 2²⁴·7¹⁵ | 86.290 | feasible | 54.09 | feasible |
| 21 | 19 960 | 135 | 189 | 569484988599458590848 | 84.512 | feasible | 54.17 | feasible |
| 22 | 22 853 | 135 | 198 | 8279979228973388671875 | 83.106 | feasible | 54.36 | feasible |
| 23 | 26 015 | 144 | 207 | 90856588969598508984375 | 82.006 | feasible | 54.64 | feasible |
| 24 | 29 458 | 153 | 216 | 963986997844765170597888 | 81.156 | feasible | 54.99 | feasible |
| 25 | 33 188 | 158 | 225 | 1947987996273487986556928 | 80.517 | feasible | 55.42 | feasible |
| 26 | 37 222 | 162 | 234 | 86206858286699959716796875 = 3³⁰·5¹³·7³ | 80.054 | feasible | 55.90 | feasible |

**Statements.**

* With the **τ₁₀ requirement** R(D) = D·τ₁₀^{1/D} (any 7-smooth D-digit number
  whose digit product must reach τ₁₀ — in the cascade of Theorem B this is the
  persistence-11 element m₀, since Π(m₀) ≥ τ₁₀ forces s(m₀) ≥ D·τ₁₀^{1/D}):
  **violated by ALL 7-smooth numbers with D = 13 and D = 14 digits.** D = 13 is
  trivially impossible (even the absolute maximum 9D = 117 < 123.24); **D = 14 is
  the substantive case**: 9·14 = 126 > 113.02, yet the best any of the 6 187
  14-digit 7-smooth numbers achieves is s = 90 — a deficit of at least 23 below
  the requirement. Hence a persistence-11 smooth number m₀ (if one exists) has
  **dc(m₀) ∉ {13, 14}**, sharpening the digit-count bound dc(m₀) ≥ 13 to
  **dc(m₀) ≥ 15**.
* D = 15 is **feasible only by a margin of 2.64** (108 vs 105.358) — the AM–GM
  constraint is tightest immediately after the infeasible window; from D = 16 on
  the margin grows quickly (8.5, 13.1, 25.6, …).
* With the **τ₉ requirement** R₂(D) = D·τ₉^{1/D} (level-1 elements m₁ with
  P(m₁) ≥ 10): **no D in 13..26 is infeasible** — digit sums alone do not exclude
  any length at this level (tightest at D = 13: maxs 90 vs 60.08).
* Striking empirical fact useful for the digit-statistics discussion: maxs(13) =
  maxs(14) = 90, i.e. every 14-digit 7-smooth number has digit-sum deficit ≥ 36
  (≥ 2.57 per digit) — smooth numbers keep digit sums *low*, exactly the
  obstruction direction discussed in §Theorem E of pure_math.md.

### Method and coverage argument

**Sweep domain.** For m = 2^a·3^b·5^c·7^d with dc(m) = D:

  len(m) = len23(a,b) + c + d ≤ ⌈a/3⌉ + ⌈b/2⌉ + c + d ≤ a/3 + b/2 + c + d + 7/6
  ≤ (a·ln2 + b·ln3 + c·ln5 + d·ln7)/ln5 + 7/6 = ln m / ln 5 + 7/6 < D·ln10/ln5 + 7/6,

using 1/3 ≤ ln2/ln5, 1/2 ≤ ln3/ln5, 1 ≤ ln5/ln5, 1 ≤ ln7/ln5 (so each prime's
len-cost per unit of log-weight is at most the digit-5 ratio 1/ln5 = 1.43068) and
m < 10^D. Hence **len(m) ≤ B(D) = ⌈1.4306766·D + 7/6⌉ − 1**, with
B(13) = 19, B(14) = 21, …, **B(26) = 38** (matching the task's "len ≤ 38,
~10⁶ points" for D = 26). B is increasing, so one sweep of all lattice points with
len23(a,b) + c + d ≤ 38 covers **every** 7-smooth m with dc(m) ∈ [13, 26]; each
point's exact product is bucketed by its exact digit count (bisect on exact powers
of 10) and, in range, its exact digit sum recorded. **608 400 lattice points** were
enumerated (a ≤ 114, b ≤ 76 bounds are complete since len23 ≥ ⌈a/3⌉, ⌈b/2⌉).

**Empirical completeness check.** A second, completely independent enumeration
with **no len bound at all** — all (a,b,c,d) with m < 10²⁶ (exact integer
boundaries, ~225k points) — produced per-D counts **identical** to the len-38
sweep for every D ∈ [13, 26] (0 mismatches). So the coverage bound is not only
proved, it is confirmed by direct exhaustification.

**Argmax audit.** Each reported argmax was re-verified: 7-smooth by trial
factoring, correct digit count, correct digit sum; and the D = 14 cell was
re-derived by a from-scratch shell-only resweep (n = 6 187, maxs = 90 at
98872937296875 = 3¹⁷·5⁶·7²). ✓

---

## Library audit — `src/persistence.py`

**No bugs found.** What was exercised and how:

* `persistence` vs `persistence_naive`: **identical on 100 % of the 18 050 sweep
  points** (values up to 5.0 × 10¹², chain depths up to 10, exercising both the
  zero-digit shortcut path and the plain path) plus the τ₁₀ candidate.
* `is_7smooth`: agreed with trial division by 2,3,5,7 on every τₖ and every
  Certificate-C argmax.
* `len23_table` / `len_of_smooth`: bracketing on all 38 801 pairs; exact equality
  with DFS ground truth on a ≤ 36, b ≤ 24; consistent with the global lex-min
  construction everywhere (a wrong DP length would have made the greedy fail to
  find any length-L solution — it never did).
* `digit_product`: used for the Π(τ₁₀) = τ₉ chain check.

Two implementation notes (not bugs): `len23_table(max_a, max_b)` must be called
with the *inclusive* upper exponents needed (indices are inclusive — fine here);
and in my own first draft of the greedy I derived the solution parametrization with
a sign error — caught immediately because every candidate is re-verified against
the three defining equations; the shipped verifier derives each coordinate by a
single equation rearrangement and re-checks all of them.

---

## Verdict

**CERTIFIED**

1. **(A)** τ₁..τ₁₀ = 10, 25, 49, 378, 2 688, 27 648, 338 688, 4 478 976,
   **438 939 648**, **4 996 238 671 872**; each proven minimal by an exhaustive
   exact-boundary lattice sweep with per-k prefix max P = k−1; strict monotonicity
   verified; τ₉ and τ₁₀ match the stated expectations; domain sizes
   9, 18, 29, 90, 210, 471, 968, 1 805, 4 499, 18 050; enumeration cross-validated
   by an independent Hamming-heap enumeration (identical 18 050-value set).
2. **(B)** Theorem C.2's closed form F(a,b) is the length-minimal
   (== len23 from `persistence.py`), product-correct (== 2^a·3^b), and
   **lex-minimal minimal-length factorization of 2^a·3^b for all 38 801 pairs with
   0 ≤ a ≤ 240, 0 ≤ b ≤ 160** — by the prescribed local search (0 length-reducing,
   0 lex-improving replacements), an independent exact global lex-min construction
   (38 801/38 801 agree), and full ground-truth enumerations on a ≤ 36, b ≤ 24 and
   40 random pairs. **No counterexample exists.**
3. **(C)** maxs(D) computed exactly for D = 13..26 over a provably-covering
   len ≤ 38 domain (608 400 points), confirmed against a len-free enumeration.
   The τ₁₀-requirement is violated by **all** 7-smooth numbers with 13 and with 14
   digits (maxs(13) = 90 < 123.24; maxs(14) = 90 < 113.03), so level-0 of the
   cascade is infeasible there and any persistence-11 smooth m₀ must have
   dc(m₀) ≥ 15; D = 15 survives with margin only 2.64; the τ₉-requirement excludes
   no D in 13..26.

**FAILED:** nothing.

**Bugs found in `src/persistence.py`:** none.
