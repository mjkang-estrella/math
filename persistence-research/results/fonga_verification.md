# Certificate 3 — Fonga's worked example, the {2,6} family, and the level-1 Diophantine test

**Subagent F** · 2026-10-19 · Python 3.14.7, stdlib only (no pip/gmpy2) ·
`src/fonga_verify.py` (28.9 s) + `src/level1_diophantine.py` (0.1 s) · full console log:
`results/fonga_cert_log.txt` · total runtime ≈ 29 s (budget: 15 min).

Sources: Fonga, *arXiv:2608.27802* (v1, 28 Aug 2026) — Lemma 2.1, Corollary 3.2,
Theorem 4.1 and §5 fetched and read in full on 2026-10-19; BCGN *arXiv:2110.04263*
via `notes/literature.md` §3; project context `notes/pure_math.md` §6, Theorems A–E.

Validation gates run before the measurements: `python3 src/test_core.py` → exit 0
(ALL GATES PASSED, 2.6 s); `arrangements()` checked equal to the sorted set of
`itertools.permutations` on four repeat-heavy multisets; the bit-trick `v₂` checked
against the division loop on 2000 random 18-digit inputs.

---

## 0. Claims under test

From Fonga Thm 4.1 (worked example, verbatim intent): for the digit multiset
𝒟 = {4,4,7} with arbitrarily many inserted 1s and no other digits,

> "Thus, the largest value among all terminal choices is 7, attained when L=6. …
> The corresponding integer is x = 1005696/9 = 111744, and indeed
> 111744 = 3²·97·2⁷."

From Corollary 3.2: every member x of the family satisfies
v₂(x) ≤ ⌊ρ·c^q + ((c^q−1)/(c−1))·log₂B⌋ with c = log₂10, q = Σν_d,
B = 1 + 9Σ(d−1)ν_d, ρ = 3 if ν₂>0, 2 if ν₂=0∧ν₆>0, 1 if ν₂=ν₆=0∧ν₄+ν₈>0, else 0.

The task brief adds two claims of its own: (i) the maximum is attained **uniquely**
at 111744 (Fonga does not state uniqueness); (ii) for the {2,6} family the max-v₂
attainers "should be small 7-smooth numbers" — stated as a hypothesis to test.

## 1. Methodology — three independent legs

Let 𝒜(ν) = {numbers whose digits are exactly ν_d copies of each exceptional digit
d ∈ {2,…,9}, any number of 1s, no 0s}. Fonga's Lemma 2.1 parametrizes it:

  x = (10^L − 1)/9 + Σᵢ (dᵢ − 1)·10^{rᵢ},  0 ≤ r₁ < … < r_q < L,

so a member is determined by the positions of its exceptional digits and the
length L (the 1s fill the rest).

- **Leg A (enumeration).** For every j ≤ 40, enumerate *all* distinct arrangements
  of {1^j} ∪ 𝒟 and compute v₂ of each (bit-trick `(n & -n).bit_length() − 1`).
  407,253 numbers for 𝒟 = {4,4,7}; 24,682 for 𝒟 = {2,6}. Empirical leg.
- **Leg B (Fonga's own recursion, verbatim).** Theorem 4.1's 𝔙(ℳ, a, T) =
  max({v_p(T)} ∪ {𝔙(ℳ∖{d}, t, T + (b−1)(d−1)b^t) : d ∈ ℳ, a < t ≤ ⌊v_p(T)/e⌋}),
  terminal case 𝔙(∅, a, T) = max({v_p(T)} ∪ {v_p(T + b^L) : a < L ≤ ⌊v_p(T)/e⌋}),
  maximized over initial states (𝒟∖{d}, 0, T_d), T_d = 9(d−1)−1 for p = 2, b = 10
  (e = v₂(10) = 1). This is an **exact** computation of max v₂ over the *entire
  infinite family* — the pruning (place a digit only where it can still change the
  valuation) is what makes it terminate. Implemented verbatim; validated by
  reproducing the paper's own partial-sum tables digit-for-digit (§2.2).
- **Leg C (complete residue analysis, mod 2⁸).** For L ≤ 8 every arrangement is
  enumerated exactly (x < 10⁸). For L ≥ 9, x mod 2⁸ depends only on the digits in
  positions 0..7 (10^t ≡ 0 mod 256 for t ≥ 8), and every admissible position-tuple
  (counts ≤ ν, rest 1s) is realizable for all large enough L; for a nonzero residue
  r, v₂(x) = v₂(r) exactly. So max v₂ over the whole infinite family and the
  **complete set of attainers** are computable from ≤ 5⁸ tuples. If any tuple had
  residue 0 mod 256, v₂ ≥ 8 would be attainable and the leg reports itself
  inconclusive (this happens for the record family, §4.3 — by design).

Legs A, B, C agree everywhere they are all decisive; leg C is the only one that
proves uniqueness over the whole infinite family.

## 2. Task 1 — 𝒟 = {4,4,7} plus 1s (Fonga's worked example)

### 2.1 Leg A — direct enumeration, j ≤ 40 (407,253 numbers, 0.9 s)

| j | #arr | max v₂ | attainer(s) | | j | #arr | max v₂ | attainer(s) |
|---|---|---|---|---|---|---|---|---|
| 0 | 3 | 3 | 744 | | 21 | 6072 | 6 | 111111111111111111111744 |
| 1 | 12 | 4 | 1744 | | 22 | 6900 | 6 | 1111111111111111111111744 |
| 2 | 30 | 5 | 11744 | | 23 | 7800 | 6 | 11111111111111111111111744 |
| 3 | 60 | 7 | 111744 | | 24 | 8775 | 6 | 111111111111111111111111744 |
| 4 | 105 | 6 | 1111744 | | 25 | 9828 | 6 | 1111111111111111111111111744 |
| 5 | 168 | 6 | 11111744 | | 26 | 10962 | 6 | 11111111111111111111111111744 |
| 6 | 252 | 6 | 111111744 | | 27 | 12180 | 6 | 111111111111111111111111111744 |
| 7 | 360 | 6 | 1111111744 | | 28 | 13485 | 6 | 1111111111111111111111111111744 |
| 8 | 495 | 6 | 11111111744 | | 29 | 14880 | 6 | 11111111111111111111111111111744 |
| 9 | 660 | 6 | 111111111744 | | 30 | 16368 | 6 | 111111111111111111111111111111744 |
| 10 | 858 | 6 | 1111111111744 | | 31 | 17952 | 6 | 1111111111111111111111111111111744 |
| 11 | 1092 | 6 | 11111111111744 | | 32 | 19635 | 6 | 11111111111111111111111111111111744 |
| 12 | 1365 | 6 | 111111111111744 | | 33 | 21420 | 6 | 111111111111111111111111111111111744 |
| 13 | 1680 | 6 | 1111111111111744 | | 34 | 23310 | 6 | 1111111111111111111111111111111111744 |
| 14 | 2040 | 6 | 11111111111111744 | | 35 | 25308 | 6 | 11111111111111111111111111111111111744 |
| 15 | 2448 | 6 | 111111111111111744 | | 36 | 27417 | 6 | 111111111111111111111111111111111111744 |
| 16 | 2907 | 6 | 1111111111111111744 | | 37 | 29640 | 6 | 1111111111111111111111111111111111111744 |
| 17 | 3420 | 6 | 11111111111111111744 | | 38 | 31980 | 6 | 11111111111111111111111111111111111111744 |
| 18 | 3990 | 6 | 111111111111111111744 | | 39 | 34440 | 6 | 111111111111111111111111111111111111111744 |
| 19 | 4620 | 6 | 1111111111111111111744 | | 40 | 37023 | 6 | 1111111111111111111111111111111111111111744 |
| 20 | 5313 | 6 | 11111111111111111111744 | | | | | |

`[PASS]` **global max over j ≤ 40 = 7, attained exactly once, at (j=3, 111744)**;
`[PASS]` uniqueness within j ≤ 40. The per-j max sequence is 3, 4, 5, 7, 6, 6, 6, …
— the peak sits at j = 3 and the level *drops* to 6 for j ≥ 4 (the 1…1744 pattern);
v₂ is **not** monotone in j. Every per-j attainer has the form a(j) = 1…1744
(j ones then 744) and **none is 7-smooth**:
744 = 2³·3·31, 1744 = 2⁴·109, 11744 = 2⁵·367, 111744 = 2⁷·3²·97,
1111744 = 2⁶·29·599, 11111744 = 2⁶·7·17·1459, … (0 of 41 smooth).

### 2.2 Leg B — Fonga's recursion 𝔙, verbatim

`[PASS]` 𝔙 says **max v₂ over the entire family = 7** (1 state, 9 nodes).
`[PASS]` maximizing branch: units 4 at position 0 → 4 at position 1 → 7 at position 2
→ leading 10⁶, i.e. exactly the paper's branch; reconstructed x = 111744, v₂ = 7.
`[PASS]` the paper's worked-example tables reproduce line by line:

| step | value | v₂ | paper |
|---|---|---|---|
| T₄ = 9(4−1)−1 | 26 | 1 | 1 |
| 4 at position 1: 26 + 9·3·10 | 296 | 3 | 3 |
| 7 at position 1: 26 + 9·6·10 | 566 | 1 | 1 |
| 7 at position 2: 296 + 54·10² | 5696 | 6 | 6 |
| 7 at position 3: 296 + 54·10³ | 54296 | 3 | 3 |
| L=3: 5696 + 10³ | 6696 | 3 | 3 |
| L=4: 5696 + 10⁴ | 15696 | 4 | 4 |
| L=5: 5696 + 10⁵ | 105696 | 5 | 5 |
| L=6: 5696 + 10⁶ | 1005696 | **7** | **7** |

`[PASS]` 9·111744 = 1005696 = 10⁶ − 1 + 27 + 270 + 5400 (Lemma 2.1 form).

### 2.3 Leg C — the whole infinite family, and uniqueness

`[PASS]` L ≤ 8 exhaustive (378 arrangements): max v₂ = 7, attainer 111744 (L=6) only.
`[PASS]` L ≥ 9 residue tuples (269 admissible): max v₂ = 6; **no** tuple attains 7;
**no** tuple has residue 0 mod 256, so **v₂ ≥ 8 is unattainable in the entire family**.

**Verdict Task 1:** `[PASS]` max v₂ over the whole family 𝒜({4,4,7}) = 7;
`[PASS]` attained **uniquely** at 111744 (all three legs);
`[PASS]` 111744 = 2⁷·3²·97 (full factorization, Miller–Rabin–verified 97 prime);
`[PASS]` Fonga's Thm 4.1 example confirmed, and the task's uniqueness claim proved
(for all j, not only j ≤ 40).

## 3. Task 2 — 𝒟 = {2,6} plus 1s (even-family small pair, Thm C.2 case a≡2, b≡1)

24,682 numbers enumerated (j ≤ 40). Per-j max v₂ and attainers:

| j | #arr | max v₂ | attainer(s) | factorization(s) |
|---|---|---|---|---|
| 0 | 2 | 1 | 26, 62 | 2*13; 2*31 |
| 1 | 6 | 3 | 216 | 2^3*3^3 |
| 2 | 12 | 6 | 1216 | 2^6*19 |
| 3 | 20 | 4 | 11216, 16112 | 2^4*701; 2^4*19*53 |
| 4 | 30 | 4 | 111216, 116112 | 2^4*3*7*331; 2^4*3*41*59 |
| 5 | 42 | 4 | 1111216, 1116112 | 2^4*199*349; 2^4*79*883 |
| 6 | 56 | 4 | 11111216, 11116112 | 2^4*71*9781; 2^4*7*99251 |
| 7 | 72 | 4 | 111111216, 111116112 | 2^4*3*2314817; 2^4*3*467*4957 |
| 8 | 90 | 4 | 1111111216, 1111116112 | 2^4*181*593*647; 2^4*69444757 |
| … | (j+2)(j+1) | 4 | 1…1216, 1…16112 (patterns) | 2⁴·(odd cofactor) |
| 40 | 1722 | 4 | 111111111111111111111111111111111111111216, 111111111111111111111111111111111111116112 | 2^4*3*7*277*48000327983*202548280423*122790757547267; 2^4*3*23*31*21521*150856586264957735258474814665503 |

**Growth pattern vs j:** max v₂ = 1 → 3 → **6 (peak, j = 2)** → 4 → 4 → 4 → … —
non-monotone, rising to a peak at j = 2 and **constant at 4 for every j ≥ 3**
(verified j = 3..40; explained structurally: for L ≥ 10 = q+8 every position-tuple
is realizable, so the achievable residues mod 256 — hence the max — are
j-independent; the L ≤ 8 exact sweep and the L ≥ 9 residue analysis confirm the
value 4). **v₂ does not grow unboundedly** — exactly Fonga's Corollary 3.2
phenomenon: the whole-family sup is finite and small.

Family-wide optimum, three ways:
- Leg A: max over j ≤ 40 = **6**.
- Leg B (𝔙): **6** — units-6 branch (T₆ = 44 → 2@2 → T = 944, v₂ 4 → L=4: 10944, v₂ 6)
  beats the units-2 branch (5, at 6112 = 2⁵·191). `[AGREE]`
- Leg C (complete): max = **6**, attained **uniquely** at 1216 (j = 2) over the
  entire infinite family; no residue-0 tuples, so v₂ ≥ 7 impossible. `[AGREE]`

**The attainers are *not* generally 7-smooth.** The task's expectation holds only
once: 216 = 2³·3³ (j = 1). 26 = 2·13, 62 = 2·31, and the family-max attainer
1216 = 2⁶·19 all carry primes > 7; across j ≤ 40 exactly one per-j attainer is
7-smooth (216). What *is* true: the attainers are **small** (≤ 42 digits) and have
the shape 2^k × (odd cofactor) — their smoothness is incidental, not structural.

Corollary 3.2 explicit bound for ν = (ν₂, ν₆) = (1,1): q = 2, B = 55, ρ = 3 →
**v₂ ≤ 58** — valid but 10× loose against the optimal 6. (For 𝒟 = {4,4,7}:
q = 3, B = 109, ρ = 1 → v₂ ≤ 140 vs optimal 7.)

**Verdict Task 2:** `[PASS]` per-j table + growth pattern (peak 6 at j=2, plateau 4
from j=3, sup over the infinite family = 6, all legs agree); `[PASS]` attainers and
factorizations reported; `[FAIL→corrected]` "attainers should be 7-smooth" — false
in general (only 216 is); reported as measured.

## 4. Task 3 — the level-1 exponential-Diophantine equation and the record case

### 4.1 The equation, concretely

Fix m₀ = 2^a·3^b·7^d (Theorem A forces a·c = 0, so no factor 5) and let the preimage
n have the rigid digit multiset {7^d} ∪ F(a,b) ∪ {1^j}, where F(a,b) is the
min-lex minimal factorization of 2^a·3^b (Theorem C.2). By Lemma 2.1 every such n is

  n = (10^L − 1)/9 + Σᵢ (dᵢ − 1)·10^{rᵢ},  L = len23(a,b) + d + j,

with the k = len23(a,b) + d exceptional digits dᵢ at pairwise distinct positions
0 ≤ rᵢ < L (the *decimal-expansion polynomial*; the 1s are the baseline
(10^L−1)/9). Π(n) = m₀ automatically, so P(n) = 1 + P(m₀) for **every** member.
The **level-1 chain condition** — n is itself 7-smooth, so P(n) = 11 when
P(m₀) = 10 and the min-lex factorization of n is a persistence-12 number whose
chain passes through m₀ = Π(record holder) — is exactly the exponential-Diophantine
equation in the insertion positions

  **(10^L − 1)/9 + Σᵢ (dᵢ − 1)·10^{rᵢ} = 2^A·3^B·7^D**,

equivalently Fonga's eq.-19 shape (multiply by 9, absorb 9 = 3² into the target):

  **10^L − 1 + Σᵢ 9(dᵢ − 1)·10^{rᵢ} = 2^A·3^{B+2}·7^D**.

For the record case (a,b,d) = (19,4,6): F(19,4) = {2, 8⁶, 9²} (checked:
product 2¹⁹·3⁴ ✓, |F| = len23(19,4) = 9 via the read-only DP ✓), so the exceptional
digits are {2, 7⁶, 8⁶, 9²} (k = 15) and the equation reads

  10^L − 1 + 9·10^r + 54·Σ_{i=1..6} 10^{rᵢ} + 63·Σ_{i=1..6} 10^{sᵢ} + 72·Σ_{i=1..2} 10^{tᵢ}
    = 2^A·3^{B+2}·7^D,  distinct positions in [0, L), L = 15 + j.

### 4.2 The bounded generator and the record case j = 0..6

`src/level1_diophantine.py` takes (a,b,d,j), enumerates the **first 2000
arrangements in sorted (ascending) order** (lex order on the sorted digit string =
ascending numeric order), asserts Π(n) = m₀ for every one, factors each by trial
division with the primes 2,3,5,…,97, and flags any 7-smooth member (support ⊆
{2,3,5,7} and cofactor 1). Results:

| j | L | total arrangements | sampled | 7-smooth | max v₂ (sample) | max v₃ (sample) | min cofactor |
|---|---|---|---|---|---|---|---|
| 0 | 15 | 1,261,260 | 2000 | **0** | 14 | 0 | 3,073,781 |
| 1 | 16 | 20,180,160 | 2000 | **0** | 14 | 1 | 21,762,271 |
| 2 | 17 | 171,531,360 | 2000 | **0** | 14 | 0 | 9,146,789 |
| 3 | 18 | 1,029,188,160 | 2000 | **0** | 14 | 0 | 4,540,833,481 |
| 4 | 19 | 4,888,643,760 | 2000 | **0** | 14 | 1 | 511,585,211 |
| 5 | 20 | 19,554,575,040 | 2000 | **0** | 14 | 0 | 702,667,641,139 |
| 6 | 21 | 68,441,012,640 | 2000 | **0** | 14 | 0 | 225,113,254,673 |

**0 of 14,000 sampled arrangements are 7-smooth — indeed none is even 97-smooth**
(every sampled member has a prime factor > 97; the smallest cofactor seen is
3,073,781). Two consistency marks: the lex-smallest j = 0 arrangement is the record
holder 277777788888899 itself (asserted in the run; it is not 7-smooth —
277777788888899 = 13·59·1699·213161503 — as expected, since level-0 numbers need
not be smooth), and the max v₂ = 14 inside the samples sits well below the exact
family values found next.

### 4.3 Record-family probes: how large can A = v₂(n) be?

For ν = (ν₂, ν₇, ν₈, ν₉) = (1, 6, 6, 2) (q = 15, B = 856, ρ = 3):

- **Corollary 3.2 explicit bound:** v₂ ≤ **476,331,879** (60-digit Decimal
  arithmetic, floor of ρ·c¹⁵ + ((c¹⁵−1)/(c−1))·log₂856). Valid, astronomically loose.
- **Leg C (mod 2⁸):** 143,235 admissible position-tuples; **312 have residue 0 mod
  256** ⟹ v₂ ≥ 8 is attainable ⟹ the mod-256 analysis correctly declares itself
  inconclusive here (it is decisive only when the true max < 8, as in §2.3/§3).
- **Exact sweep, all arrangements with L ≤ 16** (21.4 M numbers, 19 s):
  max v₂ = **22** at 787897879887872 (j = 0, all 1,261,260 arrangements) and
  **23** at 8718788987977728, 9277887781797888 (j = 1, all 20,180,160).
- **𝔙 (Thm 4.1), budgeted run: TERMINATED.** 1,973,621 nodes, 4.6 s —
  **max v₂ over the entire infinite family = 64**, attained (branch verified by
  direct recomputation) at
  x = 17119111811171111818111818111711111117111119117811712
  (L = 53, j = 38 inserted 1s; digit multiset machine-checked; v₂(x) = 64 ✓).

**Consequence for the level-1 equation:** A = v₂(n) ≤ **64** for every member of
the rigid record family (any j), against the explicit bound 476,331,879. The
Diophantine equation of §4.1 is therefore finite in A ∈ [0, 64] — and in B, D
through size — which is precisely the finiteness Fonga's machinery contributes.

### 4.4 Cross-check against subagent C

Subagent C's attack 2 (`results/redteam_results.md` §2) exhausted all 7-smooth
m′ = 2^a·3^b·5^c·7^d with len23(a,b)+c+d ≤ 30 (246,016 tuples) and found **none**
whose digit product lands in the P ≥ 10 frontier — in particular no 7-smooth
preimage of m₀ = 2¹⁹·3⁴·7⁶ with len ≤ 30. Our arrangement-level check is the same
question sliced by digit arrangements: a hit at j ≤ 5 (dc ≤ 20) would contradict C
outright, since the bridge lemma gives len(n) ≤ 1.4307·dc + 2 ≤ 30; a j = 6 hit
(dc = 21, len ≤ 32) could only escape C's slice through len ∈ {31, 32} — for any
hit we would compute len(n) = len23(A,B) + D exactly (the (240,160) DP table is
built for this). **0 hits on either side: consistent**, from two independent
parametrizations.

## 5. What Fonga's machinery would require for a full proof

Fonga proves BCGN's Conjecture 2 (uniform v₂ over each 1-insertion family) and
reduces each nonzero even terminal digit δ ∈ {2,4,6,8} to a finite computation
(*"Although carrying out the full computation lies beyond the scope of this paper,
the formulation developed here is intended to make that next step accessible."*).
The computation, per terminal digit δ:

1. **The candidate graph.** BCGN's finite backward graph B_δ = (U_δ, F_δ)
   (|U_δ| = 33, 9, 84, 51 for δ = 2, 4, 6, 8; their Appendix C). Completeness to
   prove: (17) ∀s ∈ U_δ: S²(x) = s ⟹ S(x) ∈ U_δ.
2. **Per vertex s ∈ U_δ: enumerate ℱ(s)** — all digit factorizations
   s = Π d^{n_d} (the "equation families": 1117 / 1062 / 6377 / 4774 for
   δ = 2 / 4 / 6 / 8; largest number of terms 30 / 32 / 37 / 45 — counted *before*
   the finite range of t is applied, so the true count is larger but finite).
3. **Per multiset ν (one per 𝐧 ∈ ℱ(s)): compute t_max(𝒟) by 𝔙** — finite and
   terminating (Thm 4.1). Our runs show this step is *cheap*: {4,4,7} → 7,
   {2,6} → 6, the record family {2,7⁶,8⁶,9²} → 64, each in seconds. Every
   solution of the family's equation then has t = v₂(y) ∈ [0, t_max(𝒟)].
4. **Per (𝐧, t): solve the exponential-Diophantine equation** — Fonga eq. (19),
   10^{a₀} − 1 + Σᵢ 9(dᵢ−1)·10^{aᵢ} = 2^t·3^{u+2}·7^w with distinct positions
   0 ≤ aᵢ < a₀ — by BCGN's modular-lifting algorithm (residues mod
   m₁₂ = (10¹²−1)/(3³·7), lifted to m₂₄, m₄₈).
5. **Discard** solutions violating the positional conditions (18); each survivor
   is a candidate predecessor y with S(y) = s; **verify y ∈ U_δ**.
6. If no survivor falls outside U_δ for every s ∈ U_δ, then B_δ = A_δ and the
   persistence bound for terminal δ follows (BCGN's method).

**Which infinite-family decisions remain** (the precise residue of the proof):

- **Per target digit δ ∈ {2,4,6,8}:** the 𝔙 half (step 3) is finite per family and,
  per our measurements, seconds — the modular-lifting half (step 4) is the heavy
  one: ~10³–10⁴ equation families per δ, times the t-range per family, times the
  lifting ladder; BCGN themselves flag 12³⁰ ≈ 2¹⁰⁷ position tuples "in the most
  favorable case" (δ = 2, 30 terms) as "totally out of reach to exhaust" *without*
  the t-bounds; Fonga's bounds shrink the t-range but not the position
  combinatorics. Nobody — including Fonga — has run steps 2–5 for any δ.
- **Per multiset ν:** the decision "does 𝒜(ν) contain a solution of (19) for some
  t ≤ t_max(𝒟)?" is exactly the completeness of our §4.1 equation at level 1 —
  for the record family it is now a finite question in A ∈ [0, 64] (plus bounded
  B, D), but still with unboundedly many position variables as j grows; that
  infinitude is what the modular-lifting step (not enumeration) must decide.
- **Terminal digit 0 is not covered at all.** BCGN (footnote): "The particular case
  d=0 can not be treated by our method." A chain ending at 0 must produce a
  zero-containing value m first, and bounding *when* that happens is the zero-digit
  statement (de Faria–Tresser Conjecture 1). Senge–Straus/Stewart control the
  opposite direction (unboundedly many *nonzero* digits); no tool gives the needed
  upper bound. Note the record chain itself ends at 0
  (277777788888899 → … → 0), so the headline conjecture P ≤ 11 is **not** closed
  by completing even-δ graphs alone — the zero-digit half is exactly our
  Theorem 5′ frontier (zero-free 7-smooth numbers).
- **The graphs B_δ are themselves conjectural.** Step 6 is a decision procedure
  for completeness: a single survivor y ∉ U_δ forces extending the graph (and the
  persistence bound) rather than proving it.

## 6. Verdict

```
CERTIFICATE 3 (pure_math.md §6) — subagent F — 2026-10-19
  gates: src/test_core.py exit 0; generator == itertools (4 multisets);
         v2 bit-trick == loop (2000 random 18-digit inputs)   [PASS]

TASK 1  Fonga Thm 4.1, D = {4,4,7} + 1s
  leg A  407,253 arrangements, j <= 40: per-j max = 3,4,5,7,6,6,...;
         global max 7 at (j=3, 111744) only; unique in j<=40     [PASS]
  leg B  V (verbatim) max over ENTIRE family = 7; branch 4@0,4@1,7@2,L=6
         -> x = 111744; paper's partial-sum tables 9/9 reproduced [PASS]
  leg C  complete residue analysis: family max 7; UNIQUE attainer
         111744 over the whole infinite family; v2>=8 impossible  [PASS]
  factorization 111744 = 2^7 * 3^2 * 97                            [PASS]

TASK 2  D = {2,6} + 1s, j <= 40 (24,682 numbers)
  per-j max: 1, 3, 6, 4, 4, 4, ... (peak 6 at j=2; plateau 4, j>=3)
  family sup = 6 (legs A=B=C agree); unique attainer 1216 = 2^6*19
  attainers 7-smooth? only 216 = 2^3*3^3 (j=1); 26, 62, 1216 not
  Cor-3.2 explicit bound 58 (optimal 6)                            [PASS, expectation corrected]

TASK 3  level-1 Diophantine test, m0 = 2^19*3^4*7^6 (record product)
  equation written out (9n = 10^L - 1 + 9*10^r + 54*... + 72*... = 2^A 3^{B+2} 7^D)
  generator: j = 0..6, first 2000 arrangements each (14,000 total):
  7-smooth hits = 0 (none even 97-smooth; min cofactor 3,073,781)
  cross-check vs subagent C (246,016 tuples, len<=30, 0 hits): consistent
  record-family sup v2 = 64 (V, exact, 1.97M nodes; attainer verified)
  vs explicit Cor-3.2 bound 476,331,879                            [PASS]

OVERALL: Fonga's Thm 4.1 worked example CONFIRMED (max v2 = 7 at 111744,
uniquely, over the entire infinite family); its recursion V reproduced and
applied to two new families; the level-1 exponential-Diophantine equation for
the record product has no solution in the tested range and its exponent A is
now finitely bounded (A <= 64). The conjecture remains open: what Fonga's
machinery still requires is the per-delta equation-completeness computation
(none carried out, by anyone) plus a zero-digit bound for terminal 0.
```

*Artifacts: `src/fonga_verify.py`, `src/level1_diophantine.py`,
`results/fonga_cert_log.txt` (full console output). Shared library
`src/persistence.py` used read-only (`len23_table`); no bugs found in it.*
