# Round 4 (GLM sub-agent): the ODD members of F_δ, all lengths

> **Parent audit (2026-10-19):** correct after one fix — Step 2 (δ = 4, 8) must first use the F10 dichotomy (a = 2 or b = 0); see verification/v10_odd_fix.py and REPORT.md.

**Scope.** δ ∈ {2,3,4,6,7,8,9}. n = R_L + (δ−1)·10^e with 0 ≤ e ≤ L−1. n is odd iff
(e ≥ 1 and δ even) or (δ odd, any e). Since 5 ∤ n (last digit 1 or δ ∉ {0,5}),
n 7-smooth ⟺

  (★)  9n = 10^L + A·10^e − 1 = 3^a·7^b,   A = 9(δ−1),  a ≥ 2,  b ≥ 0.

Known odd members (sieve to 10⁷ digits): 21 (δ=2,e=1), 81 (δ=8,e=1), and the single
digits 3, 7, 9 (δ=3,7,9, e=0, L=1).

**Plan (checkpoints appended below after each step):**
- §1 The workhorse: mod 8 × mod 5 parity obstruction (script v1_congruences.py)
- §2 Uniform kill for e ≥ 2; e=1 per δ; e=0 per δ; small-L direct checks
- §3 Brute-force cross-check to L = 1500 (script v2_brute.py)
- §4 Final theorem + status labels

## §0 Skeleton of the case analysis (to be verified)

Key elementary facts (F1–F4, to be certified in §1):
- (F1) 3^a·7^b mod 8 depends only on parities: (a even,b even)→1, (even,odd)→7,
  (odd,even)→3, (odd,odd)→5.
- (F2) 3^a·7^b ≡ 4 (mod 5) ⟹ a ≡ b (mod 2). [the four (a,b) mod 4 classes giving 4
  are (0,2),(1,3),(2,0),(3,1) — all same parity]
- (F3) a ≢ b (mod 2) ⟹ 3^a·7^b ≡ 2 or 3 (mod 5), never 4.
- (F4) a odd, b odd ⟹ 3^a·7^b ≡ 1 or 4 (mod 5), never 3; a even, b even and
  3^a·7^b = m² ⟹ m² mod p is a QR for every p.

For e ≥ 1, 5 | 10^L + A·10^e, so (★) forces 3^a·7^b ≡ −1 ≡ 4 (mod 5) ⟹ a ≡ b (mod 2).
The value of 10^L + A·10^e − 1 mod 8 (L ≥ 3) is 2(δ−1)·[e=1] − 1 ... details in §2.

Status: IN PROGRESS.

## §1 The workhorse lemmas — CERTIFIED (v1_congruences.py, F1–F13)

**Lemma W (parity workhorse).** Let a ≥ 2, b ≥ 0 with 3^a·7^b ≡ −1 (mod 5). Then
a ≡ b (mod 2). [F2: the only (a,b) mod 4 classes with 3^a·7^b ≡ 4 mod 5 are
(0,2),(1,3),(2,0),(3,1).] Consequently, if moreover 3^a·7^b ≡ 3 or 7 (mod 8), we get
a contradiction, since ≡ 3 mod 8 forces (a,b) ≡ (odd, even) and ≡ 7 forces
(even, odd) — opposite parities — while opposite parity forces 3^a·7^b ≡ 2 or 3 mod 5
[F3], not 4. Likewise 3^a·7^b ≡ 5 (mod 8) (both odd) forces 3^a·7^b ≡ 1 or 4 mod 5 [F4].

All facts F1–F13 certified by machine (finite checks, exact integers):
- F1: 3^a·7^b mod 8 = 1, 7, 3, 5 according as (a,b) ≡ (ee), (eo), (oe), (oo).
- F2/F3/F4: the mod-5 products by parity class.
- F5: 7^b mod 25 ∈ {1,7,24,18} (period 4); 21, 11 never occur.
- F6: 3^a ≡ 14 (mod 25) ⟺ a ≡ 18 (mod 20); 3^a ≡ −1 (mod 25) ⟺ a ≡ 10 (mod 20)
  (ord_{25}(3) = 20, 3 primitive root).
- F7: ord₇(3) = 6 and the class table.
- F8: 3^a mod 13 ∈ {1,3,9} (period 3); 10^L ≡ 10 (mod 13) for L ≡ 1 (mod 6); 449 ≡ 7.
- F9: QRs mod 5 = {0,1,4}, mod 11 = {0,1,3,4,5,9}; 89 ≡ 1 (mod 11); 17 ≡ 2 (mod 5).
- F10: class tables 27 | 10^L+c ⟺ L ≡ ℓ (mod 3), 7 | 10^L+c ⟺ L ≡ r (mod 6) for
  c ∈ {89, 269, 449, 629}: (ℓ, r) = (2,2), (0,4), (1,3), (2,0).
- F11: for L ≥ 3: (10^L + 90(δ−1)10^e − 1) mod 8 = (δ−1)·2 − 1 for e = 1 and = 7 for e ≥ 2
  (δ odd) / 3 (δ even); verified for L ∈ {3,4,5,8}.
- F12: e = 0 layer: c = 9δ−10 ≡ 1, 5, 7 (mod 8) for δ = 3, 7, 9.
- F13: direct small-case 7-smoothness checks (see §2, Step 0).

## §2 The closing case analysis — PROVED (elementary; every congruence certified in §1)

Throughout: 9n = 10^L + A·10^e − 1 = 3^a·7^b, A = 9(δ−1), a ≥ 2, b ≥ 0, 0 ≤ e ≤ L−1,
δ ∈ {2,3,4,6,7,8,9}.

**Standing congruences.**
(i) Mod 5: for e ≥ 1, 5 | 10^L + A·10^e, so 3^a·7^b ≡ −1 ≡ 4 (mod 5); by Lemma W,
**a ≡ b (mod 2)**. For e = 0: 3^a·7^b ≡ c = 9δ−10 (mod 5) and (mod 8) for L ≥ 3.
(ii) Mod 8, L ≥ 3 [F11]: 10^L ≡ 0, A·10^e ≡ (δ−1)·2 (e=1), 0 (e≥3), 4 (e=2, δ odd),
4 (e=2, δ even) — so 3^a·7^b ≡ (δ−1)·2 − 1 (e=1); ≡ 7 (e≥2); ≡ 3 (e=2, δ even).

**Step 0 (small L, direct).** [F13] The only solutions with L ≤ 3 not covered by the
L ≥ 3 congruences of (ii) are checked by exact factoring:
- e=0, L=1: 9n = 9δ → n = δ: 7-smooth exactly for δ ∈ {3,7,9} (n = 3, 7, 9). ✓ members
- e=0, L=2, δ odd: 9n = 100 + c, c ∈ {17,53,71}: 117 = 9·13, 153 = 9·17, 171 = 9·19. ✗
- e=1, L=2: n = 10δ+1: 7-smooth exactly for δ = 2 (21 = 3·7) and δ = 8 (81 = 3⁴). ✓
- e=1, L=3: n = 101+10δ ∈ {121,…,191}: none 3^a7^b-smooth. ✗
- e=2, L=3: n = 100δ+11 ∈ {211,…,911}: none. ✗
(For even δ, e=0 is the even layer of round 3b: {2,12,112,4,14,6,16,8,18}.)

**Step 1 (e ≥ 2, all δ): DEAD.** L ≥ e+1 ≥ 3, so (ii) applies: 3^a·7^b ≡ 7 (mod 8) if
δ odd (then A·10^e ≡ 0 mod 8 since v₂(A·10^e) ≥ 2 + v₂(δ−1) ≥ 3), and ≡ 3 (mod 8) if
e = 2, δ even (A·10² ≡ 4 mod 8); for e ≥ 3 also δ even gives ≡ 7. In every case the
residue is 3 or 7 mod 8, i.e. a,b have OPPOSITE parity [F1], contradicting the mod-5
same-parity requirement (i) [F2/F3]. Hence **no solutions with 2 ≤ e ≤ L−1, any δ**.
This uniformly kills the prompt's sub-case 2 (e = L−1) for L ≥ 4 and all of sub-case 3
with e ≥ 2 — no mod 2^k/5^k order bookkeeping and no size bounds are needed.

**Step 2 (e = 1, L ≥ 3, per δ).** By (ii) [F11], 3^a·7^b ≡ (δ−1)·2 − 1 (mod 8):
δ=2,6 → 1; δ=4,8 → 5; δ=3,7 → 3; δ=9 → 7.
- **δ ∈ {3,7,9}: DEAD immediately.** ≡ 3 or 7 (mod 8) forces opposite parity [F1],
  contradicting (i). [Kills the e=1 part of sub-case 1's odd-δ cousins and δ=9.]
- **δ = 4: 9n = 10^L + 269 ≡ 5 (mod 8).** If b ≥ 1: 7^b ≡ 269 ≡ 5 (mod 8) (as 9 ≡ 1),
  but 7^b ∈ {1,7} [F1]. If b = 0: 3^a ≡ 5 (mod 8), but 3^a ∈ {1,3}. DEAD.
- **δ = 8: 9n = 10^L + 629 ≡ 5 (mod 8):** identical kill. DEAD.
- **δ = 6: 9n = 10^L + 449.** Mod 8: ≡ 1, so a, b not forced opposite — need work.
  *Dichotomy* [F10]: a ≥ 3 ⟺ 27 | 10^L+449 ⟺ L ≡ 1 (mod 3); b ≥ 1 ⟺ 7 | 10^L+449 ⟺
  L ≡ 3 (mod 6) ⟹ L ≡ 0 (mod 3). Incompatible, so a = 2 or b = 0.
  – a = 2: 9·7^b = 10^L + 449; mod 25 (L ≥ 3): 7^b ≡ 449·9⁻¹ ≡ 24·14 ≡ 11 (mod 25),
    but 7^b mod 25 ∈ {1,7,24,18} [F5]. DEAD.
  – b = 0: 3^a = 10^L + 449 with a ≥ 3, so L ≡ 1 (mod 3), i.e. L ≡ 1 or 4 (mod 6)
    (b = 0 excludes L ≡ 3 mod 6).
    · L ≡ 4 (mod 6): mod 7: 3^a ≡ 3^L + 449 ≡ 4 + 1 = 5 (mod 7) [F7, 449 ≡ 1 mod 7]
      ⟹ a ≡ 5 (mod 6) ⟹ a odd; but mod 25: 3^a ≡ 449 ≡ −1 ⟹ a ≡ 10 (mod 20) [F6]
      ⟹ a even. Contradiction. DEAD.
    · L ≡ 1 (mod 6): mod 13: 3^a ≡ 10^L + 449 ≡ 10 + 7 ≡ 4 (mod 13) [F8], but
      3^a mod 13 ∈ {1,3,9} [F8]. DEAD.
- **δ = 2: 9n = 10^L + 89.**
  – a = 2: 9·7^b = 10^L + 89; mod 25 (L ≥ 3): 7^b ≡ 89·9⁻¹ ≡ 14·14 ≡ 21 (mod 25) ∉
    {1,7,24,18} [F5]. DEAD.
  – a ≥ 3 ⟹ L ≡ 2 (mod 3) [F10: 27 | 10^L+89 ⟺ L ≡ 2 mod 3]. Also 7 | 10^L+89 ⟺
    L ≡ 2 (mod 6) [F10]. Two sub-branches (L ≥ 3, so mod 8 applies: 10^L+89 ≡ 1,
    forcing a, b BOTH EVEN [F1]):
    · L ≡ 5 (mod 6): then b = 0 and 3^a = 10^L + 89, L ≥ 5. Mod 25: 3^a ≡ 89 ≡ 14 ⟹
      a ≡ 18 (mod 20) [F6] ⟹ a even. Mod 7: 3^a ≡ 3^L + 89 ≡ 5 + 5 ≡ 3 (mod 7)
      (L ≡ 5 mod 6 ⟹ 3^L ≡ 5 [F7]; 89 ≡ 5 mod 7) ⟹ a ≡ 1 (mod 6) [F7] ⟹ a odd.
      Contradiction. DEAD.
    · L ≡ 2 (mod 6): then b ≥ 1, and a, b both even, so 10^L + 89 = m² with
      m = 3^{a/2}·7^{b/2}. L even ⟹ 10^L ≡ 1 (mod 11); 89 ≡ 1 (mod 11) [F9] ⟹
      m² ≡ 2 (mod 11), but 2 is a quadratic non-residue mod 11 [F9]. DEAD.
  So δ=2, e=1 has only L = 2, n = 21 (Step 0). ✓

**Step 3 (e = 0, δ ∈ {3,7,9}, L ≥ 3).** 9n = 10^L + c, c = 9δ−10 ∈ {17, 53, 71}.
Mod 8: 3^a·7^b ≡ c (mod 8) [F12, since 10^L ≡ 0 for L ≥ 3]; mod 5: 3^a·7^b ≡ c (mod 5)
(since 5 | 10^L).
- δ=3 (c = 17 ≡ 1 mod 8): a, b both EVEN [F1] ⟹ 10^L + 17 = m²; but mod 5:
  m² ≡ 17 ≡ 2 (mod 5), and 2 is a non-residue mod 5 [F9]. DEAD.
- δ=7 (c = 53 ≡ 5 mod 8): a, b both ODD [F1] ⟹ 3^a·7^b ≡ 1 or 4 (mod 5) [F4];
  but c ≡ 53 ≡ 3 (mod 5). DEAD.
- δ=9 (c = 71 ≡ 7 mod 8): a even, b ODD — opposite parity ⟹ 3^a·7^b ≡ 2 or 3 (mod 5)
  [F3]; but c ≡ 71 ≡ 1 (mod 5). DEAD.
With Step 0 (L ≤ 2): δ=3,7,9 have exactly the members n = 3, 7, 9 (L=1). ✓

**Remark (why no Baker/Matveev is needed).** The prompt anticipated needing linear
forms in logarithms for 1 ≤ e ≤ L−2. In fact 3^a·7^b ≡ −1 (mod 5) pins the parities of
a and b to be EQUAL, while the mod-8 residue of 10^L + A·10^e − 1 pins them to be
OPPOSITE whenever that residue is 3 or 7 — which happens for ALL e ≥ 2 and for
δ ∈ {3,7,9} at e = 1. The surviving pairs (δ=2,4,6,8 at e=1; odd δ at e=0) die to
mod 25 / mod 7 / mod 13 / QR-mod-11 comparisons, each a finite residue fact. No size
bound, no lifting ladder beyond the first rung (mod 25), no p-adic logarithms.

## §3 Exhaustive cross-check — COMPUTED (v2_brute.py, L ≤ 1500, 22 s)

Every triple (δ, L, e), 1 ≤ L ≤ 1500, 0 ≤ e ≤ L−1, was tested by exact integer
arithmetic: 9n = 10^L + 9(δ−1)10^e − 1 is 2^t·3^a·7^b iff (δ, n) is one of the 14 known
members; moreover for every odd candidate (e ≥ 1 with even δ, any e with odd δ) the
value 9n has v₂ = 0 and is exactly 3^a·7^b. The found list is EXACTLY
 δ=2: {2, 12, 21, 112}; δ=3: {3}; δ=4: {4, 14}; δ=6: {6, 16}; δ=7: {7};
 δ=8: {8, 18, 81}; δ=9: {9},
matching the 10⁷-digit sieves and round 3b. No other member up to 1500 digits.

## §4 Final theorem (odd layer of F_δ, all L)

**Theorem.** Let δ ∈ {2,3,4,6,7,8,9} and n = R_L + (δ−1)·10^e (0 ≤ e ≤ L−1) be an ODD
7-smooth member of F_δ. Then exactly one of:
- δ = 2, e = 1, L = 2: n = 21 (9n = 189 = 3³·7);
- δ = 8, e = 1, L = 2: n = 81 (9n = 729 = 3⁶);
- δ ∈ {3,7,9}, e = 0, L = 1: n = δ ∈ {3, 7, 9} (9n = 27, 63, 81).

*Proof.* §2 Steps 0–3. Step 0 handles all cases with L ≤ 3 that escape the L ≥ 3
congruences (exact factoring, F13). Step 1 kills every e ≥ 2 (mod 8 residue 3 or 7 vs
mod-5 same-parity). Step 2 kills e = 1, L ≥ 3 for every δ (δ = 3,7,9 by mod 8 × mod 5;
δ = 4,8 by mod 8; δ = 6 and δ = 2 by the mod-25 / mod-7 / mod-13 / QR-mod-11 kills).
Step 3 kills e = 0, L ≥ 3 for δ = 3,7,9 (perfect-square mod 5; both-odd mod-5 class;
opposite-parity mod-5 class). ∎

**Status labels.**
- PROVED (elementary, allL): the theorem above. Every arithmetic input is certified in
  verification/glm/r4/v1_congruences.py (F1–F13); no conditional steps, no Baker-type
  input, no unproved order formulas (the deepest facts used are ord₂₅(3) = 20 with the
  two classes 10, 18 mod 20, ord₇(3) = 6, ord₁₃(3) = 3, and the QR sets mod 5, 11).
- COMPUTED: v2_brute.py exhaustive verification to L = 1500 (all 14 members, no others).
- CONJECTURAL: nothing in this layer.

**Combined with round 3b:** F_δ's 7-smooth members (single-non-1-digit layer) are
exactly {2, 12, 21, 112} (δ=2), {3} (δ=3), {4, 14} (δ=4), {6, 16} (δ=6), {7} (δ=7),
{8, 18, 81} (δ=8), {9} (δ=9), and {5, 15} for δ=5 (v8_delta5.py) — all PROVED for all L.

## §5 Artifacts
- verification/glm/r4/v1_congruences.py — F1–F13 finite congruence certificates.
- verification/glm/r4/v2_brute.py — exhaustive (δ, L, e) sweep to L = 1500.
Reproduce: bash -c 'ulimit -v 3000000; python3 -I verification/glm/r4/v{1,2}_*.py'
(v1: <1 s; v2: ≈ 25 s.)
