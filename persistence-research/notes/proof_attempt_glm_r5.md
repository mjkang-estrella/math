# Round 5 — LEVEL 1 backward tree, nonzero terminal digits, ≥ 2 non-1 digits

**Scope.** All 7-smooth n with digit product δ ∈ {4, 6, 8, 9} having **two or more**
non-1 digits, for ALL lengths L. The digit multisets are:

- product 4: {2,2} — n = R_L + 10^i + 10^j
- product 6: {2,3} — n = R_L + 10^i + 2·10^j (either order)
- product 8: {2,4} and {2,2,2} — n = R_L + 10^i + 3·10^j; n = R_L + 10^i + 10^j + 10^k
- product 9: {3,3} — n = R_L + 2·10^i + 2·10^j

with positions 0 ≤ i < j (< k) ≤ L−1. Equivalently 9n = 10^L − 1 + Σ 9c_p·10^p where
c_p = digit − 1 ∈ {1,2,3} at the non-1 positions. n must be 2^t·3^A·7^B (5 ∤ n is
automatic: the last digit of n lies in {1,2,3,4}).

**Method.** Same elementary toolkit as rounds 3b/4:
- 2-adic ladder: for L ≥ k, R_L ≡ −9^{-1} (mod 2^k) and 10^p ≡ 0 (mod 2^k) for p ≥ k,
  so n mod 2^k is read off the low digits; this pins t = v₂(n) and 3^A·7^B mod 8.
- Mod 5: n ≡ 1 + c_0 (mod 5) for L ≥ 1, so 2^t·3^A·7^B ≡ 1 + c_0 (mod 5) — parity
  information on (A, B) given t.
- Mod 25 / 125: n ≡ 111 + c_0 + 10c_1 + 100c_2 (mod 125) for L ≥ 3 (positions ≥ 3
  vanish), ord_125(3) = 100 — pins A + sB mod 100.
- Digit sum: n ≡ L + C (mod 9), C = Σ c_p, so A ≥ 1 ⟺ 3 | (L + C); mod 27 similar.
- Mod 7 / 13 (period 6 in L and positions), quadratic residues when A, B both even.

**Status: COMPLETE (Level 1), with one precisely-stated open residual (§6).**

## §0 Plan
1. [x] Skeleton created.
2. [x] Brute force all four multisets to learn the answer (v1_brute.py).
3. [x] Consistency filter (2-adic t, mod-8 parity, mod-5 class) over all low-digit
       configurations (v2_configs.py).
4. [x] Per-config elementary proofs; anything resisting → OPEN with exact equation.
5. [x] Final theorem + cross-checks (v4/v5/v6); residual stated in §6.

## §1 Brute force — DONE (v1_brute.py; pairs L ≤ 500, triples L ≤ 200, 4m16s)

Exact integer arithmetic; n 7-smooth tested via 9n = 10^L − 1 + Σ 9c_p 10^p (divide
out 2,3,7; cofactor must be 1). The COMPLETE member list found:

| multiset | L | positions | offsets | n | 9n factorization |
|---|---|---|---|---|---|
| {2,2} | — | — | — | **none** | — |
| {2,3} | 2 | (0,1) | (1,2) | 32 | 2^5·3^2 (n = 2^5·3) |
| {2,3} | 6 | (0,1) | (1,2) | 111132 | 2^2·3^6·7^3 (n = 2^2·3^4·7^3) |
| {2,4} | 2 | (0,1) | (1,3) | 24 | 2^3·3^3 (n = 2^3·3) |
| {2,4} | 2 | (0,1) | (3,1) | 42 | 2·3^3·7 (n = 3^3·7) |
| {2,4} | 5 | (0,3) | (1,3) | 14112 | 2^5·3^4·7^2 (n = 2^5·3^2·7^2) |
| {3,3} | — | — | — | **none** | — |
| {2,2,2} | — | — | — | **none** | — |

(The parent's suggested "22, 112" are NOT members: 22 = 2·11 is not 7-smooth, and
112 has only ONE non-1 digit — it is a round-3b/4 member.)

So the expected answer is: {2,2}: ∅; {2,3}: {32, 111132}; {2,4}: {24, 42, 14112};
{3,3}: ∅; {2,2,2}: ∅. Now to be PROVED for all L.

Low-digit configurations (c_0, c_1, c_2, …) of the members:
- (c_0,c_1) = (1,2): {2,3} — L = 2 and 6.
- (1,3) and (3,1): {2,4} — L = 2 only.
- (1,0,0,3): {2,4} — L = 5 only.

## §2 Structural setup

Write S = Σ_{p ∈ P} c_p·10^p (P = positions of non-1 digits, c_p = digit − 1). Then

  9n = 10^L − 1 + 9S = 10^L + K,  K := 9S − 1,   n = 2^t·3^A·7^B (A ≥ 0, B ≥ 0).

**Lemma A (t is eventually constant).** t = v₂(10^L + K). If L > t₀ := v₂(K) then
t = t₀. *Proof.* 10^L = 2^L·5^L ≡ 0 (mod 2^{t₀+1}) when L ≥ t₀+1, so
v₂(10^L + K) = v₂(K). ∎ (t₀ depends only on the digit placement, via the ladder
Σ_{p<k} c_p 10^p ≡ 9^{-1} (mod 2^k); since v₂(10^p) = p, digits at positions ≥ k do
not affect the condition at rung k.)

**Lemma B (fixed low residues for L large).** For L ≥ k: 10^L ≡ 0 (mod 2^k) and
(mod 5^k), and 9 is invertible mod both. Hence for L ≥ k:
- n ≡ K·9^{-1} (mod 2^k) — pins t = v₂(n) and 3^A·7^B mod 8 (need k ≥ t₀+3);
- n ≡ 1 + c_0 (mod 5)  [since K·9^{-1} = S − 9^{-1} ≡ c_0 − 9^{-1}, 9^{-1} ≡ 4 mod 5];
- n ≡ S₃ − 14 (mod 125) for L ≥ 3, where S₃ = c_0 + 10c_1 + 100c_2 (positions ≥ 3
  vanish mod 125; 9^{-1} ≡ 14 mod 125). So 2^t·3^A·7^B ≡ S₃ − 14 (mod 125).
- 3^A·7^B ≡ K·2^{-t}·9^{-1} (mod 2^k) for all k ≤ L − t — a very strong 2-adic pin.

**Constraints used (stage 1, L ≥ 26, positions ≤ 24):** with t = t₀ fixed,
(i) 3^A·7^B ≡ (K/2^{t₀})·9^{-1} (mod 8) → parity class of (A, B);
(ii) 2^{t₀}·3^A·7^B ≡ 1 + c_0 (mod 5);
(iii) 2^{t₀}·3^A·7^B ≡ S₃ − 14 (mod 125) → A + s·B ≡ κ (mod 100), s = dlog₃(7) mod 100.
Joint unsolvability of (i)-(iii) kills a placement for ALL L ≥ 26. L ≤ 25 is checked
by direct factoring. Placements with K ≡ 0 (mod 2^{25}) are flagged DEEP.

## §3 Essential low configurations — DONE (v3_essential.py)

Since v₂(10^p) = p, positions ≥ 11 do not affect K mod 2^{11}, and the stage-1 data
(t₀, odd-part mod 8, mod-5 and mod-125 targets) depends only on positions ≤ 10
(max t₀ over ALL placements = 7, so t₀ + 3 ≤ 10). Grouping placements by their
stage-1 data leaves **32 essential survivor groups** ({3,3}: ZERO — see §5).
They are tabulated in the script output; each carries:
- its low digits (c_0, c_1, c_2) and t₀;
- the odd-part residue O = 3^A·7^B mod 8, i.e. the parity class of (A, B);
- the (A mod 100, B mod 20) solution classes of 2^{t₀}·3^A·7^B ≡ S₃ − 14 (mod 125)
  (always exactly 10 classes, one per allowed A in a fixed residue class mod 10).

**Lemma C (the 5-adic pin is exactly stage-1 (iii)).** For all k ≤ L,
3^A·7^B ≡ K·2^{-t}·9^{-1} (mod 5^k). Writing s = dlog₃(7) in Z_5 (s ≡ 55 mod 100,
so 5 | s), the class lattice (A,B) ≡ (a₀,b₀) (mod (100,20)) meets the level-k solution
set iff a₀ + s₂b₀ ≡ κ₂ (mod 100) — precisely stage-1 (iii). *Proof:* the level-k
solution set is {A + sB ≡ κ_k mod 4·5^{k−1}}; the class lattice reaches
a₀ + s b₀ + 100Z + 20sZ = a₀ + s b₀ + 100Z (as 5 | s ⟹ gcd(100, 20s) = 100), and
s ≡ s₂, κ ≡ κ₂ (mod 100) by nesting. ∎ (Certified in v4: s ≡ 55 mod 100, and the
mod-625/5^6-level compatibility adds nothing beyond mod 100 for every group.)

**Lemma D (2-adic pin, refinement).** For m ≤ L − t: 3^A·7^B ≡ K·2^{-t}·9^{-1}
(mod 2^m), and (A, B) mod (2^{m−2}, 2^{m−2}) is UNIQUE when solvable (writing
3 = −5^{w₃}, 7 = −5^{w₇} in (Z/2^m)*, the system A+B ≡ ε, Aw₃+Bw₇ ≡ w has odd
determinant w₇ − w₃). For m ≤ 10 this depends only on positions ≤ 10; the class
lattice (100,20) meets it iff (a₀,b₀) matches the unique solution mod (4,4)
(m ≥ 7). This kills some stage-1 classes outright (checked in v4).

**Lemma E (size window).** K = 9S − 1 ∈ [8, 3·10^L), so
3^A·7^B = (10^L + K)/(9·2^t) ∈ [10^L/(9·2^t), 4·10^L/(9·2^t)].
With t ≤ 7: A·log₃10 + B·(log₃7 − wait) — in natural logs:
A·ln3 + B·ln7 ∈ [L·ln10 − ln(9·2^t), L·ln10 − ln(9·2^t) + ln4].
Since ln4/ln7 < 1 and ln4/ln3 < 2, for each class (a₀, b₀) there are at most ~2
candidate integers B near 1.1833·L − log₇(9·2^t) and correspondingly ≤ 2 for A —
i.e. **(A, B) is pinned to O(1) candidates per class per L**.

**Lemma F (size bound outside fixed points; transfers verbatim from r3b Lemma 3).**
If a := A+2 ≥ 3 and L is not the least representative λ_a of the class
{10^x ≡ −K mod 3^a} (mod 3^{a−2}), then 3^a ≤ 9L; if b := B ≥ 2 and L ≠ μ_b (least
representative mod 6·7^{b−1} of 10^x ≡ −K mod 7^b), then 7^b ≤ 7L. (Uses only
ord_{3^k}(10) = 3^{k−2}, ord_{7^k}(10) = 6·7^{k−1}, independent of K.)

**Valuation transfer.** Write A = v₃(n), B = v₇(n), so 9n = 10^L + K = 9·2^t·3^A·7^B
and v₃(10^L+K) = A+2, v₇(10^L+K) = B. Since K = 9S−1 ≡ −1 (mod 9), the map
x ↦ 10^x on 3-adic units hits −K: for A ≥ 1, 3^(A+2) | 10^L+K ⟺ L ≡ λ_{A+2}
(mod 3^A) for a unique class λ_{A+2} (v6 C1; transfer of r3b F1/F3 — only
K ≡ −1 mod 9 is used). If 1 − 9S ≢ 0 (mod 7), then for B ≥ 1, 7^B | 10^L+K ⟺
L ≡ μ_B (mod 6·7^(B−1)) for a unique class μ_B (v6 C2; transfer of r3b F2/F3).
If 1 − 9S ≡ 0 (mod 7) (i.e. S ≡ 4 mod 7) then 7 ∤ 9n for EVERY L: B = 0 forced.
All solutions have t = v₂(K) = v₂(9S_low − 1) ≤ 10 (v6 C4: no deep-low config
exists; in fact all 632 essential configs have t ≤ 7).

**Theorem 1 (trichotomy).** For every L ≥ 6, any solution satisfies
**(A ≥ 1 and L = λ_{A+2}) or (B ≥ 1 and L = μ_B).**
*Proof.* Suppose neither holds. Note 3^A·7^B = (10^L+K)/(9·2^t) ≥ 10^L/9216.
If A ≥ 1 and L ≠ λ_{A+2}: L ≥ λ_{A+2} + 3^A ≥ 3^A, so 3^A ≤ L (r3b Lemma-3
pattern). If B ≥ 1 and L ≠ μ_B: L ≥ 6·7^(B−1), so 7^B ≤ 7L/6. Four cases:
(A ≥ 1, B ≥ 1): 3^A·7^B ≤ 7L²/6 ≤ (7/6)·10^L/10752 < 10^L/9216, contradiction
(v6 C3: 10^L > 10752L² for L ≥ 6). (A = 0, B ≥ 1): 7^B ≤ 7L/6 vs 7^B ≥ 10^L/9216
gives 10^L ≤ 10752L, false for L ≥ 6. (A ≥ 1, B = 0): 3^A ≤ L vs 3^A ≥ 10^L/9216
gives 10^L ≤ 9216L, false for L ≥ 5. (A = B = 0): 10^L + K = 9·2^t ≤ 9216 < 10^L. ∎

**Dichotomy (stage 2).** A ≥ 1 ⟺ 27 | 9n ⟺ 10^L ≡ 1 − 9S (mod 27); since
10^x = (1+9)^x ≡ 1 + 9x (mod 27), this is L ≡ −S (mod 3). B ≥ 1 ⟺ 10^L ≡ 1 − 9S
(mod 7) ⟺ 3^L ≡ 1 − 2S (mod 7) ⟺ L ≡ μ₁ (mod 6), where 3^{μ₁} ≡ 1 − 2S (mod 7).
Three regimes over S mod 21 (v6 C5, by direct enumeration):
- **Void** S mod 21 ∈ {4, 11, 18} (S ≡ 4 mod 7): B = 0 for every L; every
  solution is pure-3 and Theorem 1 forces L = λ_{A+2}.
- **Good** S mod 21 ∈ {1,3,5,6,7,8,9,12,13,14,16,17}: −S ≢ μ₁ (mod 3), so A ≥ 1
  and B ≥ 1 are incompatible: at every L, A = 0 or B = 0 — pure forms
  n = 2^t·3^A or n = 2^t·7^B; at the fixed point holding for that L the other
  prime is absent exactly as in r3b Lemma 4.
- **Bad** S mod 21 ∈ {0,2,10,15,19,20}: −S ≡ μ₁ (mod 3), both primes may occur
  together; no pure-form reduction. [CORRECTION of an earlier draft: the bad set
  has SIX residues, not {0,10,20} — v6 C5.]

## §4 The per-L filter (v4_filter.py), L ∈ [26, 6000]

For each essential group and each L, every solution must satisfy ALL of:
(N0) v₂(n mod 2^11) = t₀  [n mod 2^11 = (11111111111 + S_low) mod 2^11];
(N1) (A,B) in a stage-1 class (a₀,b₀) mod (100,20);
(N2) 2-adic coset: 3^A·7^B ≡ (n_low/2^t) mod 2^{11−t}; writing d = dlog₃(49) mod
     2^{11−t} (49 = 3^d, well-posed since 49 ≡ 1 mod 16), the kernel of
     (A,B) ↦ 3^A7^B contains (−d, 2), so A + (d/2)·B is coset-invariant mod
     2^{11−t−2}: A ≡ G − (d/2)B (mod 2^{9−t}) with G fixed per group;
(N3) size strip: (10^L + K_lo)/(9·2^t) ≤ 3^A·7^B ≤ (10^L + K_hi)/(9·2^t), where
     K_lo/hi bound K = 9S − 1 using the far digits at their lowest/highest positions;
(N4) the exact last-11-digits congruence 2^t·3^A·7^B ≡ n_low (mod 10^min(L,11));
(N5) (not needed): the class list contains b₀ = 0 for every group, so "B ≥ 1
     forced" never occurs at class level; the B = 0 branch is covered by the
     strip search below.
The filter enumerates, per class, A ≡ a₀ (mod 100) against (N3) — the strip cuts
this to ≤ 2 integer candidates per A — then applies the (N2) congruence via the
CRT modulus lcm(2^{9−t}, 100) and finally the exact (N4) power check.
Survivors would be reported for exact verification; the round finds NONE (§5).

## §5 Filter results (v4_filter.py, L ∈ [26, 6000]) — ZERO survivors

Essential configurations: assignments of the multiset's digits (offsets
c = digit − 1) to positions 0..10 or "FAR" (position ≥ 11), deduped by
(S_low, far-multiset): {2,2}: 67, {2,3}: 133, {2,4}: 133, {3,3}: 67,
{2,2,2}: 232 — 632 total. No config died at (N0) or the deep-low test and no
5 | K or empty-coset config occurred; all 632 entered the per-L filter with
5 of the 20 stage-1 classes surviving the 2-adic invariant check on average.

**COMPUTED (exact where decisive).** For every essential configuration, every
stage-1 class and every L ∈ [26, 6000] there is NO pair (A, B) satisfying
(N2) ∧ (N3) ∧ (N4). Hence **no member of any of the five multisets has
26 ≤ L ≤ 6000**. Together with v1's exhaustive search (pairs L ≤ 500, triples
L ≤ 200, exact integer arithmetic) this covers all L ≤ 6000: the only members
are 32, 111132 ({2,3}), 24, 42, 14112 ({2,4}) and none for {2,2}, {3,3}, {2,2,2}.

Soundness of the fast path. The only inexact step is the float evaluation of
the strip bounds (relative error ~1e-15 on values ~2.3·L ≤ 1.4·10^4, absolute
~1e-11, against 1e-6 search margins), and every candidate that survives the
strip is re-verified by the exact big-integer power computation (N4); a float
error can only create spurious candidates, which (N4) then removes — it can
never suppress a true solution. The class list is complete: any (A, B) meeting
the depth-11 5-adic pin satisfies A + 55B ≡ κ (mod 100) (Lemma C), i.e. lies in
the enumerated classes. The 2-adic invariant A + (d/2)B ≡ G (mod 2^(9−t)) was
assert-verified on every coset point.

Validation.
- *Positive control*: the member 111132 (L = 6, S = 21, t = 2, A = 4, B = 3)
  satisfies every filter condition at its true L (class (4,3), coset, exact
  strip point, (N4)) — the machinery finds solutions that exist.
- *Exact cross-check* (v5_crosscheck.py): for 30 sampled (config, L ∈
  {100,137,500}) pairs per multiset (90 total), a from-scratch brute force over
  ALL (A, B) with 9·2^t·3^A·7^B ∈ [10^L+K_lo, 10^L+K_hi] in exact integer
  arithmetic, checking class membership, the coset invariant and (N4), agrees
  with the fast path: no survivors.

## §6 Reduction of L > 6000 and the precise residual

By Theorem 1 (valid for all L ≥ 6), any solution with L > 6000 satisfies
(A ≥ 1 and L = λ_{A+2}) or (B ≥ 1 and L = μ_B). The dichotomy of §3 splits S
mod 21 into void/good/bad regimes; in the void and good regimes one of A, B is
zero at every L, so n = 2^t·3^A or n = 2^t·7^B (pure forms); in the bad regime
both may occur. In EVERY regime, a solution is exactly a number of the form

  n = 2^t·3^A·7^B,  t = v₂(9S−1) ≤ 10,  A, B ≥ 0,

whose decimal expansion has L ≥ 6001 digits, all equal to 1 except that the
multiset's digits (digit = 1 + c) appear at the positions p with c_p ≠ 0
(equivalently: 2^t·3^A·7^B = R_L + S with S of the required digit shape).
Conversely any such number IS a member (its digit product is the multiset's δ
and it is 7-smooth by construction; then 9n = 10^L + 9S − 1 automatically).
Note the size chain also re-derives the fixed point: A ≈ 2.1L ≫ log₃(9L) gives
3^A > 9L, whence L = λ_{A+2} (r3b F5 pattern), so the fixed-point condition
adds nothing beyond the digit shape.

**Residual (OPEN).** Whether such 2^t·3^A·7^B with ≥ 6001 digits exist. For
B = 0 this asks whether 2^t·3^A can have all digits in {1,2,3,4} (mostly 1s)
with a prescribed multiset of deviations — an Erdős-type question on digits of
S-smooth numbers, open with current methods (cf. the conjecture that large
powers of 2 contain a digit outside any fixed proper digit set). What the round
*has* established: the last 11 digits of any hypothetical member are completely
determined by its low configuration and must satisfy (N0)–(N4) — in particular
2^t·3^A·7^B ≡ 11111111111 + S_low (mod 10^11) — and no configuration survives
those pins together with the size strip for any L ≤ 6000.

**Final statement (Level 1, pairs and triples with δ ∈ {4,6,8,9} and ≥ 2
non-1 digits).** The complete member list is
  {2,2}: ∅;  {2,3}: {32, 111132};  {2,4}: {24, 42, 14112};
  {3,3}: ∅;  {2,2,2}: ∅,
conditional exactly on: no 2^t·3^A·7^B (t ≤ 10) with ≥ 6001 digits has the
digit shape 1…1 plus the multiset's digits. All other steps are proved
elementarily or verified by exact computation as cited.

## §7 Status

- §1 brute force: DONE (v1). §2 structural setup: DONE. §3 lemmas + corrected
  dichotomy: DONE (v6 certificates). §4–§5 filter: DONE (v4, cross-checked v5,
  positive control). §6 residual: precisely stated, OPEN (Erdős-type).
- Scripts: verification/glm/r5/{v1_brute, v2_configs, v3_essential,
  v4_filter, v5_crosscheck, v6_cert}.py.
