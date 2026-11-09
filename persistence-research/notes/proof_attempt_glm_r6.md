# Round 6 — Level 1 completeness via the H/A/M position split

**Scope.** Same objects as round 5: 7-smooth n with digit product δ ∈ {4,6,8,9} and
≥ 2 non-1 digits (multisets {2,2}, {2,3}, {2,4}, {2,2,2}, {3,3}). Write
S = Σ c_p·10^p over non-1 positions (c_p = digit − 1), so

  9n = 10^L − 1 + 9S = 10^L + 9S − 1,   n = 2^t·3^u·7^w (t = v₂(n), u = v₃(n), w = v₇(n)).

**Split (exhaustive).** Let p = lowest position of a non-1 digit, P = 2.

- **(H)** p ≥ 3 (no non-1 digit at positions ≤ 2). Claim: NO solution for any L.
- **(A)** ALL non-1 digits at positions ≤ 2. Then 9n = 10^L + K, K = 9S − 1, one of
  19 explicit constants. Goal: only the known solutions (K=188: L=2,6; K=116: L=2;
  K=278: L=2) exist, for all L.
- **(M)** MIXED: ≥ 1 non-1 digit at position ≤ 2 AND ≥ 1 at position q ≥ 3.
  Then 9n = 10^L + A·10^q + K (A = 9c_q) and, for {2,2,2}, possibly two far terms.

**Known members and their position profiles.**
- 32 = {2,3} at positions (0,1): all-low (A), K = 9·21 − 1 = 188, L = 2.
- 111132 = {2,3} at positions (0,1): all-low (A), K = 188, L = 6.
- 24 = {2,4} at positions (0,1) offsets (1,3): all-low (A), K = 9·31 − 1 = 278, L = 2.
- 42 = {2,4} at positions (0,1) offsets (3,1): all-low (A), K = 278, L = 2.
- 14112 = {2,4} at positions (0,3) offsets (1,3): MIXED (M): S_low = 1, far c=3 at q=3,
  A = 27, K = 8, L = 5.

## §0 Plan
- [x] §1 (H): proof + residue-table certificate (v1_H.py) — PROVED
- [x] §2 (A): constants, regimes, brute force, kill tree (v2_A.py, v3_survivors.py)
- [x] §3 (A): stage-2 deep sieve — all 19 constants CLOSED (v4_stage2.py)
- [x] §4 (M): parity kills + precise residual (v5_M.py)
- [x] §5 Final statement

## §1 (H) — all non-1 digits at positions ≥ 3

**Lemma H.** Let n = 2^t·3^u·7^w have digit product δ ∈ {4,6,8,9} with ≥ 2 non-1
digits, all at positions ≥ 3. Then no such n exists, for any L.

*Proof.* All non-1 positions ≥ 3 ⟹ S ≡ 0 (mod 1000) ⟹ S ≡ 0 (mod 8) and (mod 5).
Also L ≥ 4 (a non-1 digit sits at position ≥ 3), so 10^L ≡ 0 (mod 8) and (mod 5).
Hence 9n = 10^L + 9S − 1 ≡ −1 (mod 8) and (mod 5).
- Mod 8: 9n ≡ 7. Since 9 ≡ 1 (mod 8), n ≡ 7 (mod 8); in particular t = 0 (n odd)
  and 3^u·7^w ≡ 7 (mod 8). Now 3^u ≡ 1 (u even) or 3 (u odd); 7^w ≡ 1 (w even) or
  7 (w odd). The products are 1, 3, 5, 7 for (even,even), (odd,even), (odd,odd),
  (even,odd). So 3^u·7^w ≡ 7 (mod 8) ⟺ **u even and w odd**.
  [Note: the parent draft said "opposite parity"; the exact force is stronger:
  (u odd, w even) gives 3 ≠ 7, so only (u even, w odd) survives.]
- Mod 5: 9n ≡ 4, and 9 ≡ 4 (mod 5) with 4² = 16 ≡ 1, so n ≡ 4·4 = 16 ≡ 1 (mod 5);
  i.e. 3^u·7^w ≡ 1 (mod 5). Since 3 ≡ −2 (mod 5): 3^u·7^w ≡ (−1)^u·2^{u+w} (mod 5).
  u even ⟹ 2^{u+w} ≡ 1 ⟹ u + w ≡ 0 (mod 4); u odd ⟹ 2^{u+w} ≡ −1 ≡ 4 ⟹
  u + w ≡ 2 (mod 4). Both cases give **w ≡ u (mod 4)**, in particular u ≡ w (mod 2).

(u even, w odd) contradicts u ≡ w (mod 4). ∎ (No solution for any L; no size or
L-range hypothesis is used beyond L ≥ 4, which the position condition forces.)

Certificates (v1_H.py): the 4-row mod-8 table, the 16-row mod-5 table, and the
mod-1000 vanishing of S for all placements with positions ≥ 3.

### §1 certificate (v1_H.py) — DONE, all PASS
- C1: 3^u·7^w ≡ 7 (mod 8) ⟺ (u even, w odd) — 4-row table.
- C2: 3^u·7^w ≡ 1 (mod 5) ⟺ w ≡ u (mod 4) — 16-row table.
- C3: c·10^p ≡ 0 (mod 1000) for p ≥ 3; 10^L ≡ 0 (mod 8,5) for L ≥ 4.
- C4: exhaustive brute force (all 5 multisets, all placements with positions ≥ 3,
  L ≤ 60): ZERO members. Consistent with the lemma.
**Lemma H: PROVED for all L (elementary; no unproved hypothesis).**
Note: the parent draft's "mod 8 forces opposite parity" is correct but weak —
(u odd, w even) gives 3, not 7; the exact force is (u even, w odd). The
contradiction with w ≡ u (mod 4) stands either way.

## §2 (A) — landscape script (v2_A.py)

Setup: all non-1 digits at positions ≤ 2. 19 placements → 19 constants
K = 9S − 1 (S = c_0 + 10c_1 + 100c_2). Facts used:
- t = v₂(10^L+K) = t₀ := v₂(K) for L > t₀ (r5 Lemma A); 5 ∤ K (5 ∤ n).
- a := u+2 = v₃(10^L+K) ≥ 2 always; a ≥ 3 ⟺ 27 | 10^L+K ⟺ L ≡ ℓ (mod 3),
  ℓ = −(K+1)/9 mod 3 [10^L ≡ 1+9L mod 27].
- b := w = v₇(10^L+K); b ≥ 1 ⟺ 7 | 10^L+K ⟺ L ≡ r (mod 6) (or b = 0 ∀L if 7 | K).
- **Auxiliary-prime kill.** For a prime q ∉ {2,3,5,7} and L > t₀:
  3^{u+2}·7^w ≡ (10^L+K)·2^{−t₀} (mod q). Let o₃ = ord_q(3), o₇ = ord_q(7).
  (T1) necessary: (10^L+K)·2^{−t₀} ∈ ⟨3,7⟩ mod q, i.e. T^{lcm(o₃,o₇)} ≡ 1.
  (T2) if moreover L ≢ ℓ (mod 3) then a = 2 exactly, so necessary:
  (T·9^{−1})^{o₇} ≡ 1 (mod q), T = (10^L+K)·2^{−t₀}.
  Process primes successively with CRT refinement of surviving L-classes.

### §2 results (v2_A.py)
- 19 constants confirmed. Valid brute-force solutions (L > max position), L ≤ 3000:
  K=188: L=2 (n=32), L=6 (n=111132); K=116: L=2 (n=24); K=278: L=2 (n=42).
  All other K: none (K=98,908,998 hits were spurious L ≤ max(pos)).
- Regimes: BAD (ℓ ≡ r mod 3): K ∈ {188, 1889, 1079, 278, 926, 1979};
  void (7 | K): K=98 (S=11≡4 mod 7); good: the rest.
- Stage-1 kill (T1/T2, primes ≤ 5000, CRT refinement, caps hit at 11 primes):
  FULLY KILLED (no L > t₀ survives): K ∈ {98, 989, 116, 926, 998}.
  Survivors remain for the other 14 K → need stronger tests (v3).

### §2b stage-1 result (v3_survivors.py) — 17/19 CLOSED
Refinement: seed classes L mod 6 (a=2 exact / a≥3 via ℓ; w=0 exact / w≥1 via r),
λ-ladder (a ≥ k ⟺ L ≡ λ_k mod 3^{k−2}), μ-ladder (w ≥ k ⟺ L ≡ μ_k mod 6·7^{k−1}),
aux-prime region tests T = (10^L+K)2^{−t₀} ≡ 3^a7^w (mod q) with exact-a/w regions.
Greedy prime application + deepening. RESULT:
- CLOSED (no L > t₀ survives): K ∈ {98, 908, 989, 107, 917, 1079, 1808, 1889, 2708,
  2789, 926, 1169, 197, 1817, 1979, 998, 116} — 17 constants. With brute force
  (L ≤ 3000 ⊇ L ≤ t₀) these K contribute NO members beyond the known ones
  (K=116: L=2 → 24). [K=98,908,998 spurious small-L hits excluded by L > max pos.]
- OPEN: K=188 ({2,3} → 32, 111132), K=278 ({2,4} → 42). Their true-solution
  classes survive (as they must). → stage 2 (v4).

### §2c stage 2 (v4_stage2.py) — deep sieve: classes → (a,w)-regions → size-kill

Setup. Each surviving class is a residue ρ (mod M) with a *signature*
(a_lo, a_hi, w_lo, w_hi) computed from the certified λ- and μ-ladders:
a ≥ k ⟺ L ≡ λ_k (mod 3^{k−2}); w ≥ k ⟺ L ≡ μ_k (mod 6·7^{k−1}). A value is
*exact* (a_lo = a_hi) when some ladder level fails on the class; then a = a_hi
for **every** L ≡ ρ (mod M) — sound because the λ-test is pointwise.

Three kill rules, all necessary conditions for 10^L + K = 2^t·3^a·7^w:

- **T-test (auxiliary prime q, 3 ∤ 7 ∤ q).** If the equation holds at some
  L ≡ gg (mod d_q), then (10^gg + K)·2^{−t₀} ≡ 3^a·7^w (mod q). Region test:
  x := T·3^{−a_lo}·7^{−w_lo} must lie in the subgroup forced by the signature —
  ⟨3,7⟩ (both unbounded), ⟨3⟩ (w exact), ⟨7⟩ (a exact), {1} (both exact).
  Classes are refined mod M·d_q/gcd(M,d_q) so gg-alignment is exact.
- **Size-kill (both exact).** a·ln3 + w·ln7 = L·ln10 − t₀·ln2 + δ with
  δ = ln(1 + K/10^L) ∈ (0, ln(1+K/100)] pins L to ≤ 2 integers; candidates are
  factored exactly (7-smooth test). A both-exact class is **resolved**: every
  L in it is either a verified solution or dead. (First implementation used a
  sloppy δ ≤ 3.5 margin and *wrongly killed* K=278's L=2; fixed to
  δ ∈ (0, ln(1+K/100)] and every killed class cross-checked.)
- **Deepening** ×3 / ×7 alternated, picking the side with more unbounded
  signatures; primes ordered by |⟨3,7⟩|/(q−1) ascending (strongest region first).

Result (150–300 rounds, all primes < 50000):

- **K = 278 ({2,4} → 42): CLOSED.** Class set collapses to ∅; the only member
  of the level is L = 2 → 9n = 378 = 2·3³·7, n = **42**, machine-verified
  (t=1, a=3, w=1) and retained by the resolved-class bookkeeping.
- **K = 116 ({2,4} → 24): CLOSED** already at stage 1 (L = 2, n = 24).
- **K = 188 ({2,3} → 32, 111132): CLOSED.** Class set collapses to ∅
  (final modulus M = 87 496 446 240 with zero survivors; the T-tests with
  strongest-region-first prime ordering — |⟨3,7⟩|/(q−1) ascending, primes
  < 50000, applied to exhaustion before each deepening — terminate the sieve).
  L = 6 → 111132 verified in-place (t=2, a=4, w=3) and retained by the
  resolved-class bookkeeping.

Reproduced twice end-to-end (≈ 30 s total); artifacts: r6_v4_out.json,
k188_long2.log. During development the sieve was also validated in its
*incomplete* configuration (weak δ-margin, best-prime-only application): it
correctly retained the true-solution classes while killing everything else —
K = 188 held 757 686 classes mod 3.97·10^16 and K = 278 a single exhausted
class — so the closure is not an artifact of the tuned parameters.

**Status of (A): all 19 constants CLOSED.** The level-1 members with all
non-1 digits at positions ≤ 2 are exactly 32 (K=188, L=2), 111132 (K=188,
L=6), 24 (K=116, L=2), 42 (K=278, L=2) — the known list, nothing more.
No unproved hypotheses entered: every kill is a necessary condition of
9n = 10^L + K = 2^t·3^a·7^w certified by the λ/μ-ladder tables (§2), the
region subgroups, exact factoring of the ≤ 2 size-window candidates, and
brute force up to L = 3000.

## §3 (M) — MIXED: ≥1 digit at position ≤ 2 AND ≥1 digit at position q ≥ 3

Setup. Exactly the configurations skipped by (H) and (A). Write the far part
as A·10^q + (second far digit ·10^{q'} for {2,2,2} with two far digits),
3 ≤ q < q' ≤ L−1, A = 9·c (c ∈ {1,2,3} the far digit value), and
K = 9·S_low − 1 where S_low = Σ (low digit c_i)·10^{pos_i} over positions
0,1,2. Then

    9n = 10^L + A·10^q + K,   n = 2^t·3^{a−2}·7^w,

so 2^t·3^a·7^w = 10^L + A·10^q + K. Since A·10^q ≡ 10^L ≡ 0 (mod 10^q) for
q ≤ L, we get the characteristic mixed pin:

    (P)  2^t·3^a·7^w ≡ K (mod 10^q)      [q ≤ min(q', L)]

and t = t₀ := v₂(K) exactly whenever min(q, L) > t₀ (X ≡ K mod 2^{t₀+1}).

Config split (exhaustive; "low" = digit at position 0, 1 or 2):

  multiset   low digits chosen        S_low values
  {2,2}      one of two 1s            1, 10, 100
  {2,3}      the 1 or the 2           1,10,100 / 2,20,200
  {2,4}      the 1 or the 3           1,10,100 / 3,30,300
  {3,3}      one of two 2s            2, 20, 200
  {2,2,2}    one or two of three 1s   1,10,100 / 11,101,110

### §3a Parity kill (v5_M.py) — DEAD configurations

For each S_low: does ∃(t,a,w) with 2^t·3^a·7^w ≡ K (mod 8) and ≡ K (mod 5)?
If not, the configuration is impossible for **all** L and q (the mod-8 class
of 2^t·3^a·7^w forces (t mod 3, a mod 2, w mod 2); the mod-5 class forces
w ≡ a + κ(t) (mod 4); these are checked against all 8·4·4 small classes).

DEAD for all L, q (K mod 8 / mod 5 incompatible):

    S_low = 100 (K=899),  2 (17),  20 (179),  200 (1799),  3 (26),  300 (2699)

In configuration terms: {2,2} with the low 1 at position 2; {2,3} with the
low digit 2 at any position or the 1 at position 2; {2,4} with the low digit
3 at positions 0 or 2, or the 1 at position 2; **{3,3} in every position**;
{2,2,2} with the single low 1 at position 2. (Two-digit-low {2,2,2}
configurations all survive.) 12 mixed configurations remain, in 4 multisets,
with S_low ∈ {1, 10, 30, 11, 101, 110}.

### §3b Residual for the surviving configurations

For S_low ∈ {1, 10, 30, 11, 101, 110}, t = t₀ = v₂(9S_low − 1) is pinned and
the equation becomes

    (M*)  3^a·7^w = 2^{L−t₀}·5^L + A·2^{q−t₀}·5^q + c₀,   c₀ = K/2^{t₀},

with a ≥ 2, w ≥ 0 (w = 0 exactly when 7 ∤ 10^L + A·10^q + K),
L > q ≥ 3, the pin (P) mod 10^q, and the size window
a·ln3 + w·ln7 = L·ln10 − t₀·ln2 + ln(1 + K/10^L) + O(10^{q−L}).

Known member: S_low = 1, A = 27 (c = 3 at q = 3), L = 5:
10^5 + 27·10^3 + 8 = 127008 = 2^5·3^4·7^2 → n = 14112 ✓ (machine-checked,
including the pin 127008 ≡ 8 (mod 10^3)).

This is a 4-term S-unit equation over S = {2,3,5,7} — **open in general.**
The two-step effective route (stated, not attempted): a Pillai-type gap
bound (linear forms in two logarithms, effective) applied to
|3^a7^w − 2^{L−t₀}5^L| ≤ 3·10^q + |c₀| forces q ≥ L − C(log L)²; substituting
q = L − s, s = O(log²L), turns (M*) into a bounded-height S-unit equation
whose solutions are effectively enumerable, giving a computable L₀. Both
steps require explicit effective constants that we do not derive here.

The {2,2,2} two-far-digit variant replaces A·2^{q−t₀}5^q by
A₁2^{q₁−t₀}5^{q₁} + A₂2^{q₂−t₀}5^{q₂} (3 ≤ q₁ < q₂ ≤ L−1) and is open in the
same sense; its S_low values are the same six, with the same dead/surviving
split (the K values, hence §3a, are identical).

## §5 Final statement for Round 6

**Theorem (Level 1, proved).** Let n be 7-smooth with ≥ 2 non-1 digits and
δ(n) ∈ {4,6,8,9} (multisets {2,2},{2,3},{2,4},{2,2,2},{3,3}), and let 9n =
10^L − 1 + 9S. Under the position split (H) p ≥ 3 / (A) all ≤ 2 / (M) mixed:

- (H) No solutions, for every L. Proof: elementary mod-8 / mod-5
  contradiction ((u even, w odd) vs w ≡ u (mod 4)); certificate v1_H.py.
- (A) Exactly the known members 32, 111132 (K=188, L=2,6), 24 (K=116, L=2),
  42 (K=278, L=2), for every L. Proof: 19-constant reduction + λ/μ-ladder
  sieve + T-tests + size-kill; certificates v2_A.py, v3_survivors.py,
  v4_stage2.py (r6_v4_out.json), brute force to L = 3000 (v2_A.py).
- (M) All mixed configurations with S_low ∈ {2, 3, 20, 100, 200, 300}
  (K = 17, 26, 179, 899, 1799, 2699) are impossible for every L, q, by the
  mod-8/mod-5 parity conflict (v5_M.py). The 12 surviving configurations
  (S_low ∈ {1, 10, 30, 11, 101, 110}) reduce to the open 4-term S-unit
  equation (M*) with pin (P); 14112 is the known member
  (S_low=1, A=27, q=3, L=5).

**Residual open problem (precise).** Solve (M*): 3^a·7^w =
2^{L−t₀}5^L + A·2^{q−t₀}5^q + c₀ with a ≥ 2, w ≥ 0, L > q ≥ 3,
S_low ∈ {1,10,30,11,101,110} (K = 9S_low−1, t₀ = v₂(K), c₀ = K/2^{t₀}),
A ∈ {9,18,27}, subject to 2^{t₀}3^a7^w ≡ K (mod 10^q); plus the two-far-digit
{2,2,2} variant. Known: (S_low,A,q,L) = (1,27,3,5) → 14112. Everything else
is open; effective in principle via two-step Baker, not attempted here.
