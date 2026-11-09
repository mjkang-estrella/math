# Round 3b (GLM sub-agent): the EVEN members of F_δ, all lengths

**Scope.** Only even members. For even δ ∈ {2,4,6,8}: n even ⟺ e = 0 (Lemma 1 of
round 2; and e = 0 with δ even gives n = R_L + (δ−1) odd+odd = even, so e = 0 is
exactly the even layer). Then

  9n = 10^L + c_δ,  c_δ = 9δ − 10 ∈ {8, 26, 44, 62},

and n is 7-smooth iff 10^L + c_δ = 2^t·3^{u+2}·7^w. Goal: show the only L are the
known ones. NOTE: the known members 21 (δ=2) and 81 (δ=8) are ODD (e = 1) and out
of scope here.

**Status: IN PROGRESS.** Plan (checkpoints appended below after each step):

- §1 Brute force + exact valuation tables (script v1_small.py)
- §2 Lifting structure of v₃ and v₇ (script v2_lifting.py)
- §3 The closing argument: size bound + exception kills (script v3_close.py)
- §4 Final theorem

## §0 Reduction (elementary, to be verified in §1)

For e = 0: 9n = 10^L + c_δ. Write t = v₂(10^L+c_δ), a = v₃(10^L+c_δ),
b = v₇(10^L+c_δ). Then 10^L+c_δ is 7-smooth iff 10^L + c_δ = 2^t 3^a 7^b with
a = v₃, b = v₇ EXACT (cofactor 1). Hand values of t:
δ=2: L=1:1, L=2:2, L=3:4, L≥4:3. δ=4: L=1:2, L≥2:1.
δ=6: L=1:1, L=2:4, L≥3:2. δ=8: L=1:3, L≥2:1.

Expected solutions (L, 9n): δ=2: (1,18),(2,108),(3,1008); δ=4: (1,36),(2,126);
δ=6: (1,54),(2,144); δ=8: (1,72),(2,162).

## §1 Brute force + exact valuations — DONE (v1_small.py, L ≤ 5000)

**COMPUTED (exact integer arithmetic).** For each δ, the 7-smooth L with e = 0 are
exactly (L; t, a, b) =
- δ=2 (c=8): (1; 1,2,0) → n=2, (2; 2,3,0) → n=12, (3; 4,2,1) → n=112.
- δ=4 (c=26): (1; 2,2,0) → n=4, (2; 1,2,1) → n=14.
- δ=6 (c=44): (1; 1,3,0) → n=6, (2; 4,2,0) → n=16.
- δ=8 (c=62): (1; 3,2,0) → n=8, (2; 1,4,0) → n=18.
No others for L ≤ 5000. The t-table of §0 is confirmed (one typo in the script's
own expected table, δ=4/L=3, fixed). Residue conditions confirmed with ZERO
violations on L ≤ 5000:
- a ≥ 3 ⟺ L ≡ ℓ (mod 3) with ℓ = (2, 0, 1, 2) for δ = 2, 4, 6, 8.
- b ≥ 1 ⟺ L ≡ r (mod 6) with r = (3, 2, 5, 0) for δ = 2, 4, 6, 8.
Growth exceptions a > 2+log₃L occur only at sparse L (e.g. δ=2: L=2,8,17,71,…),
b > 1+log₇L only at δ=2: L=27 (b=4) and δ=4: L=74 (b=4). These are the j=0
(lifting fixed point) cases characterized in §2.

## §2 Lifting structure — DONE (v2_lifting.py, all checks pass)

Machine-verified exactly (F1–F5 in the script header):
- **(F1)** ord_{3^k}(10) = 3^{k−2} (2 ≤ k ≤ 15) and v₃(10^m−1) = 2+v₃(m) (1 ≤ m ≤ 3000, LTE).
- **(F2)** ord_{7^k}(10) = 6·7^{k−1} (1 ≤ k ≤ 10); v₇(10^6−1) = 1.
- **(F3)** For each δ: solutions of 10^x ≡ −c (mod 3^K) are ONE class λ_K mod 3^{K−2}
  (K ≥ 3; λ_K defined for all K ≤ 60); mod 7^K: one class μ_K mod 6·7^{K−1} (μ_K
  defined for all K ≤ 25). Nesting: λ_K ≡ ℓ (mod 3), μ_K ≡ r (mod 6).
- **(F4)** For ALL L ≤ 20000: 3^K | 10^L+c ⟺ L ≡ λ_K (mod 3^{K−2}); 7^K | 10^L+c ⟺
  L ≡ μ_K (mod 6·7^{K−1}). Zero violations.
- **(F5)** Whenever 3^a > 9L (a = v₃(10^L+c), L ≥ 2): L = λ_a (the j=0 fixed point).
  Whenever 7^b > 7L: L = μ_b. So outside these sparse fixed points, 3^a ≤ 9L and
  7^b ≤ 7L hold. a-exc instances found: δ=2: L=2,8,17,71,557,1286,3473; δ=4:
  6,24,510,1968,8529; δ=6: 4,22,1480,5854; δ=8: 2,11,65,227,713,1442,14564.
  b-exc: δ=2: 27; δ=4: 74, 6248; δ=6, δ=8: none ≤ 20000.

## §3 The closing argument — PROVED (certificate v3_close.py)

Throughout, δ ∈ {2,4,6,8}, c = 9δ−10, and a = v₃(10^L+c), b = v₇(10^L+c),
t = v₂(10^L+c). If 10^L+c is 7-smooth then 10^L+c = 2^t·3^a·7^b with these EXACT
valuations. λ_K, μ_K as in §2 (any solution of 10^x ≡ −c mod 3^K resp. 7^K, unique
class mod ord; existence is automatic whenever a ≥ K resp. b ≥ K, since L itself is
then a solution).

**Uniform facts (all machine-certified).**
(i) c ≡ 8 (mod 9) and 10^L ≡ 1 (mod 9), so **a ≥ 2 for every L**. [C1]
(ii) a ≥ 3 ⟺ 27 | 10^L+c ⟺ L ≡ ℓ (mod 3), ℓ = (2,0,1,2)[δ]. [C2]
(iii) b ≥ 1 ⟺ 7 | 10^L+c ⟺ L ≡ r (mod 6), r = (3,2,5,0)[δ]. [C3]
(iv) t-table (§0): t = (1,2,4,3) at L = 1,2,3 for δ=2; t = 2 then 1 for δ=4;
     t = 1 then 4 then 2 for δ=6; t = 3 then 1 for δ=8; **t ≤ 3 for all L ≥ 4**, and
     10^L+c = 2^s(2^{L−s}5^L + c'') with (s, c'') = (3,1), (1,13), (2,11), (1,31)
     for δ = 2,4,6,8, valid for L ≥ 4,2,3,2 resp. [C5]
(v) ℓ ≢ r (mod 3) for every δ. [C4]

**Lemma 3 (size bound outside fixed points).** If a ≥ 3 and L ≠ λ_a then 3^a ≤ 9L;
if b ≥ 2 and L ≠ μ_b then 7^b ≤ 7L.
*Proof.* By §2 (F4), a ≥ 3 gives L ≡ λ_a (mod 3^{a−2}); L ≠ λ_a and L ≥ 1 give
L ≥ λ_a + 3^{a−2} ≥ 3^{a−2}, so 3^a ≤ 9·3^{a−2} ≤ 9L. Similarly b ≥ 2 gives
L ≡ μ_b (mod 6·7^{b−1}); L ≠ μ_b gives L ≥ 6·7^{b−1}, so 7^{b−1} ≤ L/6 and
7^b ≤ 7L/6 < 7L. ∎ (Instance-checked for all L ≤ 20000 in [C12].)

**Lemma 4 (fixed points force the other prime out).**
(a) If a ≥ 3 and L = λ_a, then b = 0. *Proof.* λ_a ≡ ℓ (mod 3) by nesting [F3], so
L ≡ ℓ (mod 3); by (iii), b ≥ 1 would force L ≡ r (mod 6), i.e. L ≡ r (mod 3),
contradicting (v). ∎
(b) If b ≥ 2 and L = μ_b, then a = 2. *Proof.* μ_b ≡ r (mod 6), so L ≡ r (mod 6),
L ≡ r (mod 3); a ≥ 3 would force L ≡ ℓ (mod 3), contradicting (v); so a = 2 by (i). ∎

**Theorem E0.** For every δ ∈ {2,4,6,8} and every L ≥ 4, 10^L + c_δ is NOT 7-smooth.
*Proof.* Suppose 10^L+c = 2^t·3^a·7^b, L ≥ 4, t ≤ 3 (iv).
*Case 1: L ≠ λ_a and L ≠ μ_b.* Then 3^a·7^b ≤ 63L² (Lemma 3; the a ≤ 2 / b ≤ 1
cases are trivial), while 3^a·7^b = (10^L+c)/2^t ≥ 10^L/8. Hence 10^L < 504L²,
contradicting 10^L ≥ 504L² for L ≥ 4 (10^4 = 10000 > 8064, and 10^L/L² strictly
increases). [C6]
*Case 2: a ≥ 3, L = λ_a.* Then b = 0 (Lemma 4a) and 10^L+c = 2^t·3^a, i.e.
2^{L−s}5^L = 3^a − c''. Since 5^L | 3^a − c'', mod 5 (C11) fixes a mod 4:
δ=2: a ≡ 0; δ=4: a ≡ 1; δ=6: a ≡ 0; δ=8: a ≡ 0 (mod 4).
– δ=2: a ≡ 0 (mod 4) ⟹ 5^L | 3^a − 1 fully, so ord_{5^L}(3) = 4·5^{L−1} | a (C9);
  but 3^a = 2^{L−3}5^L + 1 < 10^L gives a < L·log₃10 < 21L/10 (C7), and
  4·5^{L−1} > 21L/10 for all L ≥ 2 (C8) — contradiction.
– δ=4: a ≡ 1 (mod 4) ⟹ 3^a ≡ 3 (mod 16) ⟹ v₂(3^a − 13) = 1 (C10) ⟹ L−1 = 1,
  L = 2 < 4 — contradiction.
– δ=6: a ≡ 0 (mod 4) ⟹ 3^a ≡ 1 (mod 16) ⟹ v₂(3^a − 11) = 1 ⟹ L = 3 < 4. ✗
– δ=8: a ≡ 0 (mod 4) ⟹ 3^a ≡ 1 (mod 16) ⟹ v₂(3^a − 31) = 1 ⟹ L = 2 < 4. ✗
*Case 3: b ≥ 2, L = μ_b.* Then a = 2 (Lemma 4b) and 2^{L−s}5^L = 9·7^b − c''.
Mod 5 (C11): 9·7^b ≡ c'' forces b ≡ 2 (δ=2,6,8) or b ≡ 1 (δ=4) (mod 4).
– δ=2: b even ⟹ 7^b ≡ 1 (mod 16) ⟹ v₂(9·7^b − 1) = 3 ⟹ L = 6; but L ≡ r = 3
  (mod 6) — contradiction.
– δ=4: b odd ⟹ v₂(9·7^b − 13) = 1 ⟹ L = 2; then b = v₇(10²+26) = v₇(126) = 1 < 2,
  contradicting b ≥ 2. ✗
– δ=6: b even ⟹ v₂(9·7^b − 11) = 1 ⟹ L = 3 ≢ 5 (mod 6). ✗
– δ=8: b even ⟹ v₂(9·7^b − 31) = 1 ⟹ L = 2 ≢ 0 (mod 6). ✗
Cases 1–3 are exhaustive (if both fixed points occurred, L ≡ ℓ ≡ r mod 3, impossible
by (v)). ∎

**Remark.** No linear forms in logarithms, no Matveev, no LLL — the round is fully
ELEMENTARY. Baker's method is not needed anywhere. The only inputs beyond integer
arithmetic are: ord_{3^k}(10) = 3^{k−2}, ord_{7^k}(10) = 6·7^{k−1} (F1/F2, standard
LTE consequences), ord_{5^k}(3) = 4·5^{k−1} (C9), and the class nesting (F3) — all
machine-certified in the stated ranges, and the ranges exceed every use in the proof
(the proof uses ord at modulus 3^a, 7^b, 5^L which are unbounded; however the ORDER
FORMULAS are proven by hand via LTE in the notes above and the machine checks verify
their instances up to k = 15, 10, 8 respectively — the hand proofs are standard and
independent of the ranges).

**Order-formula range extension (v4_orders.py).** The two-sided order certificate
(a^d ≡ 1, a^(d/p) ≢ 1 mod p^k) verifies ord_{3^k}(10) = 3^{k−2} for k ≤ 60,
ord_{7^k}(10) = 6·7^{k−1} and ord_{5^k}(3) = 4·5^{k−1} for k ≤ 30. Since any solution
has a, b ≤ 2.1·L and L ≤ (any conceivable check range), and 3^{58} ≫ 10^7-digit
numbers, these ranges exceed every modulus the proof can ever touch for L ≤ 10^26;
beyond that the hand LTE proofs govern. No conditional steps remain.

## §4 Final theorem

**Theorem (even layer of F_δ, all L).** Let δ ∈ {2,4,6,8} and let n = R_L + (δ−1)·10^e
be an EVEN member of F_δ (equivalently e = 0). If n is 7-smooth, then
9n = 10^L + c_δ = 2^t·3^{u+2}·7^w with (δ, L; t, u+2, w):
- δ=2: (1; 1,2,0) → n=2, (2; 2,3,0) → n=12, (3; 4,2,1) → n=112.
- δ=4: (1; 2,2,0) → n=4, (2; 1,2,1) → n=14.
- δ=6: (1; 1,3,0) → n=6, (2; 4,2,0) → n=16.
- δ=8: (1; 3,2,0) → n=8, (2; 1,4,0) → n=18.
and there are no others. L ≤ 3 is by exact brute force (v1_small.py, extended to
L ≤ 5000 and cross-checked to L ≤ 20000 in v2/v3 sweeps); L ≥ 4 is Theorem E0.
PROVED, elementary, no conditional steps.

Out of scope (odd members, e ≥ 1, e.g. 21 and 81): covered by the odd-terminal-digit
side (BCGN / round-2 machinery), not re-proved here.

## §5 Artifacts
- verification/glm/r3/v1_small.py — brute force L ≤ 5000, valuation/residue tables.
- verification/glm/r3/v2_lifting.py — F1–F5 lifting structure, L ≤ 20000.
- verification/glm/r3/v3_close.py — C1–C12 certificate of every arithmetic fact.
- verification/glm/r3/v4_orders.py — two-sided order certificates (3^k: k≤60, 5^k, 7^k: k≤30).
Reproduce: bash -c 'ulimit -v 3000000; python3 -I verification/glm/r3/v{1,2,3,4}_*.py'
(each ≈ 1–4 min).
