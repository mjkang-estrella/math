# Independent verification of notes/pure_math.md (2026-10-19)

Fresh scripts in this directory. They share no code with `src/`.

| Script | Checks |
|---|---|
| `v1_basic.py` | Thm A, τ-table, Π(τ_k)=τ_{k−1}, Cor B′ (max Π by length), level table, AM–GM numbers, Zsigmondy remark, Thm D counts, Thm F arithmetic |
| `v2_minlex.py` | Thm C.2 closed form vs. an additive-lexicographic DP (a≤240, b≤160); Thm C reproduces OEIS A003001 a(3..11) |
| `v3_v2fam.py` | sup v₂ over 1-insertion families (right-to-left 2-adic DFS) |
| `v4_allfam.py` | sup v₂ over all digit-factorization families of the two Front(10) targets (node-capped) |
| `v5_sweep.py`, `v6_sweep_par.py` | direct sweep of all 7-smooth m with a·c=0 (v5 double-counts 3^b7^d in its histogram; v6 is correct) |

## Confirmed
- **Thm A.** Correct.
- **Thm B.** The τ₁…τ₁₀ table is exact: 18,051 7-smooth numbers ≤ τ₁₀, and P = 10 is reached only at τ₁₀. Π(τ_k) = τ_{k−1} holds for k = 6…10 (and trivially for k = 2).
- **Cor B′ (dc(m₀) ≥ 17).** Every max-Π value the doc lists is reproduced, and D = 17 is the first length where max Π ≥ τ₁₀. The level table (17, 13, 9, 7, 6, 5, 4, 3, 2, 2, 2) is reproduced.
- **(B2) AM–GM.** 94.94 and 60.08 are reproduced. The digit-sum claim also holds: the AM–GM floor at D = 14 is 113.02, and the max digit sum of a 7-smooth number with dc ≤ 14 is 90.
- **Zsigmondy remark.** Correct.
- **Thm C.** The closed form matches the DP on all 38,800 nonzero pairs, rebuilds 277777788888899, and reproduces A003001 a(3..11) exactly.
- **D=525 sweep / Front(10).** Re-run independently over 285,339,516 points in 22 s: exactly two numbers with P = 10, none with P ≥ 11.
- **Fonga {4,4,7}.** sup v₂ = 7 at 111744. The member count for j ≤ 40 is 407,253.
- **{2,6} family.** sup v₂ = 6 at 1216.
- **Record family {2,7⁶,8⁶,9²}.** sup v₂ = 64, witnessed by a 53-digit member with 38 ones.
- **Weak value-test counts.** 157 (D=14) and 4,628 (D=15) reproduced.
- **Extension 3 equation.** The algebra is correct.

## Errors found
1. **Thm D counts are wrong.** 2¹⁹3⁴7⁶ has **317** digit-multiset factorizations, not 120. 2⁴3²⁰7⁵ has **112**, not 44. The total is **429, not 164**. Two methods agree. The finiteness argument survives; every "164" in pure_math.md and README.md is wrong.
2. **Cor F′ is false as stated.** "Any 7-smooth preimage of 4996238671872 has A ≤ 64" was derived from one family out of 317. The family {6⁴,7⁶,8⁵}, which is also a minimal 15-digit factorization, has sup v₂ = **67**:
   `86111711711116111711117811111111811711117186111111168`
   This number has digit product 2¹⁹3⁴7⁶ and v₂ = 67. For the second target, the family {3²⁰,4²,7⁵} reaches v₂ = 86. Separately, the claim "bounded 3-dimensional search" is wrong: B and D grow without bound as j → ∞, so a v₂ bound alone does not make the search finite.
3. **Thm F constants.** γ¹⁰ = 0.6260 (the doc has 0.6277). The additive term is 8.17 (the doc has 8.8). The exact thresholds are D ≤ **550** for one step (the doc has 549, and ⌊γ·549⌋+1 = 524, not 525) and D ≤ **833** for ten steps (the doc has 822). The errors are conservative and harmless.
4. **Minor slips.** "dc decreases strictly" is only true for dc ≥ 22 (99 → 81); the argument only needs non-increasing. §5 says 38,880 pairs; the correct number is 241·161 = 38,801. Extension 3 gives 6.84×10¹³ arrangements at j = 6; the correct number is 6.84×10¹⁰. (B1) uses τ₁₁ at i = 0, which is undefined.

## Framing issue
Thm F says the band 526 ≤ dc(m₀) ≤ 822 is "open, reducing to family decisions". It is already closed:
- The sweep `v6_sweep_par.py 1000` covers it directly: 1,968,364,785 points in 479 s, P = 10 only at the same two numbers, max P = 10, no P ≥ 11 for any dc ≤ 1000 (see `sweep_1000.log`).
- Published bounds cover it too. A P ≥ 11 smooth m has a minimal preimage of length ≤ dc(m)/log₁₀5 + 2. So Perez–Styer's a(12) > 10¹⁵⁰⁰ already excludes dc(m) ≤ ~1047, and Peters' 2.67×10³⁰⁰⁰⁰ excludes dc(m) ≤ ~20,000.

## Bottom line
The conjecture is **not** proved, and the document does not claim it is. The rigorous content (Thms A, B, B′, C, the Zsigmondy remark, the sweep, the Fonga example) checks out. The conditional reduction in Thms D–F is logically sound, but its headline numbers (164 multisets, the A ≤ 64 bound) are wrong, and the "open band" it targets is already settled computationally.

## Audit of the GLM 5.3 Flash proof attempt (notes/proof_attempt_glm.md, round 2)
- **Theorem E is false as stated.** Equation (★δ) drops the prime 5, so F₅ was tested against 3^U·7^W only. Brute force (`v7_check_glm_table.py 150`) finds two 7-smooth members: **5 and 15** (= 3·5; 35 → 15 → 5).
  - The corrected statement is PROVED (`v8_delta5.py`): F₅'s 7-smooth members are exactly {5, 15}. For e ≥ 1, n ends in 1, so 5 ∤ n, and the mod-M₀ certificate gives 0/144 hits. For e = 0, 9n = 5·(2^L·5^{L−1}+7), w = 0 mod 7, and 2^L·5^{L−1}+7 ≡ 7 (mod 8) ≠ 3^k for L ≥ 3.
  - BCGN already cover odd terminal digits, so this is a re-derivation, not new.
- **Table 1 (δ ≠ 5)** agrees with brute force over all 7-smooth n < 10^150. The 10^7-digit claim (Theorem P/R) was not re-checked independently.
- **Lemmas 1–2** are correct and elementary: n even ⟹ the last digit is δ ⟹ e = 0.
- **Scope.** This covers only the single-digit-preimage layer with one non-1 digit, bounded in length except for δ ∈ {1, 5}. It does not touch the open core (zero digits / arbitrary length).

## Audit of GLM round 3b (notes/proof_attempt_glm_r3.md): even layer of F_δ, all L
- **The theorem is CORRECT and PROVED (elementary).** For δ ∈ {2,4,6,8} with e = 0, the only 7-smooth n are 2, 12, 112, 4, 14, 6, 16, 8, 18. Every step was checked by hand. Round 3 itself (max thinking) produced no output; round 3b did.
- **Shorter independent certificate** (`v9_even_layer.py`). For L ≥ 4:
  - 27 ∣ 10^L+c and 7 ∣ 10^L+c need incompatible L mod 3, so b = 0 or a = 2.
  - b = 0: mod 5 fixes a mod 4, then mod 64 forces v₂(3^a − c″) = 1, so L ≤ 3. For δ = 2, use ord_{5^L}(3) = 4·5^{L−1} > a instead.
  - a = 2: mod 5 fixes b mod 4, and mod 64 fixes L ∈ {2, 3, 6}. Each of these is killed by L ≥ 4 or the L mod 6 condition.
  - The lifting and size lemmas in the write-up are correct but unnecessary.
- **Still open in the single-digit layer:** the odd members (e ≥ 1, and all e for odd δ) beyond 10⁷ digits.

## Audit of GLM round 4 (notes/proof_attempt_glm_r4.md): odd layer, all L
- **The theorem is CORRECT after one fix.** Every congruence in Steps 0–3 was checked by hand.
- **The fix:** Step 2 for δ ∈ {4,8} silently assumed a = 2. The repair (`v10_odd_fix.py`): the 27- and 7-classes of L are incompatible (F10), so a = 2 or b = 0. Then 9·7^b mod 8 ∈ {1,7} and 3^a mod 8 ∈ {1,3}, and neither reaches 5.
- **Single-digit layer COMPLETE (PROVED, all L).** The 7-smooth n of the form (1s + at most one digit δ) are exactly 1; 2, 12, 21, 112; 3; 4, 14; 5, 15; 6, 16; 7; 8, 18, 81; 9. Proved by rounds 3b and 4 plus v8–v10, and independently brute-forced to L ≤ 400 for all e.
- **What this does NOT cover:**
  - preimages of δ with ≥ 2 non-1 digits ({2,2}, {2,3}, {2,4}, {2,2,2}, {3,3});
  - all higher levels of the backward tree;
  - chains ending in 0, which is the actual open core and includes the record chain.

## Audit of GLM round 5 (notes/proof_attempt_glm_r5.md): Level 1, ≥ 2 non-1 digits
- **Member list confirmed** by independent brute force (pairs to L ≤ 250, triples to L ≤ 80):
  - {2,3}: 32, 111132 = 2²3⁴7³
  - {2,4}: 24, 42, 14112 = 2⁵3²7²
  - {2,2}, {3,3}, {2,2,2}: none
- **Status: COMPUTED for L ≤ 6000 only.** The child's filter was not re-run by the parent. Completeness for L > 6000 is OPEN.
- **Parent observation (easy, all L).** If every non-1 digit sits at position ≥ 3, then 9n ≡ −1 (mod 8) and (mod 5). Mod 8 forces opposite parity of (a, b) and mod 5 forces equal parity, so there is no solution. The genuine residue is therefore configurations with a non-1 digit at position ≤ 2:
  - "all-low" configurations: 3-term 10^L + K = 2^t3^u7^w, the same shape as round 3b;
  - "mixed" configurations: one low digit and another digit at a free position q, giving the 4-term 10^L + A·10^q + K. This is effective via two-step Baker, but not elementary so far.

## Audit of GLM round 6 (notes/proof_attempt_glm_r6.md): closing Level 1
- **(H) PROVED, all L.** Every non-1 digit at position ≥ 3 gives 9n ≡ 7 (mod 8), which forces (u even, w odd), and n ≡ 1 (mod 5), which forces w ≡ u (mod 4). The two contradict. Checked by hand.
- **(A) all-low (19 constants K): ACCEPTED, pending an independent certificate.** Result: members are exactly 32, 111132, 24, 42.
  - The parent reviewed the sieve logic (`a_range`/`w_range` exactness, the cyclic-group subgroup test, the T ≡ 0 kill, the both-exact size resolution) and found it sound.
  - The parent re-ran `v4_stage2.py`: it closed K=188 and K=278 in 30 s.
  - The parent's own independent sieve (`v11_cover_sieve.py`) did not converge (search-order problem), so this is NOT independently reproduced.
- **(M) mixed: partially proved.** The parity kills for S_low ∈ {2, 3, 20, 100, 200, 300} were checked by hand; this includes every {3,3} configuration. The residual (M*) is OPEN: 3^a7^w = 2^{L−t₀}5^L + A·2^{q−t₀}5^q + c₀ for S_low ∈ {1, 10, 30, 11, 101, 110}, plus the {2,2,2} two-far variant. Its known solution gives 14112.

## Audit of GLM round 7 (notes/proof_attempt_glm_r7.md)
- **K = 188 and K = 278 are INDEPENDENTLY CERTIFIED for all L.** The parent wrote its own checker, `v12_check_cert.py`, sharing no code with the child. It recomputes every 3-adic and 7-adic signature from scratch, re-tests every kill, and verifies that the tree covers every L ≥ 0 (for kill primes with ord_q(10) ∤ M, every lift mod lcm is checked).
  - K = 188: 31 leaves, 1431 rest-lifts, 0 mismatches. The only solution with L > t₀ = 2 is L = 6 (111132); L ≤ 3000 is brute-forced (L = 2 gives 32).
  - K = 278: 11 leaves, 603 rest-lifts. The only solution is L = 2 (42).
- **Not yet independently certified:**
  - the other 17 all-low constants, which round 6 says closed at stage 1;
  - the one-far mixed (M*) closure, whose only member is claimed to be 14112;
  - the two-far {2,2,2} closed parts.
- **Two-far {2,2,2}, S_low = 1 (K = 8): OPEN.** A residual of 9 classes mod 2·3⁷·7⁵ remains, which forces q₁ ≥ 672192. They sit on both the 3-adic and 7-adic ladders, so elementary sieving cannot kill them; a Baker-type bound is needed.

## Audit of GLM round 8 (notes/proof_attempt_glm_r8.md): Level 1 certified
- **All 21 one-dimensional certificates are VALID under the parent's independent checker `v12_check_cert.py`.** They cover the 19 all-low constants plus the mixed q=3 slices K = 9008, 18008, 27008, 99008. No solutions exist with L > t₀ beyond the known ones; small L are brute-forced to 3000.
- **p = 37 kill (closes round 7's 9 residual classes): verified by the parent.** ord₃₇(10) = 3. ⟨3,7⟩ mod 37 is exactly the 18 quadratic residues. The 9 classes have T ≡ 19 or 13 (mod 37), both non-residues, so they die for every (a, w). Round 7's "OPEN" status came from a scan bug that skipped primes with ord_p(10) | M.
- **Checked only by child-written checkers:**
  - the 2-D one-far certificates (`check_cert2d.py`, written fresh, tamper tests pass);
  - the two-far {2,2,2} closure outside the 9 classes (3-D sieve plus `check_cert3d.py` on the 9-leaf certificate).
  The parent has not written its own 2-D/3-D checker.
- **LEVEL 1 STATUS: closed for all L.** The 7-smooth numbers with digit product a single digit are exactly:
  - one non-1 digit: 1; 2, 12, 21, 112; 3; 4, 14; 5, 15; 6, 16; 7; 8, 18, 81; 9;
  - two or more non-1 digits: 32, 111132 ({2,3}); 24, 42, 14112 ({2,4}).
  Proofs: elementary (rounds 3b, 4, and 6(H)) plus certificates (rounds 7–8). The only caveat is the 2-D/3-D pieces checked by child-written code.
- **What this means for the conjecture.** It settles the first backward level for chains ending in a nonzero digit only (BCGN's even-digit program, level 1). The conjecture remains OPEN. Two things are still missing: (i) the higher backward levels, and (ii) chains ending in 0, which include the record chain 277777788888899 → … → 0 and are the actual open core.

## Independent audit A (Claude Sonnet 5.5; verification/indep/REPORT_A.md)
- **Real defects found in GLM's round-8 2-D certificates:**
  - (S_low=30, A=9, K=269), i.e. {2,4} with the 4 at position 1, had NO certificate. The file `cert2d_S30_A27` is a {4,4} case and was mislabeled.
  - GLM's `pin_kill` divides by 2^{t₀} twice. As a result `cert2d_S11_A9` contains 4 invalid pin kills. Counterexample to the kill: 2·3¹⁰ = 118098 ≡ 98 (mod 1000). The K=98 statement itself is still TRUE (closed independently).
- **Independent re-certification:** A wrote its own generator and checker (`gen_nd.py`, `checknd.py`, 1-D/2-D/3-D), sharing no code with GLM. Every Level-1 configuration class is covered:
  - (H) and parity kills;
  - all 19+4 one-dimensional constants;
  - all 10 one-far pairs, including the missing 30/9;
  - two-far {2,2,2} for K = 8 and 89 (3-D), plus the q₁ = 3 slices.
  Validation: tamper tests rejected, positive controls recorded, a randomized soundness test, and a digit-level brute force over 12.3M candidates. The parent re-ran `run_all.sh` (40 s): 0 uncovered classes, and the brute force finds only 24, 32, 42, 14112, 111132.
- **LEVEL 1 IS NOW INDEPENDENTLY CERTIFIED for all L.** Every piece has ≥ 2 independent authors: GLM + Agent A, and the parent's own checker for the 1-D certificates.
- **Ground truth for the next levels** (`v13_backward_tree.py 300`): every 7-smooth n < 10^300 whose chain ends in a nonzero digit.
  - Counts by level 1–7: 13, 32, 57, 60, 17, 4, 1. The largest member has 16 digits.
  - Level 2 (32 members): 27 28 35 36 48 63 64 72 84 126 128 135 144 162 192 216 224 243 315 324 432 441 1134 1176 1323 1372 1728 2187 4116 13122 131712 33718272.

## Agent C (GLM; notes/L2_large_glm.md): general pipeline + Level 2 large targets
- **Pipeline:** `verification/glm/L2c/pipeline.py`. Configurations are enumerated programmatically; parity kills use mod 40; slices have constant v₂. There is no pin logic (this avoids the pin bug). Certificates are emitted in Agent A's nd format.
  - Its Level-1 re-derivation reproduces the ground truth with 0 coverage gaps.
  - All 464 certificates pass Agent A's independent `checknd.py`. The parent re-checked a random sample of 60: 60/60 pass.
- **Level-2 members** agree with the parent's v13 sweep (≤ 300 digits):
  - Π = 112: 1728, 2187
  - Π = 14112: 33718272
  - Π = 111132: none
- **Status:** configurations with ≤ 3 free far positions are PROVED for all L. Configurations with ≥ 4 free far positions are COMPUTED to L ≤ 300 only, OPEN beyond:
  - 112: 12 open configurations
  - 14112: 871 open
  - 111132: 332 open
  The obstruction: the 3-adic ladder family has dimension ≥ 3, and the class count explodes before the killing primes (ord ∋ 3⁷) align.
- **Ground-truth Level 2 grouped by Π** (for auditing B):

  | Π | members |
  |---|---|
  | 12 | 126, 162, 216, 1134, 13122 |
  | 14 | 27, 72 |
  | 15 | 35, 135, 315 |
  | 16 | 28, 128, 144, 224, 441 |
  | 18 | 36, 63, 192, 1323 |
  | 24 | 64, 243, 324, 432, 4116 |
  | 32 | 48, 84 |
  | 42 | 1176, 1372, 131712 |

## Agent B (GLM, resumed; notes/L2_small_glm.md): Level 2 small targets
- **Members match ground truth on all 10 targets.** Coverage replay found no gaps.
- **PROVED for all L:** t = 12, 14, 15, 18, 21, 42, 81.
  - t = 21 and t = 81 have no members at any length, by the mod-40 parity test alone. The parent verified this independently: n mod 8 is fixed by the last 3 digits and n mod 5 by the last digit, and no 7-smooth residue mod 40 matches. L ≤ 2 is brute-forced.
- **Partly open:** t = 16 (2 open configurations), 24 (2), 32 (8). All 12 are dim-4/5 slices (≥ 3 free far digits), verified by brute force only to L ≤ 300.
- **Certificates:**
  - 272 pass Agent A's unmodified `checknd.py`; the parent re-checked a random sample of 60/60.
  - 3 certificates for t = 15 use B's "five-mode" extension, `checknd5.py`, which is not independent. The parent reviewed the diff and found it sound: when 5 is the last digit, n ends in 15 or 35, so v₅(n) = 1, X = 5·2^{t₀}3^a7^w, and the five flag is tied to 5 | K.
- **Level 2 open total:** B 12 + C (112: 12, 14112: 871, 111132: 332). These are being attacked by Agent D (new high-dimensional method) and audited for coverage by Agent E.

## Agent E (Claude Sonnet 5.5; verification/indep2/REPORT_E.md): coverage audit of C's Level-2 targets
- **REAL COVERAGE HOLE found.** A 2-D `checknd` certificate covers 10^L + c₁10^{q₁} + c₂10^{q₂} + K only with L > q₂ > q₁, i.e. c₁ is the LOWER far digit. When c₁ ≠ c₂, C certified only one ordering, yet labeled the configuration PROVED. 39 configurations were affected: 16 for t=112 and 23 for t=14112.
- **Repaired:** E generated the 39 reversed-order certificates. The parent re-checked them all: 39/39 pass `checknd`, and the swapped-coefficient tamper test correctly FAILS.
- **Coverage after repair** (configurations: total / parity-dead / open / uncovered):

  | target | total | parity-dead | open | uncovered |
  |---|---|---|---|---|
  | 112 | 116 | 49 | 12 | 0 |
  | 14112 | 1640 | 737 | 871 | 0 |
  | 111132 | 806 | 474 | 332 | 0 |

  For 14112, the 871 open = 870 with ≥ 3 far digits, plus S387 {54,54}. The S387 reversed slice (K=3482) had no certificate at report time.
- **Other checks:**
  - E's independent enumeration matches C's exactly.
  - All parity kills are sound, and none were missed.
  - Brute force over 298M lattice points < 10^600 matches C's member lists.
- **The same one-order-only pattern occurs in 20 certificates for t = 12, 16, 24, 32, 42**, i.e. Agent B's targets. B's PROVED labels for 12, 42 (and any other target with mixed two-far configurations) are therefore SUSPENDED pending an audit (Agent E2).

## Agent E2 (Claude Sonnet 5.5; verification/indep3/REPORT_E2.md): coverage audit of B's targets
- **The same ordering hole was found in B's targets:** 20 configurations certified in one order only (t = 12: 2, 16: 2, 24: 8, 32: 6, 42: 2). All 20 were repaired. The parent re-checked the 20 reversed-order certificates: 20/20 pass the unmodified `checknd`.
- **Other checks:**
  - E2's enumeration equals B's on all 10 targets.
  - Parity kills are sound.
  - All 275 of B's certificates pass.
  - The five-mode math for t = 15 was independently confirmed.
  - Brute force to 10^600 matches the ground truth.
- **S387 (t = 14112, {54,54}, K = 3482) is now PROVED.** It needs a new leaf kind, "pin2". The parent reviewed the 8-line checker addition and found it sound: with qmin ≥ t₀+3, X ≡ K (mod 2^{t₀+3}) on the whole domain, so v₂(X) = t₀ and 3^a7^w ≡ K/2^{t₀} (mod 8), and the signature-allowed residues are checked. Both certificates (K3482 dim 3, K57482 dim 2) pass `chk_pin2.py`, as re-run by the parent. The resisting classes surround the phantom solution 10⁶ + 54·10³ + 54·10² + 3482 = 2·3¹², which has a far digit at position 2, outside the domain.
- **LEVEL 2 STATUS (after the E/E2 repairs):**
  - PROVED for all L: t = 12, 14, 15, 18, 21, 42, 81.
  - Partially open: t = 16 (2 open), 24 (2), 32 (8), 112 (12), 14112 (870), 111132 (332).
  - Every open configuration has ≥ 3 free far digits (slice dim ≥ 4) and is brute-force verified to 10^300 (E/E2: to 10^600).
  - All configurations with ≤ 2 far digits are certified.

## High-dimensional residuals (Agent D = session "math-8b", Claude Opus; continued by Codex GPT-6.1-Sol)
- **Method** (`verification/highdim/gen_hd.py`):
  - Breadth-first refinement along a modulus schedule rich in small divisors. This kills the "double-ladder" classes (a and w both unbounded) with ⟨3,7⟩-coset tests at primes with ord_p(10) | M, before any deep 3-adic refinement.
  - An "unordered" domain mode (far positions pairwise distinct, any order) covers every ordering at once.
  - Only plain prime kills are used.
- **Parent's independent checker `verification/v14_checknd_hd.py`.** It is Agent A's `checknd.py` with three marked changes:
  - any dimension;
  - ordered/unordered domain enumeration for the size leaves and the brute box;
  - memoized order/isprime. This does not change the arithmetic.
  Its tree and kill logic is otherwise untouched. Soundness of the unordered domain: every kill is a congruence test independent of ordering. Only the domain constraint and the solution enumeration depend on ordering, and the patch handles both.
- **t = 112: all 12 open configurations CLOSED.** That is 120 certificates:
  - 106 (dim ≤ 3) pass the UNMODIFIED `checknd.py`, as re-run by the parent;
  - of the 14 dim-4/5 certificates, 12 pass v14 as re-run by the parent; the 2 dim-5 ones ({9,9,9,54}) were still running at the time of writing.
- **Codex continuation** (`verification/highdim/codex/REPORT.md`):
  - t = 16: 2/2 closed; t = 24: 2/2 closed; t = 32: 6 of 8 closed;
  - t = 14112: 205 of 870 closed, with 665 at BUDGET (an incomplete search; that is NOT a nonexistence proof).
  - 2807 certificates passed checkhd plus v14, but through Codex's `checker_entry.py` wrapper, which memoizes builtin `pow`. The parent re-ran a random sample of 48 directly under v14 with no wrapper: 48/48 PASS.
- **LEVEL 2 STATUS:**
  - PROVED for all L: t = 12, 14, 15, 16, 18, 21, 24, 42, 81, and 112 (pending the 2 dim-5 checks).
  - Open: t = 32 (2: `10|9,9,9,9` and `11|9,9,9`), t = 14112 (665), t = 111132 (being worked on by the math-8b session in highdim/hd2/; its kmax ≤ 3 subset is 17/18 closed).
- **Update:** all 14 dim-4/5 certificates for t=112 PASS v14 (parent re-run), including both dim-5 {9,9,9,54} certificates. Every one of the 120 t=112 certificates is therefore validated by parent- or A-authored checkers. The remaining single-author link is the configuration→slice→certificate COVERAGE map for the high-dim work (D's `coverage.py`). An independent coverage audit (E-style) of all high-dim closures is planned once the Codex runs (codex3a/3b) finish.
- **codex3b (odd half of the 14112 BUDGET list): 7/332 closed.** The parent re-ran all 7 certificates under v14: 7/7 PASS.
- **SCALING WALL:** the 175 configurations of dimension 6–8 need 10^8–10^11 lifts at the next refinement level. The covering sieve grows like M^{k+1} in the number k of far digits.
- Method agent M (Codex, verification/highdim/sym/) is developing multiset ("symmetric") compression for repeated far coefficients, with a fresh checker.
- **codex3a (even half + t=32):** 7 closed: t=32 `10|9,9,9,9`, plus 6 for t=14112. The parent re-ran v14 on 3 of them (PASS); the remaining 4 are being re-checked. t=32 `11|9,9,9` is still open.
- **Method M (nd-sym, verification/highdim/sym/):** multiset refinement for repeated far coefficients, sumset kills, and decimal-tail coset kills. 121 dim-6/7 target-14112 configurations closed (dim 6: 89/221, dim 7: 32/90, dim 8: 0/20).
  - Validated so far ONLY by M's own `check_sym.py`, a same-agent checker. These closures are NOT ACCEPTED until the independent audit F (Claude Sonnet, verification/indep4/) confirms the soundness of the new kill types and the coverage.
  - M2 (Codex) is applying nd-sym to all remaining open 14112 configurations.
- **Update:** all 7 codex3a certificates PASS v14 (parent re-run). t=32 is down to 1 open configuration (`11|9,9,9`). Confirmed t=14112 closures by legacy-format certificates: 205 (codex) + 7 (codex3b) + 6 (codex3a) = 218 of the 870 hard configurations, plus S387.
- **M2 (nd-sym applied to all remaining t=14112 configurations):** 398 more closed, 133 still open. By number of far digits (closed/open): 4: 8/0, 5: 298/13, 6: 85/47, 7: 7/51, 8: 0/20, 9: 0/2. t=32 `11|9,9,9` is still open.
  - 54,777 PASS verdicts from the same-agent `check_sym.py`.
  - Kill-type dependence: decimal-tail coset 54,762; mod-8 45,670; sumset 1,415; prime-coset 54,764.
  - **t=14112 tally:** 218 confirmed (legacy format) + S387, plus 121 + 398 = 519 nd-sym closures PROVISIONAL pending audit F, with 133 open.
  - If F finds any of the decimal-tail / mod-8 / sumset kills unsound, nearly all nd-sym closures fall.

## Audit F (Claude Sonnet 5.5; verification/indep4/REPORT_F.md): nd-sym soundness
- **All nd-sym kill types are SOUND:**
  - multiset lifts;
  - aligned prime kill;
  - sumset kill (condition: the sumset is taken over all q mod d compatible with the class mod gcd(d, M));
  - mod-8 pin2 (condition: qmin ≥ t₀+3);
  - decimal-tail coset (conditions: k ≤ min(3, qmin), and divide by 2^{t₀} once);
  - size leaves.
  F wrote its own proofs and its own checker (`check_sym_F.py`) BEFORE reading M's code.
- **121/121 M closures confirmed** by F's checker, plus an independent coverage map (F's own enumeration of the 1640 configurations equals E's).
- **Agreement and tamper tests:** 59,978 differential tests between M's and F's kill procedures, 0 disagreements. 30 tamper files rejected, including an over-wide tail pin, a single-representative sumset, and multiset corruptions.
- **M2 sample:** F's checker on a random sample of 486 sym2 certificates, across all 5 certificate directories: **486/486 PASS** (the parent tallied F's output after F was cut off by an API rate limit). The coverage check of a 62-configuration sym2 sample (12,785 certificates) is being run by the parent with F's checker.
- **t=111132 (math-8b session, highdim/hd2/):** 122/332 configurations closed (≤ 4 free far digits per slice); 210 open (k = 5..8, not attempted).
  - 5876 certificates: checkhd 5876/5876, and the unmodified checknd 5648/5648 (ordered).
  - The 228 unordered dim ≥ 4 certificates are not yet independently checked.
- **Audit F, final:** 121/121 M closures fully confirmed: certificates, coverage, and soundness proofs.
  - sym2 tail/mod-8 metadata conditions were checked on ALL 54,764 full-scope certificates: 0 violations (t₀ up to 31, qmin up to 34).
  - A mutation test shows the wrong 2^{t₀} handling would wrongly kill planted true solutions, while the correct modulus never does.
  - sym2 sample: 487/487 certificates PASS; coverage of 63 configurations (≈ 13,600 certificates, including `161|18,18,54,63`, which contains the member 33718272) all PASS.
  - The remaining 335 sym2 closures rest on the sample plus the soundness proofs. A full replay (~43,689 certificates, ≈ 24 CPU-hours) is being run by the parent at low priority.
- **M4 (sym4):** 39 of 134 remaining configurations closed (t=14112, by k = 1 + #far digits: k=5 4/9, k=6 16/31, k=7 18/33, k=8 1/19, k=9 0/2); t=32 `11|9,9,9` still open.
  - 15,442 certificates pass BOTH `check_sym.py` and F's independent `check_sym_F.py`. The parent re-checked a random 40 with F's checker: 40/40.
  - The coverage audit covers all 12,795 orderings.
  - Proposed checker extension (NOT used): `pin_digits > 3` up to qmin.
  - **t=14112 tally:** 776 of 870 closed, + S387; 94 open.
- **M5 (sym5, deep decimal-tail pins with 3 < k ≤ qmin):** 62 of 95 closed, including t=32 `11|9,9,9`. t=14112 by dimension: 5: 9/0, 6: 30/1, 7: 21/12, 8: 1/18, 9: 0/2. 33 open.
  - 61 of the closures rely on k > 3, so they are PENDING the independent F5 checker (GLM, verification/indep5/).
  - Certificates with k ≤ 3 pass the unmodified F checker (10,822).
- **FULL sym2 replay (parent, F's independent `check_sym_F.py`): 54,762/54,762 certificates PASS.** Every sym2 certificate is now independently verified. Coverage of the 398 sym2 configurations was independently mapped on F's 63-configuration sample. Full coverage rests on M2's `audit_coverage.py` plus that sample.
- **t=14112 tally:** 837 of 870 closed + S387 (the 61 sym5 closures pending F5); 33 open (by dimension: 6: 1, 7: 12, 8: 18, 9: 2).
- **t=32:** closed (pending F5 for the deep-pin certificate).
- **M3 (sym3, t=111132):** 150 of 210 closed; by k: 5: 122/124, 6: 26/66, 7: 2/18, 8: 0/2.
  - 18,734 certificates pass BOTH `check_sym.py` and F's independent `check_sym_F.py`. The parent re-checked a random 40 with F's checker: 40/40.
  - Coverage audit OK, including all 10,160 orderings.
  - **t=111132 tally:** 272 of 332 closed; 60 open.
- **M6 (sym6, deep pins, t=111132):** 53 of 60 closed (k=5: 2/2, 6: 38/40, 7: 13/16, 8: 0/2); 7 open. ALL 53 need deep pins, so they are PENDING F5.
  - **t=111132 tally:** 272 closed (independently checked) + 53 pending F5; 7 open.

## F5 (GLM; verification/indep5/NOTE_F5.md): independent deep-pin checker
- **Checker:** `check_sym_F5.py` = F's checker plus deep pins with 1 ≤ k ≤ qmin. The changes are marked "# [F5]". It uses a structured pin solver: Pohlig–Hellman discrete logs mod 5^k, and an exact rank-2 lattice coset for the admissible exponents.
- **Tests:**
  - 24,003-case differential test against the base checker: 0 mismatches.
  - Regression on 50 random existing certificates: identical verdicts.
  - Tamper: pin > qmin rejected; planted smooth points are rejected, while a forgot-to-divide checker wrongly accepts them.
  - Positive controls pass.
- F5 corrected a slip in the parent's brief: ord_{5^k}(7) = 4·5^{max(k−2,0)}, since 7⁴ ≡ 1 (mod 25). Nothing depended on it.
- **sym5 deep-pin certificates: 12,262/12,262 PASS** (9 needed > 6 GiB due to pre-existing sumset code; they PASS at 30 GiB).
- **⇒ t=32 is CLOSED** (fully independently checked), and **the 61 sym5 t=14112 closures are CONFIRMED.**
- The sym6 deep-pin certificates (24,014, for the 53 t=111132 closures) are being replayed with F5 by the parent (verification/indep_F5_sym6/).
- **LEVEL 2 STATUS:**
  - PROVED for all L: t = 12, 14, 15, 16, 18, 21, 24, 32, 42, 81, 112.
  - t=14112: 837/870 + S387 closed; 33 open.
  - t=111132: 272 confirmed + 53 pending the F5 replay; 7 open.
- **M7a (position peeling + deep pins, t=14112's last 33):** 1 closed (dim 6). Dims 7–9 (32 configurations) remain OPEN. 2,041 certificates pass both check_sym5 and F5. Coverage audit (including the peeling splits) PASS.
  - **t=14112 tally:** 838/870 + S387; 32 open (dim 7: 12, 8: 18, 9: 2).
- **F5 replay of sym6 deep-pin certificates (parent):** 24,012/24,014 PASS. The other 2 are not rejections: one hit MemoryError at 30 GB, one timed out at 2 h. Both are being retried at a 70 GB / 5 h cap.
- **M7b (position peeling, t=111132's last 7):** 1 closed (k=6). 6 open (k=6: 1, k=7: 3, k=8: 2). 2,042 certificates pass both check_sym5 and F5.
  - The sym6 certificate `pin6_180/K89_q6_c9_18_18_54_54_54_72` exhausted F5 at 30 GB, and M7b withdrew it from its own covers.
  - That certificate and `pin6_180/K8_q6_c18_18_18_45_54_54_54` are being retried by the parent at 70 GB. The M6 closures that depend on them stay PROVISIONAL until those retries pass.
- **LEVEL 2 STATUS (end of this push):**
  - PROVED for all L: t = 12, 14, 15, 16, 18, 21, 24, 32, 42, 81, 112.
  - t=14112: 838/870 hard configurations + S387 closed; 32 OPEN (dims 7–9).
  - t=111132: 326/332 closed (≤ 2 of these provisional on the 70 GB retries); 6 OPEN (k = 6–8).
  - The 38 open configurations have resisted every method tried: the legacy sieve, nd-sym, the hybrid, deep pins, and position peeling. All are brute-force verified to ≥ 10^300 (E/E2: 10^600).

## Push 8 (parent): re-examining the 38 open Level-2 configurations
- **70 GB retry:** `pin6_180/K8_q6_c18_18_18_45_54_54_54` **PASS** under F5 (58.1M refinements, 173 leaves, 0 problems). `pin6_180/K89_q6_c9_18_18_54_54_54_72` still running (RSS 42 GB after 24 min).
- **Budget finding (COMPUTED):** the sym7a search spent 2,858 worker-seconds on 33 configurations (~87 s each); sym7b similar. Of the unresolved peeling states, hundreds are dimension 1–6 and failed only on "configuration wall budget". The genuinely hard leaves are dim 7 (188 states at floor 7), dim 8 (32) and dim 9 (2) in sym7a, and dim 7–9 at floors 9–11 in sym7b. So the earlier phrase "resisted every method" should read "resisted every method at ~1.5 CPU-minutes per configuration".
- **Six parallel subagents launched** (each confined to a new directory, originals untouched, no commits): S0 `highdim/sym8/` big-budget peeling with the existing method; S1 `highdim/diag1/` anatomy of surviving classes (spurious points, kill-budget model); S2 `highdim/fastgen/` numpy-vectorized generator, same format; S3 `highdim/mixed/` new mixed-modulus per-coordinate refinement with its own independent checker; S4 `baker/` Matveev + LLL explicit bounds on L and on the top digit gap; S6 `level3/` Level-3 inventory and easy closures.
