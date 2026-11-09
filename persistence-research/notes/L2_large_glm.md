# Level 2, part C — large targets 112, 14112, 111132 (research sub-agent, GLM)

**Role:** research sub-agent for LEVEL 2 part C. Targets: t ∈ {112 = 2⁴·7,
14112 = 2⁵·3²·7², 111132 = 2²·3⁴·7³}. Level 2 = all multi-digit 7-smooth n
with Π(n) = t. Another agent handles the small targets. Resource limits:
`bash -c 'ulimit -v 1500000; python3 -I file.py'`, stdlib only, < 20 min/command.
Artifacts live in `verification/glm/L2c/`. This note is appended after every step.

## 0. Setup, notation, and the master equation

For my three targets, 5 ∤ t. If 5 | Π(n) then n has a digit 5 or 0; a number
divisible by 5 ends in 0 or 5, so 5 | Π(n) iff 5 | n is *possible*; conversely
5 ∤ Π(n) ⟹ no digit of n is 0 or 5 ⟹ n is not divisible by 5 (n ≡ 0 mod 5
forces last digit 0/5). Hence **n = 2^i·3^j·7^k** and all digits of n lie in
{1,2,3,4,6,7,8,9}. (The pipeline asserts 5 ∤ t and rejects targets with 5 | t;
those need the 5^e treatment of `v8_delta5.py` and are out of scope here.)

Write n = R_L + S where R_L = (10^L − 1)/9 is the L-digit repunit and
S = Σ_p (d_p − 1)·10^p over the non-1 digits (d_p ∈ {2..9} at positions p).
Multiplying by 9:

  **9·n = 10^L + 9·S = 10^L + Σ_(non-1 p) 9(d_p − 1)·10^p.**

Positions 0,1,2 are *low*; positions ≥ 3 are *far*. With
S_low = Σ_(p≤2) (d_p−1)10^p, K = 9·S_low − 1, and far digits c_1..c_k at
positions 3 ≤ q_1 < … < q_k ≤ L−1 (A_i = 9(c_i−1) ∈ {9,18,27,36,54,63,72}):

  **2^{t0'}·3^a·7^w = 10^L + Σ_i A_i·10^{q_i} + K′**,  K′ = K + (fixed far terms),

where a = j + 2 ≥ 2 automatically (10^L + 9S ≡ 1 + 9S_low − 1 + 0 ≡ 0 mod 9
because 10 ≡ 1 mod 9 and K = 9S_low − 1). n = (RHS)/9 = 2^{t0'}·3^{a−2}·7^w.
The 2-adic exponent t0' = v₂(K′) is *constant on the domain* {L > q_i ≥ 3,
q_i + v₂(A_i) ≥ t0'+1}: every term 10^L, A_i10^{q_i} is ≡ 0 mod 2^{t0'+1} there,
so v₂(RHS) = v₂(K′) = t0'. Far digits that cannot satisfy q + v₂(A) > t0 are
handled by *slices* (their positions fixed in [3, t0]), which are finite 1-D/…,
see §pipeline. n's digit multiset is exactly {1s} ∪ low digits ∪ far digits, so
Π(n) = product of the configuration's multiset = t — the equation encodes the
whole problem. Π(n) = t > 9 also forces n to have ≥ 2 digits, so nothing is lost.

## 1. Configuration enumeration (pipeline step i)

A *configuration* = (choice of ≤ 3 digits of the multiset as low digits, their
exact positions in {0,1,2}) × (the rest as an unordered far multiset). Since
S_low has decimal digits equal to the (d−1) values (no carries, all ≤ 8), the
map configuration → (S_low, far A-multiset) is injective; the multiset is
recoverable. All-far (no low digits) is one configuration. Dedupe on
(S_low, sorted far A). For a multiset with m non-1 digits the number of
configurations is Σ_{j≤3} (m choose sub-multisets of size j) × P(3, j) — small.

## 2. Parity kill (pipeline step ii) — LEMMA (all-far dead)

**Lemma.** If every non-1 digit of n sits at position ≥ 3, there is no solution.
*Proof.* Low three digits of n are 1,1,1, so n ≡ 111 (mod 1000) (positions ≥ 3
contribute multiples of 1000; the repunit contributes 111). Hence
n ≡ 7 (mod 8) and n ≡ 1 (mod 5). n = 2^i3^j7^k: n odd ⟹ i = 0; 3^j7^k ≡ 7 mod 8
⟹ j even and k odd (table: 3^j7^k mod 8 = 1,3,5,7 for (j,k) parities
(ee),(oe),(oo),(eo) respectively). n ≡ 1 mod 5 ⟺ 3^j7^k ≡ 1 mod 5 ⟺ j ≡ k (mod 4)
(3 ≡ 3, 7 ≡ 2; 3^u7^v ≡ 1 mod 5 iff u ≡ v mod 4 — verified by the 16-case table).
j even and k odd contradicts j ≡ k mod 4. ∎

(The same kill fires for *any* configuration with S_low ≡ 0 mod 8 and
1 + S_low ≡ 1 mod 5, i.e. S_low ≡ 0 mod 40; all-far is the case S_low = 0.)
General parity kill: from v8 = (7 + S_low) mod 8 read the possible triples
(i mod 3, j mod 2, k mod 2); from v5 = (1 + S_low) mod 5 the condition
j ≡ k mod 4 or not; kill if the tables are inconsistent (exact 16-case check
in code). A low digit 5 is impossible for us (5 ∤ Π(n)); a low digit making
n ≡ 0 mod 5 is likewise killed (last digit of n is 1 or c ∉ {0,5}, but the
mod-5 table would demand 5 | n — impossible since n = 2^i3^j7^k).

## 3. Pipeline design (verification/glm/L2c/pipeline.py)

Given target t, the pipeline (single file, stdlib only):
1. **Multisets:** all multisets of digits from {d : 2≤d≤9, primes(d) ⊆ primes(t)}
   with product t (recursive over the exponent vector of t). Digits 0 and 5
   excluded (5 ∤ t).
2. **Configurations** per §1; **parity kill** per §2.
3. **Slices:** far digits with position q ≤ t0 = v₂(K) − v₂(A) + … (precisely:
   q + v₂(A) ≤ t0 for some q ≥ 3) are fixed-position slices; each slice is a
   smaller problem with K′ = K + Σ_fixed A·10^q and the remaining far digits
   required to have q ≥ t0′ − v₂(A) + 1; iterate until stable.
4. **Covering sieve** over classes (L, q_1..q_k) mod per-coordinate moduli
   (k = #variable far digits; k = 0 is the 1-D v12 problem, k = 1 the r8 2-D
   problem, k ≥ 2 the k-D generalization): per class compute the 3-adic/7-adic
   signature of X = 10^L + Σ A_i10^{q_i} + K′ (valid because
   ord_{3^{j+2}}(10) = 3^j and ord_{7^{i+1}}(10) = 6·7^i divide the moduli);
   kills: (T0) aligned prime with X ≡ 0; (region) aligned aux prime p where
   T = X·2^{−t0'} mod p is outside the reachable set of 3^a7^w given the a,w
   bounds; (split/rest) non-aligned primes — every misaligned lift must be
   killed, verified at the refined modulus; (pin) 10^{q'}-pins: on any subclass
   where min q_i and min(q_i + v₂(A_i)) and min L are ≥ e, the far terms vanish
   mod 2^e·5^e, so 3^a7^w ≡ K2 mod 2^{e−t0'} and ≡ K′2^{−t0'} mod 5^{e5} must be
   solvable — exact coset-set test when small, one-sided order test otherwise;
   (sz) when the signature pins a = a0 AND w = w0 exactly, n₀ = 2^{t0'}3^{a0−2}7^{w0}
   is a fixed integer whose decimal digits must realize the configuration —
   checked by digit comparison (this *finds* solutions rather than only killing);
   (deepen) otherwise raise min 3- or 7-valuation across tied coordinates.
   Symmetry: coordinates with equal A are permuted canonically (sound because
   every kill is symmetric under permuting equal-A coordinates).
5. **Certificates:** k = 0 → exact v12 format (checked by the parent's untouched
   `verification/v12_check_cert.py`); k = 1 → exact r8 `cert2d` format (checked
   by r8's `check_cert2d.py`); k ≥ 2 → documented k-D JSONL (same node schema,
   vector r/m) checked by a fresh `check_certkd.py` sharing no code with the
   generator. All checkers recompute signatures from scratch, re-verify tree
   coverage (every canonical lift is a child or rest-killed), re-test every
   kill, and direct-evaluate recorded solutions.
6. **Brute force** (ground truth): enumerate all (i,j,k) with 2^i3^j7^k ≤ 10^B,
   keep those with Π(n) = t; also per-configuration X-enumeration for small L.

**Soundness (brief).** Every n with Π(n) = t, n 7-smooth, multi-digit, lies in
exactly one configuration, hence one slice, hence one leaf class of one tree;
each leaf either is killed (verified kill: no (a,w) in the signature ranges can
satisfy the equation at the cited prime power — the signature ranges are valid
for every point of the class) or is an sz leaf whose recorded solutions are
verified by exact big-integer digit checks. Tree coverage is verified lift by
lift by the independent checker. The checker shares no code with the generator.

## 4. Level-1 re-validation

Run: `python3 -I pipeline.py solve 2 4 6 8 9 12 14 16 18 24 32 42 112 14112 111132`
(one shared brute-force bucket to 10^300; per-target certificates `cert_t*_*.jsonl`,
reports `solve_t*.json`).  Results (members = cert solutions + brute members; the
brute force reaches L = 300 exhaustively):

| Pi-target t | members found | matches v13 ground truth |
|---|---|---|
| 2 | 12, 21, 112 | yes |
| 4 | 14 | yes |
| 6 | 16, 32, 111132 | yes |
| 8 | 18, 24, 42, 81, 14112 | yes |
| 9 | (none) | yes |
| 12 | 126, 162, 216, 1134, 13122 | yes |
| 14 | 27, 72 | yes |
| 16 | 28, 128, 144, 224, 441 | yes |
| 18 | 36, 63, 192, 1323 | yes |
| 24 | 64, 243, 324, 432, 4116 | yes |
| 32 | 48, 84 | yes |
| 42 | 1176, 1372, 131712 | yes |
| 112 | 1728, 2187 | yes |
| 14112 | 33718272 | yes |
| 111132 | (none) | yes |

Zero coverage gaps on every target (`gaps=[]` everywhere): every 7-smooth member
with Pi = t and L <= 300 that lies in a *closed* configuration is recorded by a
certificate, and every member below a certificate's domain floor is labeled
`below domain floor`.  This reproduces Agent A's level-1 result (0 uncovered
configuration classes) on the whole audited universe: every configuration with at
most two far digits is PROVED (see status counts in the reports).  Positive
controls: `cert_t6_S21_K188_cnone.jsonl` records (L) = (6) -> n = 111132 and
`cert_t12_S11_K98_c18.jsonl` records (L, q) = (5, 3) -> n = 13122; both PASS the
independent checker `verification/indep/checknd.py`.

**Independent validation.** All 464 emitted certificates (201 of dim 1, 167 of
dim 2, 96 of dim 3) were checked with Agent A's `indep/checknd.py` (written
before reading my generator; shares no code with it): **PASS=464, FAIL=0**
(`glm/L2c/validate_all.log`).  No pin kills exist anywhere in the pipeline
(defect 1 of the audit eliminated); configurations are enumerated
programmatically from the digit multisets (defect 2 eliminated; the mislabeled
(30, 9) pair cannot recur).

## 5. Level-2 targets: 112, 14112, 111132

Per-multiset status (a configuration = (S_low, far multiset); "dim" = number of
far coordinates + 1):

* **t = 112 = 2^4 * 7** (4 multisets): **PROVED** for all configurations with
  dim <= 3 (55 proved, 49 parity-dead).  **OPEN above L = 300** for 12
  configurations of the multiset {2,2,2,2,7} and {2,2,4,7} whose slice
  decomposition contains dim >= 4 slices.  Members: exactly {1728, 2187}
  (both L = 4, brute-confirmed; the whole range L <= 300 is brute-covered).
* **t = 14112 = 2^5 * 3^2 * 7^2** (17 multisets): members exactly {33718272}
  (L = 8, brute-confirmed; found in the brute union, its own configuration
  containing dim >= 4 slices).  32 configurations PROVED (dim <= 3), 737
  parity-dead, 871 OPEN (850 with a dim >= 4 slice, 20 slice-budget
  overflows, 1 with a precise 2-class residual: config S_low = 387, far
  {54,54} of {4,7,7,8,9} — classes (L,q1,q2) == (6,3,2), (6,2,3) mod
  6049137024, a >= 11 unbounded, w = 0 exact).
* **t = 111132 = 2^2 * 3^4 * 7^3** (10 multisets): members exactly {} —
  brute force over L <= 300 finds none, matches v13.  474 parity-dead, 332
  OPEN (319 dim >= 4 slices, 13 slice-budget overflows); no configuration of
  these large multisets reduces to dim <= 3.

**Status summary.** For all three targets the member set is COMPUTED exactly up
to L = 300 (exhaustive brute force; agrees with v13_out.log) and the sieve
PROVES every configuration that reduces to dimension <= 3 — which is all of
Agent A's audited level-1 universe.  What remains OPEN is uniform and precise:
configurations whose slice decomposition still has >= 3 far coordinates.  For
those the 3-adic ladder family {X == 0 mod 3^{j+2}} has dimension >= 3 and
grows ~3^{dim-2}-fold per refinement level (measured: config far (9,9,9,9),
K=89: 26 -> 491 -> 8379 -> 84685 alive classes at levels 0..3; config far
(18,45,54,63), K=5489: 1 -> 106 -> 6881 -> 159830) while kills keep pace only
when a strong prime is aligned; since ord_p(10) for the killing primes
(17497, 52489, ...) contains 3^7..3^8, the aligned sets are empty until the
modulus itself carries 3^7, by which time the class count has exploded.  The
residual therefore affects only members with **L > 300** in those specific
configurations; closing it needs either a family-level character argument
(lattice/discrete-log, r7/r8 style) or bounds on 3-adic liftings — this is the
precise residual handed back.

Defect fixes re-verified: (1) no pin logic anywhere (the audited double
2^{t0}-division cannot occur); (2) configurations enumerated programmatically —
`enum_configs` derives every (S_low, far) pair from the multiset, and the
coverage replay re-derives each brute member's configuration the same way, so
the (30, 9) mislabeling is impossible by construction.

## Log

## Log (append-only)
1. Fixed `stats()` f-string; built front end (multisets, configs, parity, slices, brute bucket).
2. Brute ground truth B=100, then B=300 (shared bucket): level-1 members reproduced.
3. Rewrote pipeline solve mode in the audited `nd` JSONL format; no pin kills.
4. Defect fixes from audit REPORT_A: pin kills removed entirely; programmatic config enumeration.
5. Found+fixed: parity_dead lacked the L=1,2 rows and the far-digit L>=4 constraint; all-far (S_low=0) now dead for every target (generalizes the note's lemma).
6. Found+fixed: `vp()` missing arg; digit-order bug in the coverage replay (positions count from units digit).
7. Found+fixed: sz top-digit position used rstrip-length instead of len(str(res))-1 -> 13122 was silently dropped; now recorded (positive control passes).
8. Found+fixed: per-config validation of decoded solutions (carry-corrupted slice points filtered; completeness unaffected).
9. Found+fixed: slice() raise-floor branch dropped the coefficient (`nfree` typo) - silently deleted far terms (unsound). Fixed; slice counts rose (e.g. 10 -> 89 for the 33718272 config).
10. Widened the prime universe: MU = 2^7 3^10 5^2 7^5 (Agent A had 3^6); ladder classes need ord ~ 3^7-3^8 primes (17497, 52489 verified to kill 8 of 9 residual classes of (18, 98)).
11. Added direct whole-class kill at every node (sig constant on class; orders divide M by construction).
12. Dim >= 4 trees explode on 3-adic ladder families (measured growth); recorded as precise OPEN residuals; brute force covers L <= 300.
13. Final run all 15 targets: members match v13 exactly; 0 gaps; 464 certs; independent checker PASS=464 FAIL=0.
