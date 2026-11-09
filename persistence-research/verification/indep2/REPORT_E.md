# REPORT_E — independent coverage audit of Agent C's Level-2 results (targets 112, 14112, 111132)

Auditor: review sub-agent E. All files are under `verification/indep2/`. Stdlib Python, run as `bash -c 'ulimit -v 4000000; python3 -I …'`. Nothing outside `indep2/` was written (importing `../indep/checknd.py` may refresh `indep/__pycache__`). Nothing was committed.

## Verdict
**C's PROVED labels are NOT all valid. 39 configurations are only half-covered, and nothing declares them open.**
- 16 configs for t = 112 and 23 for t = 14112 are labelled PROVED, but only ONE of the two orderings of their two *distinct* far coefficients has a certificate (details in §3).
- The cause is a design error in the nd domain. `checknd` certifies `10^L + c1·10^q1 + c2·10^q2 + K` on the ordered domain `L > q2 > q1 ≥ qmin`, with `coefs[0]` at the LOWER position.
  - For c1 ≠ c2, the placement with c2 at the lower position is a different equation. It has no certificate.
- This is a real coverage hole, but it is repairable. I generated the 39 missing reversed-order certificates with Agent A's generator, and all 39 pass `checknd` (§3).
  - After adding them, every non-dead config with ≤ 2 far digits is covered, except the already-declared OPEN config (14112, S_low = 387, far {54,54}).
- Everything else holds:
  - The enumeration is complete.
  - All parity kills are sound.
  - All 152 of C's certs for these targets pass.
  - The OPEN lists are exact.
  - Brute force agrees.

## Coverage tables (my enumeration; "far" = non-1 digits at positions ≥ 3)
| | t = 112 | t = 14112 | t = 111132 |
|---|---|---|---|
| digit multisets (digits 2,3,4,6,7,8,9; Π = t) | 4 | 17 | 10 |
| total configurations (S_low, far multiset) | **116** | **1640** | **806** |
| parity-dead (mod 40; mine = C's) | 49 | 737 | 474 |
| alive | 67 | 903 | 332 |
| alive with ≥ 3 far digits, declared OPEN by C | 12 | 870 | 332 |
| alive with ≤ 2 far digits | 55 | 33 | 0 |
| ...fully certified by C's certs as submitted | 39 | 9 | – |
| ...declared OPEN by C (≤ 2 far) | 0 | 1 (S387, far {54,54}) | – |
| ...**UNCOVERED, undeclared, as submitted (labelled PROVED)** | **16** | **23** | 0 |
| ...uncovered after my 39 extra certs | 0 | 0 (+ the 1 declared open) | – |
| UNCOVERED-undeclared (≥ 3 far digits) | 0 | 0 | 0 |
| brute-force region L ≤ 300 | complete | complete | complete |

- My config set equals C's exactly, on all three targets: 0 configs only in mine, 0 only in C's, 0 multiset mismatches.
- C's top-level `open` list equals mine: 12 / 871 / 332 entries, matched as (multiset, S_low).
- The 871 for 14112 is the 870 configs with ≥ 3 far digits plus S387.
- 111132 has no configuration with ≤ 2 far digits, because the minimum number of non-1 digits is 9 and at most 3 can sit in the low positions. So nothing is certifiable by dim ≤ 3 sieves, and C correctly emitted no certificates for it.

## 1. Independent enumeration (`e_enum.py`, written before reading `pipeline.py`)
- Digit multisets: all multisets of {2,3,4,6,7,8,9} with product t. Digit 0 is excluded (Π = 0) and digit 5 is excluded (5 ∤ t).
- Configurations:
  - For every multiset, every low pattern (d0, d1, d2) ∈ ({1} ∪ M)³ whose non-1 digits form a sub-multiset of M. The far multiset is the remainder.
  - The key (S_low, sorted far A-values) is unique. Duplicates are asserted absent.
- Equation: `9n = 10^L + K + Σ A_i·10^{q_i}`, with K = 9·S_low − 1 and A = 9(c − 1).
  - `e_sanity.py` checks it on 20000 random digit strings.
- v₂ and slicing:
  - On the domain `q_i ≥ max(3, v₂(K′)+1)` (and L > q_i) we have v₂(X) = v₂(K′). Fixed far digits at positions 3..v₂(K′) are recursed on with K′ = K + A·10^q.
  - My `slices()` derivation and a more precise point-level check (§3) agree on what is needed.

## 2. Parity kills — all verified
- n = 2^i·3^j·7^k (5 ∤ n, because no digit is 0 or 5).
- For L ≥ 3, n mod 1000 = 111 + S_low exactly (no carry, since (d−1)+1 ≤ 9). Positions ≥ 3 never matter.
- Reachable residues of 2^i3^j7^k:
  - mod 40: 20 residues, `{1,2,3,4,6,7,8,9,12,14,16,18,21,23,24,27,28,29,32,36}`.
  - mod 1000: 500 residues.
  - Both are computed by monoid closure and cross-checked by direct enumeration in `e_sanity.py`.
- Checks:
  - Every config C calls parity-dead has (111 + S_low) mod 40 ∉ R40: 0 exceptions, on all three targets.
  - The converse: the mod-40 and mod-1000 dead sets coincide with each other and with C's dead sets (49 / 737 / 474), so C missed none.
  - S_low = 0 (all-far) is dead: 111 mod 40 = 31 ∉ R40.
  - L ≤ 2 is not covered by parity, but it is inside the brute-force region.

## 3. Certificate mapping — the ordering hole
Method: the point-level check in `e_point.py`.
- Every placement class (positions of the far digits, any L) of each alive config with ≤ 2 far digits must lie in the declared domain of some certificate.
- Certificate (K′, coefs c1..cm, qmin) covers the placements where some subset of the far digits is FIXED, so K′ = K + Σ fixed A·10^p. The rest sit at ordered positions q1 < … < qm ≥ qmin, with coefs matching in position order, and L > qm.
- Positions 3..100 are enumerated explicitly. Everything above is treated symbolically.
- Every cert meta was checked: qmin > v₂(K), root modulus 1, dim = #coefs + 1, K ≢ 0 (mod 5). The maximum qmin over C's certs is 13, so every "L below domain floor" is ≤ 13 and lies inside the brute-force range (L ≤ 300, in fact ≤ 600).

Result as submitted by C:
- Every config with 0 or 1 far digit is fully covered.
- Every config with a two-far *equal* pair (A, A) is fully covered, except S387.
- Every config with two far digits of DIFFERENT A is NOT covered: no cert for the reversed placement. `checknd` confirms the semantics. Swapping `coefs` in `cert_t112_S110_K989_c27_54` (`tamper/swap_S110_K989.jsonl`) makes `checknd` FAIL with many surviving rest-lifts. So the existing cert does not prove the reversed equation.

The 39 uncovered configs. Notation: S_low:digit+digit.
- t = 112 (16): S110:4+7, S310:2+7, S610:2+4, S130:2+7, S101:4+7, S301:2+7, S601:2+4, S11:4+7, S61:2+4, S103:2+7, S13:2+7, S16:2+4, S10:7+8, S70:2+7, S1:7+8, S30:4+7.
- t = 14112 (23): S663:8+9, S863:7+8, S673:7+9, S636:8+9, S736:7+9, S836:7+8, S376:7+9, S676:4+9, S876:4+7, S637:7+9, S667:4+9, S867:4+7, S638:7+8, S678:4+7, S655:7+8, S565:7+8, S665:6+8, S765:6+7, S556:7+8, S656:6+8, S756:6+7, S576:6+7, S657:6+7.

Repair, done by me:
- Missing certs: 40 reversed-order dim-3 certificates (16 for 112, 24 for 14112). I generated 39 of them.
- Generator: Agent A's `gen_nd.py`, copied to `indep2/gen/`, with the prime-universe cache redirected to `indep2/` and C's wider universe (MU = 2^7·3^10·5^2·7^5, `univ_wide.json`) for the hard ones.
  - Any generator is acceptable, because soundness comes from the independent checker.
- Output: `indep2/certs_e/*.jsonl` (39 files).
- **All 39 PASS `checknd`** (`logs/chk_e_*.log`, brute-force box L ≤ 100; 0 claimed solutions; `logs/chk_e_summary.txt` exit codes all 0).
- With them, `E_EXTRA=real python3 -I e_point.py` reports 55/55 (t = 112) and 32/33 (t = 14112) configs fully covered. The one exception is S387 {54,54}, declared OPEN by C.
- Not generated: reversed-order, K = 3482, coefs (54,54), the S387 slice. It is the declared "2-class residual" and was still running (or timed out) at hand-in. It is NOT claimed.
- Extras in C's output: 5 (t = 112) and 7 (t = 14112) cnone certs are not needed by my cover (e.g. K = 41408 = 5408 + 36000, the "27 and 9 at the same position" collision slice). They are harmless and redundant, though the slices they came from are not real configurations.
- Two dim-1 pieces I first listed as "missing" (K = 284408 etc.) are redundant: they are already inside `cert (14408, 27)`, whose domain includes q = 4. The point-level check reflects this.

All 152 certs C emitted for 112 and 14112 PASS `checknd` independently (`logs/chk_cert_*.log`, box L ≤ 60). Only one has a claimed solution: `cert_t112_S76_K683_c9`, with (L, q) = (4, 3), i.e. 2187.

## 4. Brute force (`e_brute.py`, lattice enumeration)
- Method: all n = 2^i·3^j·7^k < 10^LMAX are enumerated, and the digit product is read from `str(n)`.
- Scale: 37,375,388 numbers scanned for L ≤ 300 (the formula predicts ≈ 37.07 M). I also ran LMAX = 600: 297,795,264 numbers.
- Members (multi-digit, Π equal to the target):
  - Π = 112: **1728, 2187** (L = 4)
  - Π = 14112: **33718272** (L = 8)
  - Π = 111132: **none**
- This matches C and the parent's v13 sweep, and holds up to L = 600, beyond the required 300.
- Where the members sit in the coverage:
  - 2187 is recorded in an `sz` leaf of `cert_t112_S76_K683_c9`.
  - 1728 is all-low, L = 4, below the dim-1 floor, so it is brute-force covered.
  - 33718272 has the config (S_low = 161, far {18,18,54,63}), which is declared OPEN.

## 5. C's claims for configs with few far digits
- 0 or 1 far digit, or an equal pair (A, A): **PROVED claims hold** (certificates pass, domains cover every placement).
  - Exception: S387 (equal pair {54,54}) is declared OPEN, and it is.
- Two far digits of different A: **claims do NOT hold as submitted** (39 configs), but they hold after my 39 added certs.
- 3 or more far digits: C labels all of them OPEN, with 0 PROVED labels. The OPEN labels are exact: no alive config with ≥ 3 far digits is missing from the open list, and none was mislabelled PROVED.
  - What C calls "dim ≤ 3" means ≤ 2 far digits plus L, not "≤ 3 far digits".
- The remaining OPEN residual is exactly as C states:
  - 12 / 871 / 332 configs, each with a dim ≥ 4 generic slice, covered only by brute force to L ≤ 300 (my check to 600).
  - Plus the S387 residual.

## 6. Other observations
- The same ordering defect also affects the other targets' certificates in `glm/L2c/`: 20 distinct-A dim-3 certs for t = 12, 16, 24, 32, 42 each exist in one order only (counts 2 / 2 / 8 / 6 / 2). Level 1 itself is unaffected, because Agent A's Level 1 only needed equal-coefficient pairs. The parent should have the t ∈ {12,16,24,32,42} reviewers check this.
- Soundness of the pointwise logic: removing the added certs reproduces the 39 holes, and adding hypothetical or real ones removes them. The digit-level formula check passes on 20000 random strings.

## Files
- Enumeration and checks: `e_enum.py`, `e_sanity.py`, `e_cover.py`, `e_missing.py`, `e_point.py`, `e_brute.py`.
- Outputs: `e_cover_out.json`, `e_point_out.json`, `e_missing.json`, `e_brute_{60,300,600}.json` and `.log`, `logs/`, `tamper/`.
- Repair: `gen/` (copy of Agent A's generator, with the cache path and wide-universe option changed), `run_gen.sh`, `gen_jobs*.txt`, `certs_e/` (39 certs).
- Repro: `python3 -I e_cover.py; python3 -I e_point.py; E_EXTRA=real python3 -I e_point.py; python3 -I e_brute.py 300`.
