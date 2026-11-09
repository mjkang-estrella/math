# REPORT_A — independent audit of Level 1 (2-D one-far certificates and the two-far {2,2,2} case)

Auditor: review sub-agent. All code is under `verification/indep/`. Everything is stdlib Python and was run as `ulimit -v 1500000; python3 -I …`. Nothing outside `verification/indep/` was touched, and nothing was committed.
Reproduce everything with `bash verification/indep/run_all.sh` (about 40 s). The full output is in `indep/run_all.log`.

## Method and independence
- `check2d.py` (task 1) was written from the format spec and first principles, **before** I opened `check_cert2d.py` or any generator. It does the following:
  - It recomputes the 3-adic signature from X mod 3^{j+2} (period 3^j), and the 7-adic signature from X mod 7^{i+1} (period 6·7^i, requiring 6 | ML and 6 | MQ).
  - It re-tests every `prime`/`T0` kill and every `rest` lift with the cyclic-subgroup test x^{lcm(o3,o7)} = 1, including all lifts when ord_p(10) ∤ M.
  - It decides every `pin` kill rigorously. The method is discrete logs: 3 is a primitive root mod 5^k, and (Z/2^m)* = ⟨−1⟩ × ⟨5⟩. This gives linear congruences in (a, w), and integer-lattice membership decides solvability. The lattice method equals brute-force residue enumeration on 810 cases.
  - It recomputes every `sz` leaf by exact integer arithmetic.
  - It checks that the tree partitions the domain, and runs an end-to-end box brute force. Every actual solution in the box must land in an `sz` leaf that lists it.
- I then wrote my own generator and checker, dimension 1/2/3 (`gen_nd.py`, `sievelib.py`, `universe.py`, `checknd.py`). The checker shares only the discrete-log and lattice helpers (`nt.py`) with `check2d.py`.
  - The generator's prime universe is every prime p ≤ 2·10^7 with ord_p(10) | 2^6·3^6·5^2·7^4 (414 primes, 235 with ⟨3,7⟩-index ≥ 2).
  - The checker trusts none of this: it re-derives and re-tests every kill. The earlier failure to close hard classes (the "r7 scan bug") was a prime-supply problem. Including the fully aligned primes (37, 13, 9901, 101, …) closes everything with small trees.
- Soundness validation of the checkers:
  - `test_region.py`: for 3440 (equation with a constructed known solution, prime, modulus) triples, the solution's own class is never killed.
  - 3 positive controls (2-D and 3-D equations with known solutions, in `controls.py` and `run_all.sh`): each solution is recorded in an `sz` leaf.
  - 8 tamper tests: bogus rest prime, dropped child, perturbed residue, wrong `sz` exponent, a true-solution class replaced by a prime kill, and a deleted recorded solution. All are rejected.

## (a) Pass/fail table

### Agent's 2-D certificates under my `check2d.py` (box brute force L ≤ 200)
| file | (A,K,qmin) | result | note |
|---|---|---|---|
| cert2d_S1_A9 | 9, 8, 4 | PASS | |
| cert2d_S1_A18 | 18, 8, 4 | PASS | |
| cert2d_S1_A27 | 27, 8, 4 | PASS | q=3 slice (14112) is outside this domain, covered by a 1-D cert |
| cert2d_S10_A9 | 9, 89, 3 | PASS | |
| cert2d_S10_A18 | 18, 89, 3 | PASS | |
| cert2d_S10_A27 | 27, 89, 3 | PASS | |
| cert2d_S101_A9 | 9, 908, 3 | PASS | |
| cert2d_S110_A9 | 9, 989, 3 | PASS | |
| cert2d_K9008_A9 | 9, 9008, 5 | PASS with caveat | 2 pin leaves are invalid at their declared exponent (see Gap 2); valid at the class's minimum q |
| **cert2d_S11_A9** | 9, 98, 3 | **FAIL** | 4 pin leaves (leaf ids 2, 4, 5, 23) are not killed (Gap 2) |
| cert2d_S30_A27 | 27, 269, 3 | PASS, but wrong configuration | A=27, S_low=30 is {4,4}, product 16, not a Level-1 configuration (Gap 1) |

### My own certificates (my generator + `checknd.py`, all PASS; solution lists match brute force)
- **2-D one-far, the 10 required (S_low, A) pairs**: (1,9), (10,9), (11,9), (30,9), (101,9), (110,9), (1,18), (10,18), (1,27), (10,27). Files are `certs/my2d_A{A}_K{K}.jsonl` with K = 9·S_low − 1. They have 1–13 nodes and zero solutions in the domain.
- **q=3 slice of K=8 (A = 9, 18, 27)**: 1-D K = 9008, 18008, 27008, all PASS.
- **Two-far {2,2,2}**:

  | case | certificate | result |
  |---|---|---|
  | K=8, q1≥4 | `my3d_K8` (7 nodes, 293 rest lifts) | PASS |
  | K=89, q1≥3 | `my3d_K89` (409 nodes, 105046 rest lifts, 2 `sz` leaves, no solutions) | PASS |
  | K=8, q1=3, q2≥5 | `my2d_A9_K9008` | PASS |
  | K=8, q1=3, q2=4 | 1-D K=99008, L≥7 | PASS |

  Brute force: 3-D box L ≤ 160 (≈ 6.3·10^5 points per K), no solutions.
- **All 19 all-low 1-D constants plus the 4 slice constants** were also re-certified independently with my own generator and checker (23 certs, all PASS). The only solutions with L ≥ t₀+1 are K=188 → L=6 (111132) and K=278 → L=2 (42).
- **Digit-level brute force**, independent of every 9n = 10^L − 1 + 9S manipulation: all pairs to L=220 and all {2,2,2} triples to L=80 (12.3 M candidates). The only members are {24, 32, 42, 14112, 111132}.

## (b) Is Level 1 now fully independently certified?
**Yes, with the repairs described below.** `coverage.py` enumerates all (far digits, S_low) classes from the five admissible multisets {2,2}, {2,3}, {2,4}, {3,3}, {2,2,2}, and maps each to a proof:
- (H), all non-1 digits at positions ≥ 3: re-derived by hand (mod 8 forces a even and w odd; mod 5 forces w ≡ a+2 mod 4; contradiction).
- Parity-dead classes.
- All-low (19 constants), one-far (10 pairs) and two-far (2 constants) cases.
- Every q-slice below the domain floor (t₀ ≥ 3 cases: K=8 and K=9008).
- Small L ≤ t₀ for the 1-D pieces, covered by the digit-level brute force.

Result: 0 uncovered or failing classes. Members of Level 1 with ≥ 2 non-1 digits: **32, 111132, 24, 42, 14112**. This is confirmed. The 9-class hard residual of r7/r8 is not needed in my certificate: p=37 (and 13, 9901, 101) kill the whole K=8 3-D problem already at modulus 3 or 12 or 6.

Not independent: the correctness of my own code is single-author. I mitigated this with the controls, tamper tests, randomized soundness test and brute-force cross-checks above. The reduction to the five multisets (≥ 2 non-1 digits, each ≥ 2, product ≤ 9 forces digits ≤ 4) and the formula 9n = 10^L + Σ9c·10^q + 9S_low − 1 (checked on 2000 random numbers) are first-principles.

## (c) Gaps found
1. **Missing/mislabeled configuration (S_low=30, A=9, K=269)**, {2,4} with the 4 at position 1 and the 2 far.
   - The agent's file `cert2d_S30_A27` has K=269 but A=27 (far digit 4). That is {4,4} (product 16), a configuration that does not occur.
   - The needed pair (A=9, K=269) had **no certificate**. I verified r6's own survivor list (S_low=30 with A=9) by recomputation.
   - This is a bookkeeping gap, not a mathematical one. My cert `my2d_A9_K269` closes the case completely: the whole class dies at modulus 6 under primes 11, 13, 37. There is no solution.
2. **Pin-kill bug in the agent's `check_cert2d.py` (real defect, masked by passing tamper tests).** In `pin_kill`, the 5-adic target is `K2·2^{-t0}` where K2 = K/2^{t0} already, so it divides by 2^{t0} twice. It is wrong whenever t0 ≥ 1.
   - Concrete witness: `cert2d_S11_A9` leaf 4 (r=(0,3) mod (6,6), K=98, t0=1, pin [3,1]). It claims 2·3^a ≡ 98 (mod 10^3) is unsolvable for a ≥ 3, w=0. But a=10 works: 2·3^10 = 118098 ≡ 98 mod 1000. The correct target is 49 mod 125 (a square, so solvable); the agent's is 87.
   - The agent's certificate `cert2d_S11_A9` is therefore **invalid as submitted** (4 leaves). The statement itself is true: my fresh certificate for (A=9, K=98) kills everything at modulus 6, and brute force agrees.
   - Two leaves of `cert2d_K9008_A9` have the same problem at their declared pin exponent 5. They are valid at the class's own minimum q (7), so I accept them via the class-minimum rule, which is mathematically sound. The pin kills in the other files (K=8, 89, 908, 989) are valid at their declared exponents.
3. No counterexample class was found. There are no solutions beyond the five known members and no unclosed (L, q) classes. The parent's r7 3-D sieve and `check_cert3d.py` are not needed for Level 1 any more, because my independent 3-D certificates supersede them.

## Caveats / bounds
- The checker brute-force boxes are L ≤ 800 (1-D), L ≤ 220 (2-D own), L ≤ 200 (agent's 2-D), and L ≤ 160 (3-D). These are only sanity checks. The proofs are the certificates.
- Slice domains:
  - 1-D slices use L ≥ t₀'+1, with L ≤ t₀' covered by the digit-level brute force (L=4 for K=9008; L=4..7 for K=27008, giving 14112 at L=5).
  - 2-D one-far certificates use q ≥ max(3, t₀+1). Slices q=3 for K=8 (A = 9, 18, 27) use K' = K + 1000A.
  - Two-far K=8: the q1=3 slice is the 2-D cert A=9, K=9008 for q2 ≥ 5, and 1-D K=99008 for q2=4.
