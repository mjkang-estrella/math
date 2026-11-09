# REPORT_E2 — independent coverage audit of Agent B's Level-2 results (t = 12, 14, 15, 16, 18, 21, 24, 32, 42, 81)

Auditor: review sub-agent E2. Everything is under `verification/indep3/`. Stdlib Python, run as `bash -c 'ulimit -v 4000000; python3 -I …'`. Nothing outside `indep3/` was written. Nothing was committed.

## Verdict
**B's PROVED labels for t = 12 and t = 42 were NOT valid as submitted. The same defect also hides in t = 16, 24 and 32.**
- Agent E's ordering defect is present in B's output: 20 configurations (t = 12: 2, 16: 2, 24: 8, 32: 6, 42: 2) have two far digits of different A.
  - For each, B certified only one ordering of the two far digits. The reversed placement is a separate equation and has no certificate.
  - These configurations were labelled PROVED (or sat inside a partly-PROVED target) with nothing declared open.
- The defect is repairable. I generated the 20 missing reversed-order dim-3 certificates with Agent A's generator, and all 20 PASS `checknd`.
- After the repair the coverage is complete:
  - t = 12, 14, 15, 18, 21, 42, 81: **PROVED for all L**.
  - t = 16, 24, 32: partially open. They have exactly B's 2 / 2 / 8 open configurations (≥ 3 far digits, dim ≥ 4), no more and no fewer.
- Everything else in B's work holds:
  - The enumeration is complete (my set equals B's exactly).
  - All parity kills are sound.
  - All 275 of B's certificates pass `checknd` / `checknd5`.
  - Brute force agrees.
  - The five-mode math is sound.
- E's leftover, t = 14112 S387 {54,54}, K = 3482, is certified (§6). It uses one NEW 2-adic leaf type, so it needs a (6-line) checker extension.

## 1. Coverage table (my enumeration; "far" = non-1 digits at positions ≥ 3)
Columns:
- "dead" = parity-dead by my mod-40 test.
- "certified as submitted" = alive configs with ≤ 2 far digits whose every placement is covered by B's certificates as they were. The test is point-level and order-aware (`i3_point.py`).
- "uncov.-undecl." = uncovered AND not declared open by B.
- "repaired" = filled by my new certificates.
- "open" = alive with ≥ 3 far digits (dim ≥ 4 generic slice), exactly matching B's `open` list.

| t | digit multisets | total configs | dead | alive ≤ 2 far | certified as submitted | **uncov.-undecl. as submitted** | repaired | declared open | final status |
|---|---|---|---|---|---|---|---|---|---|
| 12 | 3 | 45 | 19 | 26 | 24 | **2** | 2 | 0 | **PROVED, all L** |
| 14 | 1 | 13 | 7 | 6 | 6 | 0 | 0 | 0 | **PROVED, all L** |
| 15 | 1 | 13 | 10 | 3 | 3 (five-mode) | 0 | 0 | 0 | **PROVED, all L** |
| 16 | 4 | 47 | 17 | 28 | 26 | **2** | 2 | 2 | partially open (2 configs) |
| 18 | 3 | 45 | 25 | 20 | 20 | 0 | 0 | 0 | **PROVED, all L** |
| 21 | 1 | 13 | 13 | 0 | – | 0 | 0 | 0 | **PROVED (all parity-dead)** |
| 24 | 5 | 99 | 43 | 54 | 46 | **8** | 8 | 2 | partially open (2 configs) |
| 32 | 5 | 79 | 26 | 45 | 39 | **6** | 6 | 8 | partially open (8 configs) |
| 42 | 2 | 47 | 27 | 20 | 18 | **2** | 2 | 0 | **PROVED, all L** |
| 81 | 3 | 34 | 34 | 0 | – | 0 | 0 | 0 | **PROVED (all parity-dead)** |
| total | | 435 | 221 | 202 | 182 | **20** | 20 | 12 | |

- The "alive ≤ 2 far" counts add up per row: certified as submitted + uncovered-undeclared = alive ≤ 2 far. The total row is 182 + 20 = 202.
- My dead count is 1 higher than B's for t = 16 (config S_low = 71, K = 638, multiset {2,8}) and t = 24 (S_low = 35, K = 314, multiset {4,6}).
  - I kill both by mod 40: (111 + S_low) mod 40 = 22 and 26 are not reachable.
  - B has them as PROVED, with a dim-1 certificate (`cert_t16_S71_K638_cnone`, and the t = 24 analogue). That is harmless.
  - Hence my dead count is 17 and 43, against B's 16 and 42.
- Enumeration agreement (`i3_cmp.py`): 0 configs only in mine, 0 only in B's, 0 multiset mismatches, on all 10 targets. The only dead/alive differences are the two above.
- Brute force finds no members of t = 21 or t = 81 up to 10^600, which matches the parity proof.

### The 12 declared-open configurations (dim ≥ 4; I confirm B's list is exact)
- t = 16: {2,2,2,2} with S_low = 1 (far 9,9,9) and S_low = 10 (far 9,9,9).
- t = 24: {2,2,2,3} with S_low = 1 and 10 (far 9,9,18).
- t = 32:
  - {2,2,2,2,2} with S_low = 1 (far 9,9,9,9), 10 (far 9,9,9,9), 11, 101, 110 (far 9,9,9).
  - {2,2,2,4} with S_low = 1 (far 9,9,27), 10 (far 9,9,27), 30 (far 9,9,9).

Each has ≥ 3 far digits that can all sit at positions ≥ max(3, v₂(K)+1), so a generic slice is dim ≥ 4. No dim ≥ 4 certificate exists or can be checked by `checknd`. No alive config with ≥ 3 far digits is missing from B's open lists, and none is labelled PROVED.

## 2. Independent enumeration (`i3_enum.py`)
Derived from Agent E's `e_enum.py`, which was written without the GLM pipelines. Sanity checks are in `i3_sanity.py`.
- Digits are {2,3,4,6,7,8,9}, plus 5 if and only if 5 | t. Digit 0 is excluded (Π = 0).
- Multisets are all multisets of those digits with product t.
- For every multiset, every low pattern (d0, d1, d2) ∈ ({1} ∪ M)³ whose non-1 digits form a sub-multiset of M is a configuration. The far multiset is the remainder, so the three low positions are exact.
- Equation: 9n = 10^L + K + Σ A_i 10^{q_i}, with K = 9·S_low − 1 and A = 9(d − 1).
  - L here is the digit count, and the far positions satisfy 3 ≤ q_i < L.
  - It is checked on 30000 random digit strings (`i3_sanity.py`).
- v₂ slicing, "small-position effects": on q_i ≥ max(3, v₂(K)+1) we have v₂(X) = v₂(K).
  - Far digits at positions 3 … v₂(K) are fixed in separate slices, with K′ = K + A·10^p.
  - I do not use the slicing function for the verdict. The verdict comes from the point-level check, which enumerates positions 3 … 100 explicitly and handles larger positions symbolically.
- Parity kills:
  - For L ≥ 3, n mod 1000 = 111 + S_low exactly. There is no carry because (d − 1) + 1 ≤ 9, and positions ≥ 3 never matter.
  - The monoid closures of {2,3,7} are computed mod 40 and mod 1000 (`R40`, 20 residues; `R1000`, 500 residues). They are cross-checked against direct exponent enumeration.
  - A config is dead if (111 + S_low) mod 40 ∉ R40.
  - I also tried stronger tests, and they kill nothing more on these targets:
    - mod 1000;
    - the odd-digits-only variant using <3,7>.
  - S_low = 0 (all far) is dead everywhere.
  - L ≤ 2 is not covered by parity. It is inside the brute-force region.
- **t = 21 and t = 81**: every one of the 13 and 34 configurations is dead by mod 40. Both are PROVED with no members, for all L ≥ 3. L ≤ 2 is brute-forced, and the lattice brute force to 10^600 finds none.
- **t = 15** (five-mode, §4): all 13 configs are enumerated. 10 are dead, and the 3 alive ones are exactly those with the 5 at position 0.

## 3. Certificate mapping and the ordering hole (`i3_point.py`)
Method: point-level coverage, adapted from Agent E's `e_point.py`.
- A certificate (T, K′, coefs c1…cm, qmin) covers the placements where some subset of the far digits is FIXED, so K′ = K + Σ fixed A·10^p. The rest sit at ordered positions q1 < … < qm ≥ qmin with coefs matching in POSITION order, and L > qm.
- Every placement class must lie in the declared domain of some certificate.
  - Placements are the positions of the far digits for every L.
  - Positions 3 … 100 are explicit, and everything above is symbolic.
  - Points with L ≤ 300 are in the brute-force region, and dim-1 certificates need qmin ≤ 301.
- For every B certificate I asserted:
  - qmin > v₂(K);
  - root modulus 1;
  - dim = #coefs + 1;
  - K mod 5 ≠ 0 for every target except 15;
  - the `five` flag equals (5 | K).
- The largest qmin over all 275 of B's certificates is 11, so every "L below domain floor" is ≤ 11 and lies inside the brute-force range.

Result as submitted:
- Every config with 0 or 1 far digit is covered.
- Every config with two far digits of EQUAL A is covered.
- **Every config with two far digits of DIFFERENT A is NOT covered.** There are 20 such configs, and no reversed-order certificate exists anywhere in the repo (searched `verification/`, `results/`).
  - Tamper test: swapping the coefs of `cert_t12_S10_K89_c9_18` and `cert_t24_S10_K89_c9_45` makes `checknd` FAIL, with many surviving rest-lifts (`tamper/swap_*.jsonl`). The existing certificate does not prove the reversed equation.

The 20 holes. "A low-first" = the A-values of the far digits, lower position first. The reversed order is the missing one.
- t = 12 (multiset {2,2,3}):
  - S_low 1, K = 8: far {9,18}.
  - S_low 10, K = 89: far {9,18}.
- t = 16 (multiset {2,2,4}):
  - S_low 1, K = 8: far {9,27}.
  - S_low 10, K = 89: far {9,27}.
- t = 24:
  - {2,2,6}: S_low 1 (K = 8) and S_low 10 (K = 89), far {9,45}.
  - {2,3,4}: S_low 1 (K = 8) and S_low 10 (K = 89), far {18,27}.
  - {2,3,4}: S_low 30 (K = 269), far {9,18}.
  - {2,2,2,3}: S_low 11 (K = 98), 101 (K = 908) and 110 (K = 989), far {9,18}.
- t = 32:
  - {2,2,8}: S_low 1 (K = 8) and 10 (K = 89), far {9,63}.
  - {2,4,4}: S_low 30 (K = 269), far {9,27}.
  - {2,2,2,4}: S_low 11 (K = 98), 101 (K = 908) and 110 (K = 989), far {9,27}.
- t = 42 ({2,3,7}): S_low 1 (K = 8) and 10 (K = 89), far {18,54}.

For each hole the missing piece is only the "none-fixed" dim-3 certificate with the larger-A digit at the LOWER position. The dim-2 slices where one digit is fixed at position 3 or 4 already exist.

## 4. Repair, and the five-mode (t = 15) check
Repair: **20 reversed-order dim-3 certificates** in `certs_e2/` (K, coefs low-first, qmin, nodes):

| t | S_low | K | coefs (low-first) | qmin | nodes |
|---|---|---|---|---|---|
| 12 | 1 | 8 | (18,9) | 4 | 315 |
| 12 | 10 | 89 | (18,9) | 3 | 648 |
| 16 | 1 | 8 | (27,9) | 4 | 677 |
| 16 | 10 | 89 | (27,9) | 3 | 612 |
| 24 | 1 | 8 | (27,18) | 4 | 243 |
| 24 | 1 | 8 | (45,9) | 4 | 1026 |
| 24 | 10 | 89 | (27,18) | 3 | 484 |
| 24 | 10 | 89 | (45,9) | 3 | 178 |
| 24 | 11 | 98 | (18,9) | 3 | 308 |
| 24 | 30 | 269 | (18,9) | 3 | 341 |
| 24 | 101 | 908 | (18,9) | 3 | 619 |
| 24 | 110 | 989 | (18,9) | 3 | 1434 |
| 32 | 1 | 8 | (63,9) | 4 | 97 |
| 32 | 10 | 89 | (63,9) | 3 | 904 |
| 32 | 11 | 98 | (27,9) | 3 | 546 |
| 32 | 30 | 269 | (27,9) | 3 | 463 |
| 32 | 101 | 908 | (27,9) | 3 | 509 |
| 32 | 110 | 989 | (27,9) | 3 | 447 |
| 42 | 1 | 8 | (54,18) | 4 | 887 |
| 42 | 10 | 89 | (54,18) | 3 | 563 |

- Generator: Agent A's `gen_nd.py`, copied unmodified to `indep3/gen/` apart from the prime-universe cache path. It uses E's wide prime universe `univ_wide.json` (503 primes), `--deep 8 --mcap 1e9`.
- **Hard cases:** none. All 20 closed in under 30 s each, with maximum M ≤ 1,968,300 and 0 unresolved classes. The wide universe was used by default, so I did not need E's escalation.
- Validation: all 20 PASS the unmodified `indep/checknd.py` with a brute-force box of L ≤ 150 (about 5·10^5 points each; 0 claimed solutions, 0 brute solutions). Logs are in `logs/chk_*.log`, with the summary in `logs/chk_summary_certs_e2.txt`.
- After adding them, `python3 -I i3_point.py certs_e2` gives **0 holes on all 10 targets**, with every alive ≤ 2-far config covered (202/202). Removing them reproduces the 20 holes.
- B's 275 certificates all PASS the unmodified `checknd` (stock, 272 certs) / `checknd5` (the 3 five-mode certs) with box L ≤ 60 (`logs/chk_summary_L2b.txt`: 275 × `rc=0 RESULT: PASS`).
- B's legacy artifacts `certs1d/` and `certs2d/` are not used for coverage. They come from the older generators with the known pin bug. Only the `cert_t*.jsonl` set matters.

**Five-mode math (t = 15), verified by me:**
- Π = 15 forces digits {1,3,5} with exactly one 3 and one 5. So n is odd and 2 ∤ n.
- If the 5 is not at position 0, then 5 ∤ n and n ∈ <3,7>. All 10 such configs have (111 + S_low) mod 40 ∈ {11, 31, 33}, and none of these is in R40o = {1,3,7,9,21,23,27,29}. So they are dead.
- If the 5 is at position 0, n ends in 15 or 35 (the second digit is 1 or 3). Then n mod 25 ∈ {15, 10}, so v₅(n) = 1 exactly. Hence n = 5·m with m = 3^a7^w, and X = 9n = 5·(9m).
  - On the sieve domain (positions ≥ 1), X ≡ K (mod 5). So 5 | K if and only if the five case holds, and K mod 5 = 0 is asserted against the `five` flag.
  - The checker solves Y = X/5 by multiplying X mod p by 5⁻¹. This is exact because every modulus (3^j, 7^i, primes p > 7) is coprime to 5. The `sz` leaf value becomes N = 5·2^t0·3^a·7^w, and the brute box skips X with 5 ∤ X.
  - v₂, v₃, v₇ are untouched by the factor 5, and the real solutions satisfy Y = 2^t0 3^a 7^w. So the sieve is sound.
- I read the 4-line diff of `checknd5.py` against `indep/checknd.py`; those are the only changes.
- The three alive configs (n mod 1000 = 115, 135, 315, so m = n/5 mod 200 ∈ {23, 27, 63}, all in <3,7>) are covered:
  - S_low 4, K = 35, coefs (18), qmin 3: covers all positions ≥ 3.
  - S_low 24, K = 215, dim 1, qmin 1: all L ≥ 1. It records L = 2 and 3, the members 35 and 135.
  - S_low 204, K = 1835, dim 1, qmin 1. It records L = 3, the member 315.
- Re-run with box L ≤ 300: 3/3 PASS. My tamper tests (`tamper/f*.jsonl`) are all REJECTED:
  - drop the `five` flag (assertion);
  - replace a rest prime with 13 (a lift survives);
  - drop a child (a lift is neither child nor killed);
  - run the stock `checknd` on a five certificate (the K mod 5 assertion).
- The t = 15 brute force by digit strings (§5) is complete without any smoothness assumption.

## 5. Independent brute force to 10^300 (and 10^600)
- **Lattice** (`i3_brute.py`): all n = 2^i·3^j·7^k < 10^300 are enumerated, 37,375,388 numbers. The digit product is read from `str(n)`, and only digit sets without 0 or 5 are considered. I also ran LMAX = 600, which scanned 297,795,264 numbers.
- **t = 15 by digit strings** (`i3_brute15.py`): all strings of length 2 … 300 with digits {1,3,5}, one 3 and one 5 (8,999,900 strings), tested for 7-smoothness by trial division by 2, 3, 5, 7. No assumption about the form of n is needed.
- Members, which match the ground truth in `REPORT.md` (Ground-truth Level 2 grouped by Π) exactly on all 10 targets:

| t | members | t | members |
|---|---|---|---|
| 12 | 126, 162, 216, 1134, 13122 | 24 | 64, 243, 324, 432, 4116 |
| 14 | 27, 72 | 32 | 48, 84 |
| 15 | 35, 135, 315 | 42 | 1176, 1372, 131712 |
| 16 | 28, 128, 144, 224, 441 | 21 | none |
| 18 | 36, 63, 192, 1323 | 81 | none |

- The L ≤ 600 lattice run agrees (same lists).
- Coverage replay (`i3_replay.py`): every member with ≥ 3 digits lies in a NON-dead configuration of my enumeration, with a unique key. This is a soundness test of the parity kills against ground truth. Members with fewer than 3 digits (27, 72, 35, 28, 36, 63, 64, 48, 84) are brute-force only.

## 6. E's leftover: t = 14112, S387, far {54,54}, K = 3482 — **CERTIFIED** (with one new leaf type)
- First, "reversed slice" is a misnomer. The coefficients are equal, so there is only one ordering. The unresolved piece is the whole K = 3482 dim-3 domain (and, once qmin is raised to 4, the q1 = 3 slice).
- **Why it was hard.**
  - X(6,3,2) = 10^6 + 54·10^3 + 54·10^2 + 3482 = 1062882 = 2·3^12. This is an integer solution OUTSIDE the domain (q = 2).
  - Every class (L, q1, q2) ≡ (6,3,2) mod M has the same kill-relevant data (T mod p) as that point. Here w = 0 is exact and a is unbounded.
  - So no prime kill can ever fire on these classes. They are a "phantom ladder", the same phenomenon B diagnosed in its round-2 addendum.
  - The generator therefore ran into class explosion and MemoryError (the E run), or stopped with 2 unresolved classes (C's run).
- **The 2-adic fact that kills it.** If all positions are ≥ t0 + 3 = 4, then X ≡ K (mod 16).
  - So 3^a·7^w ≡ K/2 = 1741 ≡ 5 (mod 8).
  - Since 3^a ∈ {1,3} and 7^w ∈ {1,7} mod 8, this forces a odd and w odd.
  - Hence every class with w = 0 exact, and in general with w even exact, dies. I checked 3^a7^w mod 8: for w even the set is {1,3}, and for w odd it is {5,7}.
  - The same C ≡ 5 (mod 8) holds for the q1 = 3 slice, K′ = 3482 + 54000 = 57482 (K′/2 = 28741 ≡ 5).
- **Implementation: a NEW leaf kind `pin2`.**
  - Soundness conditions: qmin ≥ t0 + 3, and C = K/2^t0 mod 8 ∉ {3^a·7^w mod 8 : (a, w) allowed by the class signature}. The signature means a, w are either exact or range over their parity classes.
  - The pin is not in the original `checknd` format. I copied `checknd.py` to `pin2/chk_pin2.py` with ONE added branch (8 lines, a diff against `chk/checknd.py` shows only that branch). The generator is `pin2/gen_pin2.py` (the unmodified generator plus the same test).
  - **This checker is NOT independent of me.** The pin rule needs a parent review. It is a 6-line argument that I verified by hand, and the tamper tests below check it.
- **Certificates (`certs_s387/`), both PASS `chk_pin2` with box L ≤ 200:**
  - K = 3482, coefs (54,54), qmin 4: 29 nodes, 7 `pin2` leaves, 2918 prime-killed rest-lifts, max M = 108. 1,254,890 brute points, 0 solutions.
  - K = 57482, coefs (54), qmin 4: 3 nodes, 2 `pin2` leaves, 34 rest-lifts. 19,306 points, 0 solutions.
- Together with the existing certificates they cover S387 {54,54} completely: both positions ≥ 4 (dim 3), one position = 3 (dim 2), both = 3 is impossible, and L ≤ 300 is brute-forced.
- **Tamper tests (`tamper/`), all REJECTED:**
  - qmin set to 3: "pin2 needs qmin ≥ t0+3".
  - A leaf's residue shifted: a rest-lift survives.
  - K changed to 57394 (C ≡ 1 mod 8): "pin2 does not kill (C mod 8 = 1)".
- **Positive control:** for K = 2·3^20 − 10^8 − 54·10^5 (a true solution at (L, q) = (8, 5)), the generator leaves the solution's class UNRESOLVED instead of pinning it. So the pin is not over-killing.
- Consequence for t = 14112 (not my target, but E's leftover): the one config declared OPEN among E's ≤ 2-far configs, S387 {54,54}, can be upgraded to PROVED, subject to the parent's review of the `pin2` leaf kind.
- The same pin may shrink other phantom-ladder residues, but `checknd` supports only dim ≤ 3, so it does not touch the 12 dim ≥ 4 open configs above. I did not attempt those.

## 7. Final status per target
- **t = 12 — PROVED for all L** after the 2-config repair. Members 126, 162, 216, 1134, 13122.
- **t = 14 — PROVED for all L.** Members 27, 72.
- **t = 15 — PROVED for all L** (five-mode math verified; 3 five-certs PASS `checknd5`). Members 35, 135, 315.
- **t = 16 — partially open.**
  - 2 configurations, ({2,2,2,2}, S_low 1 and 10), are COMPUTED to L ≤ 300 and OPEN beyond.
  - Everything else is PROVED after the 2-config repair.
  - Members 28, 128, 144, 224, 441.
- **t = 18 — PROVED for all L.** Members 36, 63, 192, 1323.
- **t = 21 — PROVED for all L** (all configs parity-dead; no members).
- **t = 24 — partially open.**
  - 2 configurations, ({2,2,2,3}, S_low 1 and 10), are OPEN beyond L = 300.
  - Everything else is PROVED after the 8-config repair.
  - Members 64, 243, 324, 432, 4116.
- **t = 32 — partially open.**
  - 8 configurations are OPEN beyond L = 300, listed in §1.
  - Everything else is PROVED after the 6-config repair.
  - Members 48, 84.
- **t = 42 — PROVED for all L** after the 2-config repair. Members 1176, 1372, 131712.
- **t = 81 — PROVED for all L** (all configs parity-dead; no members).
- B's PROVED labels for 12 and 42 are restored by the repair. The PROVED parts of 16, 24, 32 are valid only with the repaired certificates.
- Level-2 open total for B's targets: 12 configurations (2 + 2 + 8), unchanged.

## Files
- Enumeration and checks: `i3_enum.py`, `i3_cmp.py`, `i3_point.py`, `i3_replay.py`, `i3_sanity.py`, `i3_brute.py`, `i3_brute15.py`.
- Outputs: `i3_point_out.json` (as submitted), `i3_point_out_repaired.json`, `i3_brute_{300,600}.json`, `i3_brute15_300.json`, `logs/`, `tamper/`.
- Repair: `gen/` (copy of Agent A's generator and E's wide-universe cache), `run_gen.sh`, `gen_jobs.txt`, `certs_e2/` (20 certs).
- Checkers used: `chk/` (unmodified `indep/checknd.py`), `chk5/` (B's `checknd5.py` unmodified), `run_chk.sh`.
- S387: `pin2/` (`gen_pin2.py`, `chk_pin2.py`), `certs_s387/` (2 certs).
- Repro:
  - `python3 -I i3_enum.py; python3 -I i3_cmp.py; python3 -I i3_point.py` (the as-submitted holes)
  - `python3 -I i3_point.py certs_e2` (0 holes)
  - `python3 -I i3_brute.py 300; python3 -I i3_brute15.py 300; python3 -I i3_replay.py`
  - `ls ../glm/L2b/cert_t*.jsonl | xargs -P 28 -n 1 ./run_chk.sh`
