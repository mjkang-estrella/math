# Level 2, part B — targets t ∈ {12,14,15,16,18,21,24,32,42,81} (research sub-agent)

Started. Context read: REPORT.md tail, r8 note, v12_check_cert.py, r8/check_cert2d.py.

## Plan
- [ ] Step 1: enumerate digit multisets over {2..9} with product t, per target.
- [ ] Step 2: brute force all 7-smooth n < 10^200 with Π(n) = t (each target), classify by multiset.
- [ ] Step 3: configuration case split (all-low / one-far / multi-far / (H)), re-prove (H) for Level 2.
- [ ] Step 4: close configurations with 1-D (v12) and 2-D certificates reusing r7/r8 generators.
- [ ] Step 5: report.

## Log

## Step 1-2 results (brute force to 200 digits, `L2b/brute.py`, 6 s)

29 members total: t=12: 126, 162, 216, 1134, 13122; t=14: 27, 72; t=15: 35, 135, 315;
t=16: 28, 128, 144, 224, 441; t=18: 36, 63, 192, 1323; t=24: 64, 243, 324, 432, 4116;
t=32: 48, 84; t=42: 1176, 1372, 131712; t=21: none; t=81: none (up to 200 digits).

Key structural facts set up:
- 5 | Pi(n) iff 5 | t (5|n => n ends in 5 or 0; no digit 0 allowed => ends in 5 => 5|Pi).
  Hence for t != 15: n = 2^u 3^a 7^w exactly. For t = 15: n = 5*3^a*7^w, and the digit 5
  is at position 0 (n ends in 5); the digit 3 is at position q >= 1. t=15 handled separately.
- Equation framework (r6/r8): n = repunit(L) + sum (d_i-1)10^i, so
  9n = 10^L + sum_far A_i 10^{q_i} + K, A_i = 9(d_i-1), K = 9 S_low - 1,
  S_low = sum_{i<3}(d_i-1)10^i. t = v2(K) pinned for L >= t0+1, q_i >= t0+1-v2(A_i).
- (H) re-proved for Level 2: all non-1 digits at positions >= 3 => n = 111 mod 1000 =>
  n odd, n = 3^u 7^w, mod 8 forces (u even, w odd), mod 5 forces u = w (mod 4): contradiction.
  Independent of t (needs only 5 !| t). For t=15 the config is impossible anyway (5 at pos 0).
- Parity kill (weak superset test, t mod 12): fixed K with no (t,a,w) solving
  2^t 3^a 7^w = K (mod 8) and (mod 5) => config dead for all L >= 3, q_i >= 3.
  (First version had a soundness bug for 8|K — t>=3 missed; fixed to t in 0..11.)

## Step 3: configuration census (L2b/configs.py)
- all-low: 105 distinct K, 68 parity-dead, **37 alive** (1-D certs needed).
- one-far: 181 distinct (A,K), 140 dead, **41 alive** (2-D certs + q<qmin slices).
- two-far: 130 distinct (A1,A2,K), 106 dead, **24 alive** (3-D).
- >=3 far: 36 distinct, 27 dead, **9 alive**: (9,9,9)/K=8, (9,9,9)/K=908,
  and K=8 with far (9,9,9,9), (9,9,18), (9,9,27), (9,18,9), (9,27,9), (18,9,9), (27,9,9).

## Step 4a: all-low 1-D certificates — DONE, all 37 VALID under v12_check_cert.py

Generator: L2b/gen17.py (copy of r8/gen_cert17.py with one patch: if a prime-split
would kill ALL children, fall through to deepening instead of emitting a childless
internal node, which the v12 checker rejects; r8 never hit that case). CHECK_CONSTANTS=0
(Level-1 constant-set assert disabled; engine unchanged otherwise).

Results (nodes / v12 output):
K=134 [3]; K=152 []; K=161 []; K=206 [4]; K=224 []; K=242 []; K=287 []; K=296 [];
K=332 []; K=548 []; K=584 [4]; K=647 []; K=656 []; K=728 []; K=944 []; K=962 [];
K=1007 []; K=1016 []; K=1052 []; K=1088 []; K=1844 []; K=1988 []; K=2348 [4];
K=2726 []; K=2744 []; K=2762 []; K=2807 []; K=2816 []; K=2888 []; K=4508 [2];
K=4526 []; K=5408 []; K=5444 []; K=5588 []; K=6308 []; K=6326 []; K=7208 [].
0 signature mismatches everywhere; recorded solutions L(>t0) as shown.
Cross-check vs brute hits: 134→L3? (9n=10^3+134=1134? no: 10^3+134=1134, n=1134/9=126 ✓ member 126, L=3);
206→L4: 10206/9=1134 ✓; 584→L4: 10584/9=1176 ✓ (t=42); 2348→L4: 12348/9=1372 ✓ (t=42);
4508→L2: 14508/9=1612? 1612=4·13·31 not 7-smooth... CHECK BELOW. All other recorded L ≤ t0 (artifacts).

**TODO check 4508 L=2**: 10^2+4508 = 4608 = 2^9·3^2 ✓ 7-smooth! n = 4608/9 = 512.111.. NOT integer!
Wait: 9n = 10^L + K requires 9 | 10^L + K. 4608/9 = 512 exactly (9·512=4608) ✓. n=512: digits 5,1,2
— contains 5! Pi(512) = 10 ≠ target. So n=512 is NOT a Level-2 member: it solves the all-low
equation for K=4508 (S_low = (6−1)+0+500 = 505? K=9·505−1=4504 no...). Actually the all-low
config for K=4508 comes from some multiset; n=512 has digit 5 → t must contain 5 → t=15 family.
The equation 2^t 3^a 7^w = 10^L + K with t = t0 is only valid when 5 !| t (n = 2^u3^a7^w);
n=512 = 2^9: t=9 ≠ t0=v2(4508)=2 — out of the cert's scope (L=2 ≤ ... hmm L=2 > t0=2? no, t0=2, L=2 not > t0).
Actually the checker reports solutions L > t0; L=2 = t0 → NOT counted. Good: recorded [2] means
L=2 = t0 boundary artifact, excluded by the checker. RESOLVED: K=4508 has NO solutions L > t0.

## PARENT UPDATE incorporated
- r8 2-D pin_kill divides by 2^t0 twice (wrong for t0 >= 1). => I will NOT use r8 pin logic.
  My gen17.py 1-D engine has no pins (v12 format) -> unaffected; all 37 1-D certs stand.
- For 2-D/3-D I switch to Agent A's independent tools verification/indep/gen_nd.py + checknd.py
  (correct single 2^-t0 division; no pin kills at all; aligned primes included).
- Ground truth v13: my targets' members <= 300 digits are exactly my 29
  (1728, 2187 have Pi=112 and 33718272 has Pi=14112 -> other agent's targets).
- Configurations enumerated programmatically (configs.py) -> no mislabel risk; will cross-check
  coverage against ground truth at the end.

## L2b addendum (round 2): the w-exact phantom and the v2-squeeze

**Diagnosis.** For 2-D pairs containing a true solution at q=qmin (e.g. (A,K)=(18,98),
member 13122 at (L,q)=(5,3)), the sieve leaves "ladder" classes: q ≡ 3 (mod 3^k·R),
L ≡ Hensel lift (mod 3^k·R'), whose kill-relevant data (T_p mod aligned primes) is
*identical to the true solution's class* and survives every prime-region kill. Empirically
81 unresolved nodes at M = 226842638400, all with sig a=(12,None), **w=(0,0) exact**.

Why r8 never saw this: in the K=8 two-far residual the phantom had **w unbounded**
(7 | X), so the reachable coset T·3^{-a_lo}·7^{-w_lo}·<3,7> *shifts* with a_lo,w_lo and
eventually misses <3,7> (killed at p=37 etc.). With **w exact**, the test collapses to
T ∈ <3> (since 3^{a_lo} ∈ <3>), which is *invariant* under a_lo — prime kills can
never fire. Agent A's cert for (27,8) closed only because qmin=4 excludes the true
q=3 and its phantom has w unbounded (X≡0 mod 7 there).

**The v2-squeeze (new kill, replaces the broken r8 pin).** For a class with w = w0 exact,
C = K/2^{t0} (odd), any solution point satisfies:
1. *5-pin:* X ≡ K (mod 10^{q1}) ⇒ 3^a ≡ C·7^{-w0} (mod 5^{q1}) ⇒ a ≡ ρ (mod 4),
   ρ = dlog_3(C·7^{-w0} mod 5). (Single division by 2^{t0} — correct pin.)
2. *2-pin:* 3^a·7^{w0} ≡ C (mod 2^{q1-t0}); solvable iff C·7^{w0} ≡ 1 or 3 (mod 8).
3. *Squeeze:* 2^{t0}(3^a·7^{w0} − C) = 10^{q1}(10^{L-q1} + A1 + A2·10^{q2-q1} + ...) so
   v2(3^a·7^{w0} − C) = q1 + s − t0 with s = v2(10^{L-q1} + A1 + ...). By the 5-pin
   a ≡ ρ (mod 4), so mod 16 the value 3^a·7^{w0} is the constant 3^ρ·7^{w0 mod 4};
   if that ≠ C (mod 16) then v2(3^a·7^{w0} − C) = β is a *fixed constant* < 4.
   Hence q1 = β + t0 − s ≤ Q := β + t0 − s_min: **q1 is bounded**, s_min computed over
   m1 ∈ [1,60] (asymptote v2(A1), reached for m1 > v2(A1) ≤ 3).
4. All class points have q1 ≡ r1 (mod M); if minq > Q the class is **empty**. If
   minq = r1 ≤ Q the class reduces to the single slice q1 = r1 (K' = A1·10^{r1} + K).

**Result on (18,98)** (cert /tmp/t53.jsonl, 81 u-nodes): 80 KILLED, 1 SLICE
(q=3 → K' = 18098), 0 FAIL — exactly matching the hand computation ρ=2, β=v2(9−49)=3,
s_min=1, Q=3.

**Slice closure.** Slice K' has its own t0' = v2(K'). Points with q < L ≤ t0' die by
v2(10^L + K') = min(L, t0') ≠ t0' (and L = t0' dies: (10^{t0'}+K')/2^{t0'} = 5^{t0'}+C'
is even). The v12 cert covers L > t0'. If C' = K'/2^{t0'} is **even**, the tree closes
fast (mod-16 death bounds L). If C' is **odd** (e.g. K'=18098, C'=9049) the tree is
phantom-ridden (depth cap hit) and the slice is a genuine 2-term Pillai problem
3^a·7^w = 5·10^{L−1} + 9049 — BUT the squeeze's *restricted* slice (L ≡ ρ mod M,
L ≥ ρ ≈ 10^11) is closeable elementarily: w = 0 forced (L ≡ 5 mod 6 ⇒ X ≡ 1 mod 7);
the 10-adic log c_∞ of 9049 base 3 exists (9049 ≡ 1 mod 8, 3 a pr. root mod 5^k) and
c_∞ ∉ N (3^a ≠ 9049); any solution has a = c(L) := least residue of c_∞ mod
2^{L−1}·5^{L−2} (pin precision ≫ 2.2L), and the sequence c(L) is non-decreasing with
jumps ≥ M_L ≫ 2.2L; since c_∞ ∉ N the jumps recur, so c(L) > 2.2L for all L beyond a
computable L*, and the finitely many surviving L are checked exactly (3^{c(L)} has
≤ ~500 digits). Implemented in slice_close.py; verified 0 surviving L on the AP.


## L2b round 3 (resume): pipeline path per parent update

Adopted Agent C's L2c/pipeline.py as the preferred path. Setup: verbatim copy of
pipeline.py + univ_20M.json into L2b/ (outputs land in L2b; L2c untouched).
Old artifacts of rounds 1-2 (gen17/certs1d, gen2d/certs2d, slice_close) kept as
cross-check material but superseded.

`stats 12 14 16 18 21 24 32 42 81` (9 s):
- t=21 (ms {3,7}): configs=13, alive=0 — ALL parity-dead.
- t=81 (ms {3,3,3,3},{3,3,9},{9,9}): configs=8+19+7, alive=0 — ALL parity-dead.
  => 21 and 81 are PROVED for ALL L by the mod-40 parity lemma alone; no sieve,
  no certificates, no L<=300 restriction needed. (Consistent with "no members
  up to 300 digits": stronger, no members at all.)
- t=12: 26 alive configs (18+11+4 slices... 3+7+2, 6+4, 3+1 = k-dist);
  t=14: 6 alive; t=16: 31 alive (14/21/10/4 slices); t=18: 20 alive;
  t=24: 57 alive; t=32: 49 alive; t=42: 20 alive.
- t=15: stock pipeline asserts (5|t out of scope) as documented — handled by a
  dedicated wrapper (see below).

## L2b round 3: pipeline run results (9 stock targets)

`run_solve.py` (driver; caches the shared 2^i3^j7^k bucket to 10^300 in bucket9.json)
calling the verbatim L2c copy's solve_target. Wall clock: 12/14/18 <= 3 s, 16 11 s,
24 34 s, 32 33 s, 42 5 s, 21/81 0 s.

| t | proved configs | open | parity-dead | members (certs + brute, L<=300) | gaps |
|---|---|---|---|---|---|
| 12 | 26 | 0 | 19 | 126, 162, 216, 1134, 13122 | [] |
| 14 | 6 | 0 | 7 | 27, 72 | [] |
| 16 | 29 | 2 | 16 | 28, 128, 144, 224, 441 | [] |
| 18 | 20 | 0 | 25 | 36, 63, 192, 1323 | [] |
| 21 | 0 | 0 | 13 | (none) | [] |
| 24 | 55 | 2 | 42 | 64, 243, 324, 432, 4116 | [] |
| 32 | 45 | 8 | 26 | 48, 84 | [] |
| 42 | 20 | 0 | 27 | 1176, 1372, 131712 | [] |
| 81 | 0 | 0 | 34 | (none) | [] |

- Members match the parent's ground truth exactly on every target; `gaps=[]`
  everywhere; all brute_only entries are `below domain floor` (L <= t0 artifacts).
- 21 and 81: EVERY configuration parity-dead => PROVED for ALL L by the mod-40
  lemma alone (stronger than "no members up to 300 digits").
- OPEN residuals (uniform kind: 3-adic ladder family, dim >= 4 slices; affect
  only L > 300, which brute force covers exhaustively):
  - t=16: multiset {2,2,2,2}, S_low in {10, 1} (2 configs, slices with 3 free
    far digits => dim-4 trees).
  - t=24: multiset {2,2,2,3}, S_low in {10, 1} (2 configs, dim-4 slices).
  - t=32: multiset {2,2,2,2,2}, S_low in {10,110,1,101,11} (5 configs; S_low=10,1
    have 4 free far digits => dim-5 trees; others dim-4) and {2,2,2,4},
    S_low in {10,30,1} (3 configs, dim-4). Total 8.
- Validation: `validate.py` runs Agent A's UNTOUCHED indep/checknd.py on every
  cert: **272 certs, PASS=272, FAIL=0** (validate_L2b.log).

## L2b round 3: the t = 15 extension (five mode)

Pipeline rejects 5 | t (its digit tuple omits 5 and it asserts 5 !| ps). Analysis
(in header of pipeline15.py): Pi(n)=15 forces digits {1,3,5} (one 3, one 5), n odd,
v5(n) <= 1 (no 25/75 endings possible); on the sieve domain X mod 5 = K mod 5, so
per slice 5 | K' <=> 5 | n <=> X = 5*2^t0 3^a 7^w; otherwise c=0 and the stock
sieve applies. S_low ≡ 4 (mod 5) ⟺ digit 5 at position 0.

Files (L2b/): pipeline15.py (documented copy: 5 added to the candidate digits;
five-aware parity table {5,15,25,35} mod 40; Sieve five flag multiplies Xmod and
kill_by by 5^{-1} mod m — all moduli coprime to 5; sz N *= 5; meta "five"), 
checknd5.py (indep/checknd.py copy with the mirrored five mode + nt.py), 
brute15 (digit-string enumeration of ALL n with Pi=15 — complete without any
smoothness assumption — plus 7-smoothness filter).

`pipeline15.py stats 15`: ms (3,5): 13 configs, 10 parity-dead, 3 alive — and all
3 alive are five configs (S_low = 4 dim-2 K=35; S_low = 24, 204 dim-1 K=215, 1835),
exactly the ones with the 5 at position 0.

`pipeline15.py solve 15`: **3 proved, 0 open, 10 parity-dead; members {35, 135, 315};
brute(L<=300)=3; brute_only=[]; gaps=[]** — every ground-truth member is a recorded
certificate solution (no `below domain floor` either: qmin=1 dim-1 domains).

Validation of the five certs: checknd5.py **PASS=3, FAIL=0** (validate_t15.log).
Robustness of the extension:
- regression: checknd5 on stock certs (five absent) behaves identically (PASS).
- stock checknd.py REJECTS all 3 five certs (K % 5 assert) => the 5-strip is
  load-bearing, not vacuous.
- tamper tests, all REJECTED: five->false on a five cert (assert), dropped sz
  solution (sz/brute mismatch), wrong rest prime 13->17 (rest lift survives:
  "node 3: rest lift (24,29) mod 42 survives primes [1933, 2689, 17]"), five=true
  on a stock cert (assert K % 5).

## Final status (part B)

| t | status | exact counts |
|---|---|---|
| 12 | PROVED for all L | 26/26 alive configs closed; 19 parity-dead; 5 members |
| 14 | PROVED for all L | 6/6; 7 dead; 2 members |
| 15 | PROVED for all L | 3/3; 10 dead; 3 members |
| 16 | 29 PROVED + 2 OPEN (dim-4 ladder) | members {28,128,144,224,441} computed to L<=300, gaps=[] |
| 18 | PROVED for all L | 20/20; 25 dead; 4 members |
| 21 | PROVED for all L | 0 alive, 13 parity-dead; no members |
| 24 | 55 PROVED + 2 OPEN (dim-4 ladder) | members {64,243,324,432,4116} computed to L<=300 |
| 32 | 45 PROVED + 8 OPEN (7 dim-4, 2 dim-5 slices) | members {48,84} computed to L<=300 |
| 42 | PROVED for all L | 20/20; 27 dead; 3 members |
| 81 | PROVED for all L | 0 alive, 34 parity-dead; no members |

Checker totals: 272 stock certs PASS (indep/checknd.py) + 3 five certs PASS
(checknd5.py) = 275/275. 275 cert files in L2b/.
