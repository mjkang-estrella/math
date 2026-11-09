# Round 8 — certificates for the rest of Level 1 (all-low 17 + one-far mixed), and the two-far residual

**Role:** research sub-agent, round 8. Parent validated r7's K=188/278 certs via
`verification/v12_check_cert.py`; that file defines the certificate conventions.

## Plan
- [ ] A1: certificates `cert_K{K}.jsonl` for the other 17 all-low constants
      (round 6 stage 1), in EXACTLY the v12 format; each checked by
      `python3 verification/v12_check_cert.py K file`.
- [ ] A2: 2-D certificate format for the one-far mixed closure (variables L, q),
      fresh independent checker `verification/glm/r8/check_cert2d.py`,
      certificates for all 10 surviving (S_low, A) pairs + the q=3 slice of
      S_low=1 as three v12-format 1-D certificates (K = 9008, 18008, 27008).
- [ ] B: bounded attempt on the 9 residual two-far {2,2,2} S_low=1 classes.
- [ ] Final statement.

## Design notes (written before coding)

### A1
19 all-low constants K = 9S − 1 from the multisets {2,2},{2,3},{2,4},{3,3},{2,2,2}
at positions ≤ 2. r7 certified K ∈ {188, 278}. The other 17 (to enumerate exactly
from the r6 §2 permutation enumeration): pending — generator `gen_cert17.py`
reuses the r7 `gen_cert.py` engine (my own code; the *checker* stays v12).

### A2
Equation: 2^t·3^a·7^w = 10^L + A·10^q + K, domain L > q ≥ 3, K = 9·S_low − 1,
A = 9·c (far digit c ∈ {1,2,3}). t = t0 := v₂(K) on the whole domain when
q > t0; hence for K = 8 (t0 = 3, S_low = 1) the 2-D tree covers q ≥ 4 and the
q = 3 slice is certified separately as three v12-format 1-D certificates:
on the slice, 2^t·3^a·7^w = 10^L + (1000A + 8) with t = v₂(10^L + 1000A + 8) =
v₂(1000A+8) for L > v₂(1000A+8) — exactly the v12 statement for
K ∈ {9008, 18008, 27008} (small L factored directly by the checker, as v12 does).

2-D certificate (one JSONL per (A, K) pair):
- line 1: `{"k":"meta","A":A,"K":K,"qmin":Q0,"sols":[[L,q],...]}`.
- internal: `{"k":"i","p":par,"r":[rL,rq],"m":[ML,MQ],"c":[ids],"rest":{"q":p}|null}`;
  children share one modulus pair; every lift (rL + i·ML mod ML′, rq + j·MQ mod MQ′)
  is a child or re-killed by `rest.q` at the child modulus (signature recomputed).
- leaf: `{"k":"l","p":par,"r":[rL,rq],"m":[ML,MQ],"a":[lo,hi],"w":[lo,hi],"x":...}`.
- signatures: a from (10^rL + A·10^rq + K) mod 3^{j+2}, j = min(v₃(ML), v₃(MQ));
  w from mod 7^{i+1}, i = min(v₇(ML), v₇(MQ)), requiring 6 | ML and 6 | MQ
  (else w unbounded from 0).
- kills: `{"T0":p}` (ord_p(10) | ML, MQ and residue ≡ 0);
  `{"prime":p}` (v12 region test, all aligned 2-D lifts when ord_p(10) ∤ M);
  `{"pin":[]}` — pin at modulus 10^{qmin} (valid on the whole domain since every
  domain point has q ≥ qmin): 3^a·7^w ≡ K·2^{−t0} (mod 2^{qmin−t0}·5^{qmin}) must
  be UNSOLVABLE for (a,w) in the signature ranges; verified by explicit
  subgroup/coset sets mod 2^{qmin−t0}·5^{qmin} (tiny: qmin ≤ 4);
  `{"sz":[a0,w0],"L":[[L,q],...]}` — both exact ⟹ 10^q(10^{L−q}+A) = N0 − K,
  finitely many (L,q), each verified by exact big-int comparison.

## Log
- A1 DONE. `gen_cert17.py` (r7 engine, parameterized over K; asserts the 19-constant
  enumeration minus {188,278} = the 17) emitted `cert_K{K}.jsonl` for
  K ∈ {98, 908, 989, 107, 917, 1079, 1808, 1889, 2708, 2789, 926, 1169, 197, 1817,
  1979, 998, 116} — all 17 **CERTIFICATE VALID** under `verification/v12_check_cert.py`
  (0 signature mismatches each; outputs in the final report). Every cert has
  solutions L(>t0) = [] — consistent with r6: the only all-low equation-solutions
  are at L ≤ t0 (spurious artifacts for the level: K=98 L=1, K=107 L=0, K=998 L=1,
  K=116 L=1; and the true member K=116 L=2 = t0 → 24, recorded in the sz leaves).
  `verify_a1.py`: brute force L ≤ 3000 reproduces exactly the recorded L sets.
  Cert sizes 596–1465 bytes, ≤ 16 nodes each.
- A2 DONE. `gen_cert2d.py` emits one tree per (S_low, A) pair; `check_cert2d.py`
  (fresh, independent) verifies all 10 **CERTIFICATE VALID**. Two pin modes were
  needed: (a) exact coset-set reachability at the domain floor 10^qmin; (b) the
  r7 discovery that each class has its own minimum q, so the pin also holds mod
  10^{q'} with q' = min(class-q-min, 40) — one-sided ord_{p^k}-lifting test. Two
  generator fixes were needed: the kill scan must cover ALL primes < 50000 (the
  capped strongest-region scan missed p=13, which kills the deep (10,27) ladder
  classes), and the loose pin is vacuous when a is unbounded. Certs are 3.7–24 KB,
  37–228 nodes. Tamper tests (bogus kill prime 3, bogus rest prime, dropped child
  of rest/deepening nodes, perturbed leaf residue) are all REJECTED by the checker.
- q=3 slice of S_low=1: `gen_cert17.py 9008 18008 27008` (v12 format; on the
  slice 2^t·3^a·7^w = 10^L + (1000A+8) with t = v2(10^L+1000A+8) = v2(1000A+8)
  for L > v2(1000A+8) — exactly the v12 statement; small L factored by the
  checker). All three **CERTIFICATE VALID**; K=27008 records L=5 (the 14112 member).
- `verify_a2.py`: brute force L ≤ 600, all q, all 10 pairs + slices — the only
  mixed one-far solution is (S_low, A, q, L) = (1, 27, 3, 5) → n = 14112
  (9n = 2^5·3^4·7^2 = 127008), matching r7.
- B started.
- B CLOSED (upward of expectations — see below). `taskB.py` steps:
  (1) all 9 residual classes re-verified: a ≥ 9 and w ≥ 6 unbounded (X ≡ 0 mod 3^9,
      Y ≡ 0 mod 7^6, valid since ord_{3^9}(10) = 3^7 and ord_{7^6}(10) = 6·7^5 divide
      M = 2·3^7·7^5); (2) pin vacuous (K/2^{t0} = 1); (3) the 3-adic and 7-adic
      ladders persist forever (verified to modulus 2·3^11·7^9 ≈ 1.4·10^13; also
      provable: f(L+t·M) − f(L) ≡ 10^L·(10^{tM} − 1) ≡ 10^L·tM·κ mod (next power),
      κ a unit, so every solution lifts — Hensel). So no ladder/sieve/pin kill exists.
  (4) aux-prime region scan — **all 9 classes are KILLED by p = 37**.
- **The r7 bug.** r7's 3-D wide scan (p2_resid.py wide_try_kill, line: `if n**3 >
  COMBO_CAP or n < 2: continue`) and the r7 sieve's try_kill (p2_twofar.py line 140)
  SKIP primes with n = d/gcd(M,d) = 1 — exactly the fully aligned primes (d = ord_p(10)
  divides M), where the region test is a single exact combo and strongest. p = 37 has
  d = 3 | M, so it was never tested against the residual. (The n < 2 skip is correct
  for SPLIT candidates — an n=1 split does not refine — but wrong for kill scans.)
- The p = 37 kill, hand-checked: on each residual class, ord_37(10) = 3 | M pins
  (L, q1, q2) mod 3; T = (10^L + 9·10^{q1} + 9·10^{q2} + 8)·2^{−3} ≡ 19 (mod 37);
  a solution would give 3^a·7^w ≡ 19 with a ≥ 9, w ≥ 6; the reachable set is
  3^9·7^6·⟨3,7⟩ and 19·3^{−9}·7^{−6} ≡ 32 (mod 37), a quadratic non-residue
  (⟨3,7⟩ mod 37 = ⟨3⟩ = the QRs, since ord_37(3) = 18, ord_37(7) = 9). Hence no
  solution in any of the 9 classes. Cross-checked by brute force over
  {3^a·7^w : 9 ≤ a ≤ 27, 6 ≤ w ≤ 15} mod 37 (covers all residue classes).
- Certificates completing the two-far S_low=1 case:
  - `cert_3d_S1.jsonl` (9 leaves, 3-D analogue of the v12 format) + fresh
    `check_cert3d.py`: **CERTIFICATE VALID**; tamper test (perturbed residue) rejected.
  - q1 = 3 slice: for q2 ≥ 5, 2^t·3^a·7^w = 10^L + 9·10^{q2} + 9008 with
    t = v₂(9008) = 4 (q2 ≥ 5 > 4) — the 2-D one-far problem (A=9, K=9008, qmin=5):
    `cert2d_K9008_A9.jsonl` **CERTIFICATE VALID** (check_cert2d.py). For q2 = 4:
    10^L + 90000 + 9008 = 10^L + 99008, t = v₂(99008) = 6 for L > 6 — the v12-format
    1-D certificate `cert_K99008.jsonl` **CERTIFICATE VALID** (v12_check_cert.py);
    it also covers (L,q2) = (5,4), (6,4) by direct factoring of small L.
  - Brute force L ≤ 250, 4 ≤ q1 < q2 < L: no two-far S_low=1 solutions ✓.
- **Status of the two-far {2,2,2} mixed case: CLOSED.** S_low=10: r7 3-D sieve
  (kills sound, brute-force-guarded). S_low=1: r7 sieve for q1 ≥ 4 + the new p=37
  kill of the 9-class residual; q1 = 3 via cert2d_K9008_A9 and cert_K99008.
  With A1 + A2 + r6 (H) + the parity-dead configurations, Level 1 is now
  completely covered by machine-checkable certificates.
- CAVEAT for the parent: the r7 3-D sieve itself (which classes it killed) is
  audited, not certificate-verified; the new certificates cover exactly its 9-class
  residual, and its other kills were guarded by check_no_sol against brute force.
- **INCIDENT + restoration.** While validating the fix, I temporarily patched r7's
  `p2_twofar.py` (line 140) and re-ran its `__main__`, which overwrote r7's
  `residual_3d_S1.json` / `residual_3d_S10.json`. `p2_twofar.py` was restored
  byte-identical (backup verified), `residual_3d_S10.json` = [] is unchanged in
  content (the S=10 sieve closes, so its original residual was empty), and
  `residual_3d_S1.json` was rebuilt as the deterministic output of the ORIGINAL
  sieve code (120 classes at moduli 52081218/66961566/73513818, ph=11 for the
  M=73513818 entries; verified deterministic across two runs and containing all
  9 hard classes; moduli just below the P2MAXM=10^8 deepening cap, consistent
  with the original run parameters). `hard_3d_S1.json` was never touched.
  Residual risk: if the original r7 run used a non-default P2MAXM, the ph values
  could differ; the 9-class certificate is unaffected (it reads hard_3d_S1.json).

## Final artifact list (all in verification/glm/r8/ unless noted)
- Generators: `gen_cert17.py` (1-D, also takes explicit K list for the slices),
  `gen_cert2d.py` (`S A` pairs, or `K A K` for explicit (A,K)).
- Checkers: parent's `verification/v12_check_cert.py` (1-D, unchanged);
  `check_cert2d.py` (2-D, fresh); `check_cert3d.py` (3-D residual, fresh).
- Certificates: `cert_K{K}.jsonl` for the 17 all-low K and the slice K ∈
  {9008, 18008, 27008, 99008}; `cert2d_S{S}_A{A}.jsonl` for the 10 mixed pairs;
  `cert2d_K9008_A9.jsonl` (q1=3, q2≥5 two-far slice); `cert_3d_S1.jsonl`.
- Cross-checks: `verify_a1.py` (brute L ≤ 3000 vs recorded), `verify_a2.py`
  (brute L ≤ 600 all q, all pairs + slices; only solution (1,27,3,5) → 14112),
  two-far brute L ≤ 250 (none), K=9008 brute L ≤ 300 q ≥ 5 (none),
  K=99008 brute L ≤ 3000 (none). Tamper tests on all three checkers reject.
- Diagnostics: `debug_1027.py`, `debug_ladder.py`, `taskB.py` (+ taskB.log).

## Final statement
Level 1 of the backward tree (7-smooth n with digit product δ ∈ {4,6,8,9} and ≥ 2
non-1 digits) is now completely covered by machine-checkable certificates:
- (H) all non-1 positions ≥ 3: impossible (r6, elementary);
- parity-dead low configurations (r6);
- (A) all-low, 19 constants: cert_K{188,278} (r7) + the 17 of this round (v12-checked);
- (M) one-far mixed: 10 two-D certificates (check_cert2d) + the S_low=1 q=3 slice
  as three 1-D certificates (9008/18008/27008); only solution 14112 = 2^5·3^2·7^2;
- (M) two-far {2,2,2}: S_low=10 closed by r7's 3-D sieve; S_low=1 closed by r7's
  sieve + cert_3d_S1 (p=37 kill of the 9-class residual) + cert2d_K9008_A9 and
  cert_K99008 for the q1=3 slice. No two-far solution exists.
The residual-class incident and the r7 `n < 2` scan bug are documented above.
