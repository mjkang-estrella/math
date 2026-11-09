# Round 7 — certificates for (A) K=188/278, and the mixed residual (M*)

**Role:** research sub-agent, round 7. Reuses round-6 code in `verification/glm/r6/`.

## Plan
- [ ] Part 1: machine-checkable certificate for the (A) sieve, K = 188 and K = 278
      (`verification/glm/r7/gen_cert.py` -> `cert_K188.jsonl`, `cert_K278.jsonl`),
      independent checker `check_cert.py` (no sieve code reuse).
- [ ] Part 2: mixed residual (M*), all (S_low, A) pairs; brute force ground truth;
      two-variable sieve; both-exact size resolution; two-far {2,2,2} case last.
- [ ] Final statement.

## Part 1 — certificate design (written before coding)

Equation being certified: 10^L + K = 2^t·3^a·7^w, K ∈ {188, 278}, t0 = v2(K).
"Solution" at L ⟺ 10^L+K is {2,3,7}-smooth. Known equation-solutions:
K=188: L=0 (189=3^3·7), L=2 (288=2^5·3^2), L=6 (2^2·3^6·7^3);
K=278: L=1 (288), L=2 (378=2·3^3·7).

**Signature recomputation (checker-independent, no ladders).** For a class
{rho mod M} with 6 | M, j = v3(M), i = v7(M):
- ord_{3^{j+2}}(10) = 3^j | M and ord_{7^{i+1}}(10) = 6·7^i | M, so
  10^L+K ≡ 10^rho+K (mod 3^{j+2}) and (mod 7^{i+1}) for every L ≡ rho (mod M).
- X = (10^rho+K) mod 3^{j+2}: a = v3(X) if v3(X) ≤ j+1, else a ≥ j+2 unbounded.
- Y = (10^rho+K) mod 7^{i+1}: w = v7(Y) if v7(Y) ≤ i, else w ≥ i+1 unbounded.

**Kill reasons (all recomputed directly by the checker):**
- {"T0": q}: q prime ∉ {2,3,5,7}, 10^rho+K ≡ 0 (mod q), ord_q(10) | M ⟹ q | 10^L+K
  for every L in class, but q ∤ 2^t·3^a·7^w. Valid for ALL L ≥ 0 in the class.
- {"prime": q}: for every gg ∈ [0, ord_q(10)) with gg ≡ rho (mod gcd(M, d)), d = ord_q(10):
  T(gg) = (10^gg+K)·2^{-t0} mod q; x = T·3^{-a_lo}·7^{-w_lo} must lie OUTSIDE the
  subgroup forced by the signature (⟨3,7⟩ / ⟨3⟩ / ⟨7⟩ / {1}); T ≡ 0 also kills.
  Needs the lemma L > t0 ⟹ v2(10^L+K) = t0 (checker verifies it once). For the at
  most one L0 ≤ t0 in the class, the checker factors 10^L0+K directly: it must not
  be {2,3,7}-smooth.
- {"exact_size": [a0, w0], "L": [...]}: signature both exact. Any solution with
  L > t0 forces 10^L+K = N0 := 2^{t0}·3^{a0}·7^{w0} exactly, i.e.
  10^L ∈ (N0−K, N0]; finite candidates, checked by exact big-int comparison.
  L0 ≤ t0 in the class: factored directly; smooth ones must be recorded in L.

**Partition:** tree. Root {0 mod 1}; internal node (rho, M) lists children, all of
one modulus M_c = M·mult, residues exactly {rho + k·M mod M_c : k < mult}.
Split-by-prime q (d = ord_q(10), g = gcd(M,d)) creates d/g children mod M·d/g;
children killed by q at split time are compressed into ONE "rest" leaf stored on
the parent (checker re-derives each killed child via CRT and re-verifies the kill).

## Log
- Part 1 DONE. `gen_cert.py` (kill-first DFS sieve, direct-method signatures) produced
  tiny trees:
  - `cert_K188.jsonl`: 45 nodes (31 leaves, 13 rest-killed splits), 4 087 bytes.
    Recorded equation-solutions L = 0, 2, 6 (n = 21, 32, 111132; the family members
    are 32 and 111132 — L=0 gives n=21, δ=2 with ONE non-1 digit, outside (A)).
  - `cert_K278.jsonl`: 17 nodes (11 leaves, 5 rest-killed splits), 1 464 bytes.
    Recorded equation-solutions L = 1, 2 (n = 32 spurious-in-family, 42).
  - `check_cert.py` (fully independent: fresh ord/subgroup/signature code, verifies
    tree coverage, recomputes a_sig/w_sig from 10^rho+K mod 3^{j+2}/mod 7^{i+1},
    re-verifies every kill incl. rest subclasses and small-L<=t0 factoring): PASS both.
  - `verify_against_brute.py`: tree walk L ≤ 2000 matches brute-force smoothness
    exactly (K=188: solutions {0,2,6}; K=278: {1,2}); modular signature spot checks
    and region-soundness (13 761 exponent pairs) all OK.
  - Note: no {"T0"} leaves occur (exact-size/region kills fire first in the DFS);
    the reason type is implemented and checker-verified regardless.
- Part 2 started.

## Part 2 — the mixed residual (M*)

Setup: 9n = 10^L + A·10^q + K, K = 9S_low − 1, n = 2^t 3^{a−2} 7^w, L > q ≥ 3.
t = t0 := v₂(K) requires q > t0; hence S_low = 1 (K=8, t0=3) needs q ≥ 4 in the
pair sieve, with q = 3 handled separately. Surviving (S_low, A) pairs (10):
(1,9),(10,9),(1,18),(10,18),(1,27),(10,27),(30,27),(11,9),(101,9),(110,9).

### Machinery (p2_sieve.py)
Class = (rho mod ML, kappa mod MQ). j = min(v₃(ML), v₃(MQ)), i = min(v₇(ML), v₇(MQ));
signature from (10^rho + A·10^kappa + K) mod 3^{j+2} / mod 7^{i+1} (uniform because
ord_{3^{j+2}}(10) = 3^j and ord_{7^{i+1}}(10) = 6·7^i divide both ML and MQ).
Kills, all brute-force-cross-checked (no FALSE KILL assertions fired):
- T0: p | RHS on the whole class (ord_p(10) | ML and MQ);
- region test at aux prime p over all aligned (L mod d, q mod d) pairs, d = ord_p(10);
- pin 2^{t0}3^a7^w ≡ K (mod 10^{qmin}) — valid because 10^L, A·10^q vanish mod 10^q —
  applied at q' = min(qmin, 40) (the pin holds mod 10^{q'} for every q' ≤ qmin!);
  mod 2 the congruence is divided through: 3^a7^w ≡ K/2^{t0} mod 2^{q'−t0};
- exact-size: a,w both exact ⟹ 10^q(10^{L−q} + A) = N0 − K, N0 = 2^{t0}3^{a0}7^{w0};
  finitely many (L,q), each verified by exact big-int comparison.
Deepening ×3/×7 on the coordinate with smaller valuation; prime splits available
but not needed for the 2-D sieve.

### Results, one-far (all 10 pairs): CLOSED
Every class killed (typical split: size 21, pin 13, prime 2 of 36 root classes);
recorded solutions empty everywhere; brute force (L ≤ 800, all q) agrees and shows
the only one-far solution overall is (S_low,A,q,L) = (1,27,3,5) → 14112.

### The q = 3 slice for S_low = 1 (p2_q3.py)
t = v₂(10^L + A·10^3 + 8) is piecewise explicit: A=9: t=6 (L=4), t=4 (L≥5);
A=18: t=3 (all L); A=27: t=4,5,6,16 (L=4..7), t=7 (L≥8). Verified for L < 150.
Each piece reduced to finitely many direct L plus a 1-D sieve (t pinned).
Result: A=9,18: no solutions; A=27: exactly L=5 → n=14112 (t,a,w)=(5,4,2).

### Two-far {2,2,2} (p2_twofar.py): 9n = 10^L + 9·10^{q1} + 9·10^{q2} + K
- S_low = 10 (t0=0, t=0 for all q1 ≥ 1): 3-D sieve FULLY CLOSED.
- S_low = 1: q1 ≥ 4 (t=3 pinned): 3-D sieve closes except 9 classes;
  q1 = 3: (L,q2)=(5,4),(6,4) direct-dead; q2=4, L≥7 (t=6): 1-D sieve CLOSED;
  q2 ≥ 5 (t=4, K=9008): 2-D sieve CLOSED.
- The 9 surviving S_low=1 classes (hard_3d_S1.json): all mod M = 2·3^7·7^5 = 73 513 818,
  signature a ≥ 9 unbounded AND w ≥ 6 unbounded:
  (L,q1,q2) ≡ (21060654, 50012047, 2349901), (21060654, 25507441, 2349901),
  (21060654, 1002835, 2349901), (10558680, 50012047, 16129), (10558680, 25507441, 16129),
  (10558680, 1002835, 16129), (14004150, 49681404, 47633), (14004150, 25176798, 47633),
  (14004150, 672192, 47633)  (mod 73513818).
- Why they resist: (i) a and w are both unbounded on them (they sit on the 3-adic and
  7-adic ladders simultaneously — deepening produces exact-a/w siblings that die, but
  the on-ladder child persists), so the region test has three free coordinates and
  always finds an aligned combo inside ⟨3,7⟩ mod p (wide scan: ALL primes < 50000,
  (d/g)³ ≤ 4096 combos); (ii) the pin is vacuous for S_low=1: K/2^{t0} = 1 ∈ every
  subgroup, and ⟨3,7⟩ = all odd residues mod 2^k; (iii) any solution in them would
  have q1 ≥ 672 192 and L > q2 > q1 — far beyond brute force.
- Brute force (L ≤ 250): no two-far solutions in either S_low.
