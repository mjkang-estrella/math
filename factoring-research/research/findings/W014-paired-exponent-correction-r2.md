# W014 Card C, round 2: corrections to the paired-exponent review

2026-10-09 UTC (2026-10-08 local). Independent follow-up review.
**Verified complete factoring improvement: NONE.**

Round 1 ([W014-paired-exponent-review.md](W014-paired-exponent-review.md))
is preserved unchanged; its hashes still verify (§11). This note corrects
it and does not erase it. Round 1's failed preregistered certificate (exit 1)
and its post-hoc checks (exit 0) remain part of the record.

**Scope.** All results below are for semiprimes N=pq with distinct odd primes,
unless stated otherwise. The cost model is the round-1 one: one operation in
G=(Z/NZ)^* or in R=(Z/NZ)[t]/(t^2−d) costs poly(log N), and hashing or sorting
n elements costs n·poly(log N). Following round 1, p is the inert prime,
(d/p)=−1, and q is the split prime. Jacobi(d,N)=−1, g=(u,z) and
hbase=(u,z^(−1)).

## 0. Ledger: what survives, what is repaired, what is unsupported

| Round-1 item | Status after round 2 |
|---|---|
| Identities z^(N−1)=z^(p−q), u^(N+1)=u^(p+q), (C1), orientation, Correction 1 (gcd(a²−d,N) ∈ {1,q}) | **Survive** |
| Correction 3 (rational slope uses the unpowered hbase, as in (A8)) | **Survives** |
| §4.2 independent per-block 2-D BSGS, N^(5/12) | **Survives**, with ceilings and feasibility added (§1.3) |
| §4.3 shared 1-D baby table, N^(2/7) | **Withdrawn.** The literal schedule costs ≥ L ≈ (κ−1)√N (§1.1) |
| A 2-D schedule sharing babies across blocks | **New, priced:** best N^(1/3) in its family (§1.4) |
| §4.4 dominance of the S-search | **Repaired.** It holds per group with an explicit +2 constant, for the priced schedule families only (§2) |
| Lemma C (linear a·p+b·q, polynomial F) | **Survives as stated**, and is **extended** to all integer polynomials f(p,q), with d allowed to vary (§3). Round 1's broader readings are **withdrawn** |
| §3.1 "only S and D are global public exponents" | **Narrowed.** True for universal integer-polynomial identities; unsupported beyond that class (§3.4) |
| Correction 2, "smooth ⇒ every z has small order" | **Wrong**, corrected in §4 |
| Correction 2, Cayley distribution | **Survives.** It is made exact under two sampling conditions (§5). The parent's "±1 excluded" holds only if gcd(a,N)=1 is also required |
| §4.3 "test gcd(hbase^j−1,N)" | **Repaired** with explicit coordinate gcds (§6) |
| §4.3 "existing routine gives order > B" | **Narrowed.** Valid for the u-coordinate (1-D table). Unsupported for 2-D pair-injectivity (§6) |
| §6 residue image (r+χ(−κ))/2 | **Survives**, with the zero cases separated (§7.1) |
| §6 re-centring cost | **Repaired**: +1 giant per block, explicit class tables (§7.2) |
| §6 μ=m²/φ(m) inflation and the r=3 constant | **Unsupported** (volume heuristic, not a theorem). The break-even condition λρ<1 is consistent (§7.3) |
| §6 "decisive missing input" (fixed-class generator) | **Downgraded.** Even an ideal generator gains only N^(o(1)) for squarefree m (§7.4) |
| §5 Lemma E/D "group encoding cannot change the exponent" | **Narrowed** to a fixed polynomial certificate in a W013-type consumer (§8) |
| §6 "Card C has no repair inside its own encoding"; §10 "rejected" | **Withdrawn as broad claims.** Replaced by the quantified statements of §§1–3 and §9 |

## 1. Objection 1: cost of the displayed schedules

### 1.1 The literal one-dimensional shared table (round-1 §4.3)

The blocks are i=1..K, each X_i ≤ P < X_i+H_i, with Σ_i H_i = L. They cover
the larger-factor range [√N, κ√N], so L ≈ (κ−1)√N. Per block, the target is

    T_i′ = F′^h · S^e,     0 ≤ h < H_i,   |e| ≤ E_i,

where (F,S)=(g,hbase) or (hbase,g) is the role pair, and F′=F^b·S^a.

Babies are S^j for 0≤j<B. Giants are T_i′·F′^(−h)·S^(E_i−kB). The exact
worst-case work for one role is

    C_1D(B) = K·c_setup + B + Σ_i H_i·⌈(2E_i+1)/B⌉ + V,

where:
- c_setup = O(log N) group operations;
- V is the number of verified candidates, each costing one division of N by
  X_i+h.

Because ⌈·⌉ ≥ 1, the giant term is at least Σ H_i = L for every B. The B
regimes are:
- B ≥ max_i(2E_i+1): exactly L giants.
- B < 2E_i+1: at least H_i·(2E_i+1)/B > H_i giants in block i.

Hence min_B C_1D ≥ L + 1. The literal schedule costs Θ(√N) group operations;
it is not N^(2/7).

**Round 1's N^(2/7) is withdrawn.** Its formula K + B + L(2E′+1)/B dropped the
ceiling. That formula is valid only when every block has 2E_i+1 ≥ B, and at
its optimum B ≫ 2E′+1, so the condition fails.

Fixed instance (K7, §10): the literal schedule generated exactly 1200 = L
giants per role and found P=10007.

**Early stop versus full coverage.** Neither role assignment is known in
advance.
- The worst case is full coverage of both roles: 2·C_1D.
- If the true block position is uniformly distributed and the roles are
  interleaved, early stop halves the expected giant count.
- Neither changes Θ(L).

**Match multiplicity.** Use a multimap keyed by the triple (U,x,y) mod N
(§6). A giant matches every baby with an equal key. Let m_max be the largest
key multiplicity. Then V ≤ (#giants)·m_max. If ord_N(u) ≥ B, the map
j ↦ hbase^j is injective on [0,B), so m_max=1 (§6).

**Construction order.** For each role, block and h, the giants come from one
multiplication by the precomputed S^(−B). Moving h by one costs one
multiplication by F′^(−1). Each block costs O(log N) operations for T^b,
F^(−bX_i) and S^(−c0_i). Memory is B keys.

### 1.2 Line error, restated

Write bQ ≈ c0_i + a·h with c0_i = round(bN/X_i). By the exact reciprocal
remainder,

    |e| ≤ E_i := 1/2 + |a + bN/X_i^2|·H + b·N·H^2/X_i^3.

With a Dirichlet slope per block (b ≤ Q0, |a+bN/X_i²| ≤ 1/Q0), the error is
E_i ≍ 1 + H^(3/2)/X^(1/2), as in round 1.

With one slope (a,b) shared across a group of blocks of total width W:
- |a + bN/X_i²| ≤ 1/Q0 + 2bNW/X³;
- at X ≍ √N, this gives E_i ≲ 1/2 + H/Q0 + b·H·(2W+H)/X;
- with b ≍ Q0 and Q0 ≍ (X/W)^(1/2), it gives E ≍ 1 + H·(W/X)^(1/2).

### 1.3 Independent per-block 2-D BSGS (round-1 §4.2): survives

Per block, take babies F′^(h1)·S^j with h1<H1 and j<B. Take giants
T_i′·F′^(−H1·h2)·S^(E_i−kB). The cost per block is

    H1·B + ⌈H/H1⌉·⌈(2E_i+1)/B⌉ ≥ 2·sqrt(H(2E_i+1)).

The bound is attained up to rounding when sqrt(H(2E+1)) ≤ H·(2E+1); that
inequality always holds. Summing, (X/H)·sqrt(H·E) is minimized at H ≍ X^(1/3).
The total is ≍ X^(5/6) = **N^(5/12)**, as in round 1.

### 1.4 New: a 2-D schedule that shares babies across blocks

A shared table needs a common F′, so one slope (a,b) must serve a whole group
of blocks of width W. Take a common baby table F′^(h1)·S^j for h1<H1≤H and
j<B, and per-block giants as in §1.3. The cost is

    C_2D = Σ_groups H1·B + Σ_blocks ⌈H/H1⌉·⌈(2E_i+1)/B⌉ + K·O(log N) + V.

It satisfies C_2D ≳ L/H + (L/W)·2·sqrt(W(2E+1)), with E from §1.2.

Optimizing over (H, W, Q0):

| Regime | Choice | Total |
|---|---|---|
| E ≍ 1 (needs H²W ≲ X) | W ≍ X/H², H ≍ X^(1/4) | ≍ X^(3/4) = N^(3/8) |
| E > 1 | W ≍ L ≍ X (Q0 ≍ 1, b=1, integer slope, E ≍ H), H ≍ X^(1/3) | ≍ X^(2/3) = **N^(1/3)** |

In the second regime the total is X/H + 2·sqrt(2XH). The feasibility
condition sqrt(W(2E+1)) ≤ H(2E+1) holds there: about √2·X^(2/3) ≤ 2X^(2/3).

So the best priced schedule in this family costs N^(1/3). That is better than
the per-block 2-D search and the literal 1-D search, and worse than the
S-search's N^(1/4).

This is a computed optimum over the displayed family (box babies, per-block
linear giants, one slope per group). It is not a lower bound for other baby
sets.

Fixed instance K7 (N=10007·7919, H=100, H1=10, B=16, slope (−1,1)):
- E_i = 2,4,…,22;
- 160 babies and 250 giants per role, equal to the predicted
  Σ⌈H/H1⌉⌈(2E_i+1)/B⌉;
- no duplicate baby keys;
- exactly one match and one division test in the correct role, finding
  P=10007, and zero matches in the other role.

## 2. Objection 7: dominance, constants versus exponents

Fix a group of blocks with total width W that share one table (a single block
is the case W=H).

**2-D side.** The group's giants number at least A_g/M_g, where M_g = H1·B
and A_g = Σ_{i∈g} H(2E_i+1). So

    cost_2D(g) ≥ M_g + A_g/M_g ≥ 2·sqrt(A_g),

and A_g ≥ W because 2E_i+1 ≥ 1.

**S side.** Lemma S (round 1) applies for X ≥ √N. The S-values of the group
lie in an integer interval holding n_g ≤ W candidates. A BSGS with
B=⌈√n_g⌉ costs at most 2√n_g + 2.

Therefore, with matched constants,

    cost_S(g) ≤ 2·sqrt(n_g) + 2 ≤ 2·sqrt(A_g) + 2 ≤ cost_2D(g) + 2,

plus O(log N) setup on each side. The S-side also needs no role duplication,
a further factor of 2. Round 1's literal inequality 2√H ≤ sqrt(H(2E+1))
needs 2E+1 ≥ 4 and is false at E=0. The comparison above replaces it.

**Across groups.** A single S-search over the union interval of n candidates
costs at most 2√n + 2 ≤ Σ_g 2·sqrt(n_g) + 2, by subadditivity of the square
root.

**Exponents.** S-BSGS costs ≍ (√κ−1/√κ)·N^(1/4). The priced families cost
N^(5/12), ≥ (κ−1)√N, and N^(1/3).

**Scope.** These comparisons cover only the priced schedule families
(rectangle/box-baby BSGS over (h,e) with global keys). They say nothing about
generic algorithms in G×T.

## 3. Objection 2: what Lemma C actually proves, and an extension

### 3.1 Reduction identities

Write λ(N) = lcm(p−1,q−1) and λ_T(N) = lcm(p+1,q−1), the exponent of the
torus T_d(Z/NZ) ≅ C_(p+1) × C_(q−1). Then

    N ≡ S − 1  (mod λ(N)),      N ≡ D + 1  (mod λ_T(N)),            (R)

because N−S+1 = (p−1)(q−1) and N−D−1 = (p+1)(q−1).

Consequently, for every integer polynomial F, u^F(N) = u^F(S−1) for all
units u, and z^F(N) = z^F(D+1) on the torus. A public exponent built
polynomially from N acts in G as a polynomial in S, and in T as a polynomial
in D. This is the precise content behind round 1's "only S and D".

### 3.2 Lemma C′ (all integer polynomials)

Let f ∈ Z[x,y] and F ∈ Z[y].

**G-channel.** The following are equivalent:
- (i) u^f(p,q) = u^F(pq) for every pair of distinct odd primes (p,q) and
  every unit u;
- (ii) F(y) = f(1,y) = f(y,1).

*Proof.*
- (ii)⇒(i): f(p,q) ≡ f(1,q) and F(pq) = f(1,pq) ≡ f(1,q) (mod p−1),
  because pq ≡ q. The case mod q−1 uses f(·,1) in the same way.
- (i)⇒(ii): take u with ord_p(u) = p−1. Then p−1 divides F(q) − f(1,q)
  for infinitely many p, so F(q) = f(1,q). This holds for infinitely many q,
  so it is a polynomial identity. Symmetrically, F(x) = f(x,1). ∎

Moreover, f(x,y) − f(y,x) is antisymmetric and vanishes at x=1, so it equals
(x−1)(y−1)·g(x,y) in Z[x,y]. Its contribution to u^f(p,q) is trivial. The
exponent therefore carries only symmetric information, which is a polynomial
in S and N.

**Torus channel.** The following are equivalent:
- (i) z^f(p,q) = z^F(pq) for every ordered pair of distinct odd primes
  (p,q), for some (equivalently, every) d with (d/p)=−1 and (d/q)=+1, and for
  every z ∈ T_d(Z/pqZ);
- (ii) F(y) = f(−1,−y) = f(y,1).

*Proof.* Such a d exists for every pair by CRT. The abstract group
C_(p+1) × C_(q−1) does not depend on which d is used, so d may vary with N.
- Mod p+1: p ≡ −1 and pq ≡ −q. This gives F(−q) = f(−1,q), so
  F(y) = f(−1,−y).
- Mod q−1: F(p) = f(p,1).
- The converse runs the same congruences backwards. ∎

For f = ax+by this gives b=−a and F = a(y−1), which is round 1's Lemma C.
S = x+y fails: −1−y ≠ y+1. D² = (x−y)² passes. The proof also goes through
for F ∈ Z[N,d] with d fixed; for each fixed non-square d, inert and split
primes are both infinite in number.

### 3.3 Checks

K3 confirmed the G-channel equivalence for all units of 11·13, 23·47 and
101·103:
- 15/15 identities hold, including the non-symmetric
  f = x+y+(x−1)(y−1)x;
- f = 2x+y fails for 100/120, 968/1012 and 10000/10200 units.

**Preregistered failure retained.** At N = 101·103 the torus prediction
"z^(p+q) ≠ z^(N+1) for some z" was false. There p+1 = q−1 = 102 divides
(p−1)(q−1) = N+1−S, so that one modulus satisfies an extra identity.

This was a certificate design error. It also illustrates that Lemma C′
quantifies over varying primes. A single N can satisfy additional identities.

### 3.4 What these results do not exclude

Lemma C′ and (R) classify only universal identities with integer-polynomial
exponents. They do not exclude:
1. **Non-polynomial public exponents.** Examples are isqrt(N), roundings,
   continued-fraction data and block-dependent M_i. For an arbitrary
   function of N, an integer F(N) with u^(ap+bq) = u^F(N) always exists:
   - by CRT it exists whenever a+bq ≡ b+ap modulo gcd(p−1,q−1), which
     always holds;
   - so the obstruction is computing F(N), not its existence.

   Equivalently, a global giant with small unknown e is a public M with
   M ≡ e (mod ord_N u), i.e. an approximate multiple of λ(N).
2. Identities required only on a subfamily of semiprimes (§3.3 shows that a
   single N can have extra ones).
3. Identities that hold only for elements of restricted or known order.
4. Other groups: the full R^*, higher tori and elliptic curves. One check:
   the R^* identity w^p·w̄^q = w^N·w̄ holds universally, but it is
   (C1) again.
5. Multi-instance, compression or batch techniques (Kuhn–Struik style; not
   surveyed).
6. Any generic-group or non-generic algorithm in G×T.

## 4. Objection 3: smooth order is not bounded order

Round 1 said: "If p+1 and q−1 are smooth, every z has small order." That is
**wrong.** Three properties need to be kept apart.

**Bounded order** is what BSGS injectivity needs. In a cyclic group C_n,

    #{z : ord z ≤ M} = Σ_{d|n, d≤M} φ(d) ≤ M(M+1)/2.

For z uniform on T_(p+1)∖{1} this gives
Pr[ord_p z ≤ M] ≤ M(M+1)/(2p), whether or not p+1 is smooth.

K4 tests this at p = 8191, where p+1 = 2^13. All 8191 Cayley images have
power-of-2 order. Exactly 63 have order ≤ 64, and 4096 have the maximal
order 8192.

**Smooth order** is what Williams p+1 and Pollard p−1 need. With a public
exponent E_B, z^(E_B) ≡ 1 (mod p) iff ord_p z divides E_B. For uniform z the
probability is (gcd(E_B,p+1) − 1)/p, and it equals 1 iff p+1 | E_B. The cost
is about π(B)·log B·poly(log N) operations for a paid bound B. This is a
special-family method, not a guarantee.

With Jacobi(d,N) = −1, one Lucas run tests p+1 at the inert prime and q−1 at
the split prime. Which prime plays which role is unknown. Williams §5 (read)
treats the unknown character as a ½ chance per trial (7/8 after three
trials) and describes time-sharing over many characters.

**Shared annihilation.** If E_B kills both components, then gcd = N. The fix
is to apply prime powers one at a time. That fails only if both components
first die at the same step.

K4 tests this at N = 8191·257, where both orders are powers of 2:
- all 29 valid a satisfy z^(2^13) = 1 globally;
- stepwise squaring still splits N for each of them, at the first step where
  the q-component dies (k = 5…8);
- a=23 gave gcd(a²−d,N) = 257, the split prime, as Correction 1 predicts.

The second half of round 1's sentence ("then Williams plus p−1 splits N") is
true only with a paid smoothness bound and stepwise processing.

## 5. Objection 4: exact Cayley distribution

**Split prime q.** With t ↦ s, s² ≡ d, the map is w = (a+s)/(a−s), a Möbius
map of P^1(F_q):
- s ↦ ∞, −s ↦ 0 and ∞ ↦ 1;
- **0 ↦ −1**.

So a ∈ F_q∖{±s} maps bijectively onto F_q^*∖{1}. The value −1 is attained
at the finite non-pole a ≡ 0.

The parent's statement ("±1 are excluded once a avoids ±s") therefore holds
only if gcd(a,N) = 1 is also imposed. A natural sampler may impose it,
because a ≡ 0 (mod q) reveals q.

**Inert prime p.** a ∈ F_p maps bijectively onto T_(p+1)∖{1}, and 0 ↦ −1.

**Sampling.** Draw a uniformly mod N, conditioned on gcd(a²−d, N) = 1. By CRT
the components are independent:

    (z mod p, w mod q) uniform on (T_(p+1)∖{1}) × (F_q^*∖{1}).

Additionally conditioning on gcd(a,N) = 1 gives uniform on
(T∖{±1}) × (F_q^*∖{±1}).

Excluding only a ≡ 0 (mod N) removes only the global −1. With probability
1/p, z ≡ −1 (mod p) still occurs, with order 2 at p. No sampling rule gives
a large-order guarantee; §4 supplies the probability bound. K1 confirmed every
image claim, for q ∈ {11,13,101,103} and p ∈ {7,11,103,107}.

## 6. Objection 6: coordinate extraction and order guarantees

Write hbase^j = (u^j, z^(−j)) with z^(−j) = x_j + y_j·t. For each prime ℓ | N,

    hbase^j ≡ 1 (mod ℓ)  iff  ℓ | gcd(u^j−1, x_j−1, y_j, N).

Compute the three gcds g_u = gcd(u^j−1,N), g_x = gcd(x_j−1,N) and
g_y = gcd(y_j,N) separately. Any value strictly between 1 and N is a factor.
Batch them as a product mod N with a remainder tree for localization, at cost
B·poly(log N). Hash keys are the triples (U,x,y) mod N.

K5 (N = 8191·257, j ≤ 300) confirmed the equivalence. It also shows
coordinate events that are not hbase^j ≡ 1 events. At j=16, g_y = 257 while
g_x = 1, because z^(−16) ≡ −1 (mod 257). The y-coordinate reveals q earlier.

**Order guarantees.**
- **1-D table.** ord_N(hbase) = lcm(ord_N u, ord_N z) ≥ ord_N u. Injectivity
  of j ↦ hbase^j on [0,B) therefore follows from ord_N(u) ≥ B. Hittmeir's
  Algorithm 6.2 / Theorem 6.1 (read in outline in round 1) supplies this for
  ordinary units.
- **2-D table F′^(h1)·S^j**, with F′ = (u^(a+b), z^(±(b−a))) and
  S = (u, z^(∓1)):
  - if ord_N(u) > |a+b|(H1−1) + B−1, a collision forces Δj = −(a+b)·Δh;
  - the z-coordinate then requires z^(2b·Δh) = 1 (identity verified by K6);
  - so injectivity also needs ord_N(z) ∤ 2bΔh for 0 < |Δh| < H1;
  - when a+b = 0 (as in K7), the u-coordinate of F′ is 1, and h1-injectivity
    rests entirely on z.

  **No existing routine supplies this torus guarantee unmodified.** Two
  priced substitutes:
  - (i) Random a: Pr[ord_p z ≤ M] ≤ M(M+1)/(2p) with M = 2b(H1−1).
  - (ii) Detection: a duplicate key found when building the table gives a
    known multiple n0 = 2bΔh of ord_N z. Coordinate gcds of z^(n0/ℓ) − 1,
    for each prime ℓ | n0 (trial division of n0 ≤ 2bH1), either split N or
    certify a small order. In the second case, resample a.

  A deterministic worst-case torus order routine is **unsupported**.

## 7. Objection 5: residue restriction, done exactly

### 7.1 Image classification

Take r an odd prime with r ∤ N, x = p mod r ∈ F_r^*, and the map
x ↦ a1·x − c/x with c ≡ q·N. The image size is:

| Case | Image size | Reason |
|---|---|---|
| a1·c ≠ 0 | (r + χ(−a1·c))/2 | parent's count, below |
| exactly one of a1, c is 0 | r−1 | the map is a bijection onto F_r^* |
| a1 ≡ c ≡ 0 | 1 | e ≡ a0′ (mod r) |

For a1·c ≠ 0 (κ = a1·c), a value v is attained iff y² − v·y − κ has a root in
F_r^*. The number of v with v² + 4κ = 0 is 1+χ(−κ), and Σ_v χ(v²+4κ) = −1.
That gives (r+χ(−κ))/2, which is the parent's count.

The doubly-zero case gives nothing new. If r | a1 and r | q, then (e−ε)/r,
with ε ≡ a0′, is exactly the error of the integer certificate
(a0−ε)/r + (a1/r)·h for q/r. It is a rescaling, not a gain.

K2 checked all 373 pairs (a1,c) for r ∈ {3,5,7,11,13}.

### 7.2 Re-centring with full accounting

Context: the W013 consumer, with β^j babies and component collisions. Let m
be squarefree, coprime to N, and require m | B.
- **Offset.** For block i, choose O_i ∈ [E_i, E_i+m−1] with
  O_i ≡ −a0′_i (mod m). Use giant offsets O_i in place of E_i. Then the true
  baby index satisfies j = e + O_i − kB ≡ e − a0′_i (mod m), which lies in
  L_m(κ_i).
- **Range shift.** e + O_i ∈ [0, 2E_i+m−1], so block i needs ⌈(2E_i+m)/B⌉
  giants. That is at most ⌈(2E_i+1)/B⌉ + 1 when m ≤ B+1.
- **Babies.** For each class κ, a table of residues j < B with
  j mod m ∈ L_m(κ), of size exactly B·ρ(κ). Here ρ(κ) = |L_m(κ)|/m is a
  product over r | m by CRT.
- **Collision localization.** There is one batch product and one remainder
  tree per class. Total size is unchanged, so localization costs poly(log N)
  per element plus C trees.

With C classes the cost is

    Σ_c [B·ρ_c + Σ_{i∈c} ⌈(2E_i+m)/B⌉]·poly(log N) + K·poly(log N)
      ≈ 2·sqrt(C·ρ·Σ(2E_i+1)) + 2K.

The true collision is never lost, because the restriction removes only babies
whose residues are impossible.

### 7.3 Break-even condition

Suppose a fixed-class generator inflates Σ(2E_i+1) by a factor λ.
- At fixed H, the balanced term scales by sqrt(λρ).
- Re-optimizing H in K + 2·sqrt(ρλ·c·X^(1/2)·H^(1/2)) scales the total by
  (λρ)^(2/5).

A gain therefore requires **λρ < 1**. That matches round 1's final condition
λ < Π 2r/(r±1) = 1/ρ, so the condition is consistent.

Round 1's specific λ = √μ with μ = m²/φ(m) is a lattice-volume heuristic
(φ(m) acceptable cosets among m² residue pairs (q,a1)). It is **not a
theorem** and is not adopted. So the "r=3 gives 0.84" constant is
unsupported.

### 7.4 Ceiling on the residue route (new)

For squarefree m ≤ N^c, outside the rescaling case,

    ρ_m ≥ Π_{r|m} (r−1)/(2r) ≥ 2^(−ω(m))·φ(m)/m.

Since ω(m) ≤ (1+o(1))·c·ln N / ln ln N, this gives ρ_m ≥ N^(−o(1)).

For the same blocks, the class-fixed certificates are a subset of all
certificates, so λ ≥ 1 relative to the best unconstrained choice. So even an
ideal generator (λ = 1) changes the cost by a factor of only N^(−o(1)), never
by a power of N. This is consistent with the sub-power gains
of Hittmeir 2018 Theorem 7.1 and Harvey–Hittmeir 2021.

Prime-power moduli were not analysed.

**Round 1's "decisive missing input" therefore cannot change the exponent.**
It is not recommended as the next computation.

## 8. Narrowing round-1 §5 (Lemmas E and D)

Lemma E remains correct as stated. For one fixed integer polynomial
certificate F, the unknown integer F(p,Q) is the same in G (public value
F(1,N)) and in T (public value F(−1,−N)). Changing the group changes only
the modulus and the order conditions.

Lemma D shows that the two-digit F_(p²) lift equals the shifted-certificate
family.

Round 1's broader sentence, "changing the group encoding cannot change the
exponent of a component-collision search", is withdrawn. Lemmas E and D do not
cover:
- consumers that combine different certificates across channels;
- groups other than G, T and F_(p²)^*;
- non-W013 consumers.

## 9. The missing computation and one changed operation

**Exact missing computation.** For a global (mod N, hash-matched) search to
beat N^(1/4), it needs a public, poly(log N)-time exponent family M_i(N), and
a base u of verified order, such that the residues M_i mod ord_N(u) of the
true factor fall in a set with a sumset cover A+Γ of size o(√L_S). The
computation of each M_i must be priced.

By (R), every M_i that is an integer polynomial in N reduces to a polynomial
in S. By §7.4, congruence restriction of S (or of e) shrinks the candidate set
only by N^(−o(1)). A candidate M_i must therefore be non-polynomial (block- or
rounding-dependent) and non-congruence. None is known to this review.

**Concrete changed operation, priced: the repair of Card C's own displayed
search.**
1. Keep the block decomposition.
2. Replace the 2-D rectangle and the full (U,x,y) key by the u-coordinate
   quotient.
3. For block i, form the S-interval I_i = S([X_i, X_i+H)) of n_i ≤ H integer
   candidates. Compute the giant base u^(N+1−min I_i) with O(log N)
   operations.
4. Share babies u^j, 0 ≤ j < B, with ord_N(u) ≥ B certified by the
   Hittmeir routine at cost ≈ B^(1/2)·poly(log N).
5. Use giants u^(N+1−min I_i)·u^(−kB) for 0 ≤ k < ⌈n_i/B⌉.
6. Verify each match (an S candidate) by the square test on S² − 4N:
   poly(log N) per match, at most one per giant.

The total is B + Σ_i ⌈n_i/B⌉ + K·O(log N) ≤ B + L_S/B + 2K. This is
2·sqrt(L_S) + O(K), i.e. the known Pollard / McKee–Pinch / Hittmeir
S-search, with the paired encoding removed.

It is the cheapest correct execution of Card C's idea. It leaves exactly one
open lever, the non-polynomial M_i above. The torus coordinate adds no
candidate reduction (D's interval is more than twice longer; round-1 §3.3,
unchanged).

**Recommendation to the parent.** Treat Card C's search schedules as closed
at the known N^(1/4). Retain as verified tools:
- the identities;
- (R) and Lemma C′, as a cheap symbolic screen for any future
  "global giant" proposal: reduce its exponent mod λ and mod λ_T first;
- the coordinate-gcd extraction;
- the exact Cayley sampling law.

The next exponent-level computation should come from the component-collision
line (W013 C), not from G×T global matching.

## 10. Certificate record (all results retained)

The preregistration ([preregistration.md](W014-paired-exponent-correction-r2-evidence/preregistration.md))
and certificate_r2.py were hashed before the run
(`pre-run-hashes.sha256`, 2026-10-09T00:31:56Z). The certificate ran once
with `python3 -I` (Python 3.14.7) and **exited 1**; stderr was empty.

**Passed:**

| Check | Result |
|---|---|
| K1 (4 groups) | 16/16 |
| K2 | 373/373 |
| K3_G | 15/15 |
| K3_G 2x+y failures | 3/3 |
| K4 orders | 1/1 |
| K4 shared annihilation | 1/1 |
| K5 | 1/1 |
| K6 | 3/3 |
| K7 counts | 2/2 |
| K7 found-once | 1/1 |

**Failed:** K3_T, 1 of 3. At N = 101·103, z^(p+q) = z^(N+1) held for every
sampled z (explained in §3.3). This was a design error, not a failure of the
lemma. There was no rerun and no post-hoc replacement.

No timing run and no sweep was performed. K7 is a single fixed correctness
instance; its counts are exact operation tallies, not performance evidence.

## 11. Hashes

- Inputs: `W014-paired-exponent-correction-r2-evidence/inputs.sha256`
  (39 entries). It covers:
  - the governance docs and W014.md (`aef28d31…`, unchanged from round 1);
  - the round-1 report (`acc9ed41…`);
  - the round-1 delivery manifest and sha256 list;
  - every round-1 evidence file.

  All 39 entries verified OK before writing, so round 1 is unchanged.
- Frozen copies: `frozen/` holds the docs, W014.md and the round-1 report and
  manifests. The round-2 brief is `brief-r2.txt`. The original brief is
  `frozen/round1/original-brief.txt` (`3e083ce8…`).
- Primary sources were not re-fetched. Round 1's frozen copies were re-hashed
  and match its sources manifest (Williams txt `c19d5da8…`, Hittmeir txt
  `e699b65a…`, Harvey–Hittmeir txt `01fce7e2…`). Williams §5 was re-read for
  §4.
- Delivery: `W014-paired-exponent-correction-r2-evidence/delivery.sha256`
  lists this report and every evidence file, excluding itself.

## 12. Report items required by RESEARCH_LOOP

- **Best supported claim:** for balanced semiprimes, the best correct
  execution of Card C is the known S-search, ≍ N^(1/4)·poly(log N). The
  priced paired schedules cost:
  - N^(5/12) (per block);
  - ≥ (κ−1)√N (literal 1-D shared);
  - N^(1/3) (shared-slope 2-D).
- **Verified improvement:** NONE.
- **Evidence:**
  - for: the identities, Lemma C′ and (R), and exact global verification;
  - against: §§1, 2 and 7.4, within their stated families.
- **Limitations:**
  - no generic lower bound;
  - non-polynomial global exponents, other groups and multi-instance methods
    are not excluded;
  - the torus deterministic order routine is unsupported;
  - prime-power residue moduli were not analysed;
  - the r=3 constant is heuristic.
- **Disposition:** the displayed search schedules are **rejected** as an
  asymptotic route (dominated by the known S-search). The identities are
  retained as tools. The broad "no repair" claim is withdrawn.
- **What could change this:** a priced non-polynomial, non-congruence public
  exponent family as in §9, or a 2-D baby set beating the box-baby optimum of
  §1.4 (which would still only reach the S-search cost unless the candidate
  image shrinks).
