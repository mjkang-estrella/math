# W014 Card C paired sum/difference exponents: independent review

2026-10-09 UTC (2026-10-08 local). **Verified complete factoring improvement: NONE.**

**Disposition: reject Card C as an asymptotic route. Its identities are correct,
with three corrections.** The displayed coupled-rectangle search never saves
work. Any form of it with global (mod N) giants is dominated, block by block,
by Shanks BSGS on the single coordinate S=p+q. That is the known Pollard /
McKee–Pinch / Hittmeir (2018) N^(1/4) route. Two of the rectangle schedules
cost more than that:

| schedule (balanced semiprime, block p-range ~ sqrt(N)) | best exponent of N |
|---|---|
| independent 2-D BSGS per block (§4.2) | 5/12 |
| one shared baby table in hbase^e, giants over all (h,k) (§4.3) | 2/7 |
| single BSGS on S (prior art; §4.4) | 1/4 |
| component-collision consumer, W013 / Harvey (prior art) | 1/5 |

The torus coordinate never shortens the global search (§3.3). At the inert
prime, it gives the same information as Fermat in G, with p replaced by −1 (§5).
The missing computation and one priced changed operation are in §6. These
exponents describe the costs of specific recipes. They are not lower bounds
for factoring.

## 1. Review objects, scope and evidence

- Frozen inputs (exact bytes and SHA-256 values are in
  [inputs-manifest](W014-paired-exponent-review-evidence/inputs-manifest.json)):
  - the original brief, `brief.txt`, SHA-256
    `3e083ce89434b3fa0ec30f4084d18ea0b6e6e40dc780ffd08727be33707b706b`;
  - `research/hypotheses/W014.md`, SHA-256
    `aef28d3145145d1720e4c31a1ad7d526d74654777c09cbd9fa3c5d24e30b409d`;
  - AGENTS, RESEARCH_TEAM, RESEARCH_LOOP, README and SPECIFICATION;
  - the W013 consumer note, used only as the stated prior finding;
  - Harvey's arXiv 2010.05450 HTML, re-frozen byte-identical to the W013
    review copy (`bcd347a9…`).
- Only Card C (W014.md lines 156–223) was audited. A, B and W013 were not
  re-audited.
- Scope is semiprimes N=pq with distinct odd primes, unless a passage says
  otherwise. §7 covers arbitrary composites.
- Cost model: one operation in (Z/NZ)^* or in R=(Z/NZ)[t]/(t^2−d) costs
  poly(log N). Sorting or hashing a list of n tagged elements costs
  n·poly(log N). Exponents have polynomial bit length. "≈" hides poly(log N)
  factors and constants that depend only on the factor-ratio bound κ.
- A fixed exact algebra certificate was preregistered and run once
  ([preregistration](W014-paired-exponent-review-evidence/preregistration.md)).
  - That preregistered run **exited 1**. Its output is retained unchanged
    (§8).
  - The failures were certificate design errors, not mathematical failures.
    A separately labelled post-hoc script repeats only those checks with
    corrected domains and exits 0.
  - No timing run and no parameter sweep was performed.

## 2. Identities: verified, with corrections

Let gcd(d,N)=1 and Jacobi(d,N)=−1. Then (d/p)(d/q)=−1. Name p the inert prime,
(d/p)=−1, and q the split prime.

1. **Structure of R.**
   - R/p ≅ F_{p^2}, because t^2−d is irreducible mod p. Frobenius sends t to
     t^p = d^((p−1)/2)·t = −t, so it is conjugation.
   - R/q ≅ F_q×F_q via t ↦ (s,−s), where s^2≡d mod q.
2. **z is well defined and has norm 1.** Norm(a−t)=a^2−d, so a−t is invertible
   iff a^2−d is a unit. Norm(z)=(a^2−d)/(a^2−d)=1.
3. **Local orders.**
   - Mod p: z^p = z̄ = z^(−1), so z^(p+1)=1. This is the Lehmer theorem
     quoted by Williams (§2): V_{(p−ε)m} ≡ 2Q^m, with ε=−1 and Q=1.
   - Mod q: z ↦ (w,w^(−1)) with w=(a+s)/(a−s) ∈ F_q^*, so z^(q−1)=1.
4. **The two global identities.**
   - N−1−(p−q)=(p+1)(q−1). Therefore z^(N−1)=z^(p−q) mod p and mod q, and
     globally by CRT.
   - N+1−(p+q)=(p−1)(q−1). Therefore u^(N+1)=u^(p+q) for every unit u.
     This is Hittmeir 2018, Lemma 2.2, read in the primary source.
   - (C1) follows, and so does S^2−D^2=4N. Recovering the factors from S is
     Hittmeir 2018, Lemma 2.1, which uses the same D.
5. **Orientation.** D is p_inert − p_split, and its sign is unknown. The
   algorithm must search a signed D interval, or search |D| against both z
   and z^(−1). S and D are both even, which halves either search.

**Correction 1: gcd failure modes.** gcd(a^2−d,N) is always 1 or q (the split
prime). It is never p and never N.
- Mod p, a^2≡d is impossible because d is a non-residue there.
- So "gcd=N is a failed sample" (W014.md l.195) cannot happen. Every nonunit
  denominator is a proper factor, which occurs with probability 2/q per
  sample.
- Certificate A2 confirms this exhaustively for the fixed small cases:
  6298 values of a, gcd ∈ {1,q} every time.
- Sampling d: a d with 1<gcd(d,N)<N is a factor. Units with Jacobi −1 make up
  exactly φ(N)/2 of all units. The expected number of samples is about 2,
  each costing poly(log N).

**Correction 2: a=0 gives z=−1, of order 2.**
- At p, the Cayley map a ↦ (a+t)/(a−t) is a bijection from F_p onto
  T_{p+1}∖{1}, and a=0 maps to −1. Post-hoc check P-A7 confirms the
  bijection for the four cases with p ≤ 2000.
- At q, the corresponding map gives w=−1 when a=0.
- So a=0 must be excluded. The preregistered certificate drew its torus
  element from a=0 and its A10 check degenerated (§8).
- For uniform a, z is uniform on T_{p+1}∖{1} at p, and uniform on
  F_q^*∖{1}, apart from the two factor-revealing values, at q.
- **There is no large-order guarantee.** If p+1 and q−1 are smooth, every z
  has small order. In that case Williams p+1 plus p−1 already splits N.

**Correction 3: the rational-slope "order loss" is milder than stated.**
- The card says rational slopes need denominator-cleared powers "with order
  loss paid as in A". Write b·q = c0 + a·h + e′ with integer c0 nearest
  bN/X. Then

      T^b = g^(bX) · hbase^(c0) · (g^b·hbase^a)^h · hbase^(e′)      (A8)

- The e-side base is the **unpowered** hbase. A shared baby table hbase^j
  needs only ord_N(hbase) ≥ B.
- The powering of T adds only extra false matches. Each costs one
  divisibility test, because a match gives h and therefore p=X+h directly.
- The true pair always matches globally, since (A8) is exact.
- Certificates A8 and P-A8 confirm (A8) on fixed blocks.

## 3. What the global encoding actually contains

### 3.1 Classification of global public exponents

**Lemma C.** Let F be an integer polynomial, and let a,b be integers.

- *G-channel.* Suppose u^(ap+bq)=u^(F(N)) holds for all semiprimes pq and all
  units u. Then a=b and F(x)=a(x+1).
- *Torus channel.* Suppose z^(ap+bq)=z^(F(N)) holds for every element z, for
  all semiprimes with the (inert p, split q) pattern. Then b=−a and
  F(x)=a(x−1).

*Proof, G-channel.*
1. Use u of order exactly p−1 at p. Then pq≡q (mod p−1), so
   F(q) ≡ a+bq (mod p−1).
2. Fix q and let p grow. Then F(q)=a+bq as integers.
3. This holds for infinitely many q, so F(x)=a+bx.
4. By symmetry (mod q−1), F(x)=b+ax. Hence a=b.

*Proof, torus channel.*
1. Mod p+1 we have p≡−1 and N≡−q. So F(−q) ≡ −a+bq, which gives
   F(x)=−a−bx.
2. Mod q−1 we have F(p) ≡ ap+b, which gives F(x)=b+ax.
3. Hence b=−a and F(x)=a(x−1). ∎

So, in these two groups, the only global identities with public exponents
are multiples of S (in G) and multiples of D (in this torus).

- The patterns (−,−) and (+,+) have Jacobi +1 and are indistinguishable
  without factoring. There, z^(N+1)=z^(∓S), with the sign unknown. That
  again only gives S.
- Lehman / Harvey linear forms aq+bp with a≠±b have public exponents only
  **modulo p**: α^(aq+bp) ≡ α^(aN+b) (mod p) (Harvey–Hittmeir 2021, §1, read).
- (C1) puts S and D into two independent groups. No single cyclic group
  carries ap+bq globally.

The preregistered A10 checked this over a,b,α,β ∈ {−2..2}:
- G survivors were exactly a=b=α=β.
- The torus check was invalid because it used z=−1 (§8).
- Post-hoc P-A10, using three z with a ∈ {1,2,3}, found survivors exactly
  (a,−a,−a,a).

This finite check illustrates the proof; it does not replace it.

### 3.2 Either coordinate alone factors N

S determines D up to sign, and D determines S. The pair (S,D) has one degree
of freedom: the point p on the hyperbola. The pair constraint S^2−D^2=4N
contributes nothing that S alone lacks, beyond the residue restrictions
Hittmeir already extracts from pq=N (§4.4).

### 3.3 The D coordinate is always the longer search

Let both factors lie in [sqrt(N)/κ, κ·sqrt(N)].

- S ranges over an interval of length L_S = (√κ−1/√κ)^2·sqrt(N).
- The signed D ranges over an interval of length L_D = 2(κ−1/κ)·sqrt(N).
- L_S/L_D = (√κ−1/√κ) / (2(√κ+1/√κ)), which is less than 1/2.

Near the diagonal, S−2√N = D^2/(S+2√N) is quadratically smaller than |D|.
So the "near-diagonal D" special family (W014.md l.203) is better served by S.
That is Fermat's method, not a torus gain.

## 4. Full cost of the displayed coupled rectangle search

### 4.1 Setup and line-approximation error

Parameterize by the larger factor P = X+h, with 0≤h<H and X≥√N.
- If p is the larger factor, the equation is T=g^P·hbase^Q.
- Otherwise it is T=hbase^P·g^Q, where g=(u,z), hbase=(u,z^(−1)), Q=N/P.
- Running both role assignments costs a factor of 2.

The block offset h is a genuine unknown. Approximate Q along the block as
follows.

- **Integer slope c.** The error is about dist(N/X^2, Z)·H + N·H^2/X^3. This
  is generically Θ(H), so it is useless.
- **Rational slope a/b, with b ≤ Q0 chosen by Dirichlet** so that
  |a + bN/X^2| ≤ 1/Q0, and c0 the nearest integer to bN/X. Using the exact
  reciprocal remainder,

      |e′| ≤ E′ = 1/2 + H/Q0 + Q0·N·H^2/X^3.

  - At X ≍ √N the last term is about Q0·H^2/X.
  - Taking Q0 ≍ (X/H)^(1/2) gives E′ ≍ 1 + H^(3/2)/X^(1/2).
  - This is the same error budget as W013's linear certificates.
  - The continued-fraction acquisition per block costs poly(log N).

K = L/H blocks cover a factor range of length L ≍ X ≍ √N.

### 4.2 Independent 2-D BSGS per block

Each block is a 2-dimensional DLP in the sense of Galbraith–Ruprai,
Definition 1. Its BSGS (Matsuo–Chao–Tsujii, as cited there) costs
O(sqrt(H·(2E′+1))) group operations, plus sorting. The total is

    Σ_i sqrt(H·(2E′+1)) ≈ (X/H)·sqrt(H·max(1, H^(3/2)/X^(1/2))).

- For H ≤ X^(1/3), the total is X/√H.
- Otherwise it is X^(3/4)·H^(1/4).
- The minimum is at H ≍ X^(1/3), giving X^(5/6) = **N^(5/12)**.

### 4.3 Shared baby table in hbase (the best global sharing available)

hbase is the same in every block and for every slope (Correction 3), so one
baby table hbase^j, 0≤j<B, serves all blocks. The giants are

    γ_(i,h,k) = T_i′ · (g_i′)^(−h) · hbase^(E′−kB),   0≤h<H, 0≤k<⌈(2E′+1)/B⌉,

where T_i′ = T^b·(g^(bX)·hbase^(c0))^(−1) and g_i′ = g^b·hbase^a.

Itemized cost:
- **Block setup:** K·poly(log N) for T^b, g^(bX), hbase^(c0), g_i′ and the
  Dirichlet slope.
- **Baby table:** B elements. Before matching, test gcd(hbase^j − 1, N)
  for each j, as in W013.
- **Giants:** Σ_i H·⌈(2E′_i+1)/B⌉, generated incrementally at one group
  operation each.
- **Matches:** if ord_N(hbase) ≥ B, at most one baby matches each giant
  globally. Each match costs one divisibility test of X+h.

The true pair always matches globally, so no prime-component batch gcd is
needed. That is the only advantage of global encoding, and it saves only
poly(log N).

If ord_N(hbase) < B, an order must first be acquired. Hittmeir 2018,
Algorithm 6.2 / Theorem 6.1 (read in outline) and Harvey–Hittmeir arXiv
2601.11131 (recorded in docs/SOURCES.md, not re-read here) return a factor
or an element of order > B. The cost is about B^(1/2) poly(log N), which is
subdominant here.

The total is

    K + B + L·(2E′+1)/B  ≥  L/H + 2·sqrt(L·(2E′+1)).

- For H ≤ X^(1/3) this is at least X^(2/3).
- Otherwise it is about X/H + X^(1/4)·H^(3/4), minimized at H ≍ X^(3/7).
- The result is X^(4/7) = **N^(2/7)**.

**The exact loss compared with W013/Harvey is the factor H in the giant
count.** W013's consumer has K + B + Σ_i(2E_i+1)/B: one exponent per block,
because Fermat at the component, p≡1 (mod p−1), removes h. That gives
X/H + X^(1/4)·H^(1/4), hence H ≍ X^(3/5) and N^(1/5). The global encoding has
to enumerate every h.

### 4.4 Dominance by the single S-coordinate search

**Lemma S.** On a block X ≤ P < X+H with X ≥ √N:
- S(x) = x+N/x is increasing, with S′ = 1−N/x^2 ∈ [0,1).
- So the block's S-values lie in an integer interval of length at most H.
  The exact width is (H−1)·(1−N/(X(X+H−1))), which is less than H−1.
- Post-hoc P-A11 checks this on fixed blocks.

Consequences:
1. A per-block S-BSGS costs about 2√H. That is at most the 2-D cost
   sqrt(H(2E′+1)) for every slope, error budget and b.
2. The blocks' S-intervals tile one interval of length L_S. A single shared
   S-BSGS costs about 2·sqrt(L_S) = 2(√κ−1/√κ)·N^(1/4).
   - It is no larger than the sum of per-block searches (concavity of the
     square root).
   - It needs no line approximation at all.
3. Hittmeir 2018, Theorem 7.1 (read) then restricts S to the modular-hyperbola
   residue sets L_{N,m}. This saves a superpolynomial-in-log factor, but not
   a power of N.

So, once collisions and verification are paid, no scheme that matches global
(mod N) elements of G×T in this block family beats S-BSGS by more than a
constant. The joint encoding saves no asymptotic work. It adds a redundant
dimension, h, which a single S coordinate removes exactly.

Not claimed:
- a generic-group lower bound for every conceivable global algorithm;
- anything about multi-instance DLP techniques (Kuhn–Struik style) beyond the
  BSGS sharing priced above, which were not checked.

## 5. Component level: the torus gives the same information as Fermat in G

**Lemma E (channel equivalence).** Let F(x,y) be an integer polynomial, and
Q=N/p at the inert prime p.
- α^F(p,Q) ≡ α^F(1,N) (mod p), because p≡1 and Q≡N mod p−1.
- z^F(p,Q) ≡ z^F(−1,−N) (mod p), because p≡−1 and Q≡−N mod p+1.

Both congruences test the **same** unknown integer F(p,Q). A small-error
certificate searches the same interval either way. The torus changes only
the modulus (p+1 instead of p−1), and therefore the order and acquisition
conditions; it does not change the search length. The pair (α,z^(±1)) only
enlarges the local order to lcm(ord_p α, ord_p z).

**Lemma D (digit lift).** In the full unit group R^*, w^p ≡ w̄ (mod p),
because Frobenius is public conjugation. Certificates A9 confirm this. So

    w^(e0 + e1·p) = w^(e0) · w̄^(e1)  (mod p).

Searching a two-digit error (e0,e1) is therefore exactly the same as running
the W013 consumer on the 2E1+1 shifted certificates A(h) − e1(X+h), with
identical shared-baby cost.

The same argument applies to p-adic digits in any cyclic degree-k extension
where p is inert. There, digit i corresponds to shifting the certificate by
e_i·(X+h)^i.

So changing the group encoding (G, the quadratic torus, F_{p^2}^*, cyclic
tori) cannot change the exponent of a component-collision search. That
exponent is fixed by the certificate budget K and Σ_i(2E_i+1).

## 6. Exact missing computation and one priced changed operation

**Missing computation (for Card C itself).** Card C needs a global giant
whose exponent does not depend on the block offset h. Lemma C shows that no
such giant exists in G×T: the only global public exponents are S and D, and
S varies with h at rate 1−N/x^2, which is nonzero off the diagonal. Removing
h requires reducing exponents at a prime component. That is the W013/Harvey
consumer, already at N^(1/5) and not new. Card C as written therefore has no
repair inside its own encoding.

**Changed operation: carry C's real coupling, the hyperbola residue
restriction, into component certificates.**

For a linear certificate A(h)=a0+a1·h, the residue of the error e mod a small
prime r is

    e − a0′ ≡ a1·x − q·N·x^(−1),       x = p mod r ∈ F_r^*.

Substituting y=a1·x turns this into y − κ/y, where κ = a1·q·N mod r. Its
image L_r(κ) has exactly (r+χ(−κ))/2 elements. (Count the points of the conic
v^2 − w^2 = −4κ; checked by hand for r=3.) This is Hittmeir's 2-to-1 S-residue
phenomenon (Theorem 7.1) transferred to certificates.

Priced operation:
- Take B ≡ 0 (mod m), with m a product of small primes.
- Re-centre each giant by a0′ mod m, so the residue set depends only on κ_i.
- Group the certificates by κ class.
- Give each class a baby table restricted to the residues in L_m(κ), of size
  B·ρ_m, where ρ_m = Π_{r|m} (r±1)/(2r).
- Giant counts are unchanged.

With C classes in use, the cost is 2·sqrt(C·ρ_m·Σ_i(2E_i+1)) + K.

- **Classes left unconstrained:** C·ρ_r = Σ over κ of |L_r(κ)|/r =
  (r−1)/2 ≥ 1 for every r≥3. That is a loss, or break-even at r=3.
- **One class forced:** fixing κ forces a1·q ≡ const (mod m) inside the
  Dirichlet step. A density heuristic, treating qθ mod m as equidistributed
  and not a theorem, inflates the slope error by μ = m^2/φ(m), and hence E′
  by √μ. The net cost factor is (μ·ρ_m^2)^(1/4):
  - with the residue sign χ(−κ)=+1, it is Π((r+1)^2/(4(r−1)))^(1/4) > 1;
  - choosing χ(−κ)=−1, it is Π((r−1)/4)^(1/4): 0.84 at r=3, 1 at r=5, and
    greater than 1 for r ≥ 7.
- So at most a constant factor can be gained (r=3), and no power of N.

The known rigorous version of this idea restricts candidates to p coprime to
m. It is a class-independent restriction, which is why it can be shared. It
gives exactly Harvey–Hittmeir 2021's (log log N)^(3/5) improvement (§1 read).

**The decisive missing input** for any power gain from this direction is a
certificate generator that keeps κ_i = a1_i·q_i·N fixed modulo m while
inflating Σ(2E_i+1) by a factor λ < Π_{r|m} 2r/(r±1). Equivalently, it must
supply approximation quality in a prescribed residue class at the cost of an
unconstrained Dirichlet approximation. Neither Card C nor any source read
supplies this. I recommend not running an experiment until such a generator
is written down with its own error bound.

## 7. Semiprime versus arbitrary composite scope

- **The identities need N=pq with distinct odd primes.**
  - For N=p^2 no Jacobi −1 symbol exists (control: 0 of 120 residues). The d
    acquisition loop would never terminate, so test for perfect powers first.
  - For N with three or more prime factors, u^(N+1)=u^(a+b) fails for typical
    splits. Control N=105, u=2: it fails for 3·35 and 5·21, and holds for
    7·15 only by coincidence (ord 12 divides 84).
- A complete splitter needs the known reductions. Remove small and even
  factors, test perfect powers in polynomial time, and handle three or more
  prime factors via a factor ≤ N^(1/3) found in N^(1/6+o(1)) time
  (Harvey–Hittmeir 2021 §1, citing Harvey 2020 Prop. 2.5; not re-proved here).
  All of these are below the N^(1/4) Card C cost.
- A prime N must also be rejected first; the semiprime identities do not
  apply to it.
- None of these reductions improves Card C.

## 8. Certificate record (all results retained)

The preregistered certificate.py ran once and **exited 1**, after 37,634
assertions.

- **Passes:** A1, A2 (6298), A3 norm, order and Frobenius (6207 each),
  A4 (6207), A5, A6, A8, A9 (260), and the A10 G-channel check.
- **Failures** (each a certificate design error, not a mathematical failure):
  - **A7 ×4:** the domain was filtered by the *global* gcd, which dropped the
    a with a^2≡d mod q. Those a are valid at p, so the image size came out as
    p−3, p−3, p−2, p−2 instead of p.
  - **A11 ×4:** these blocks started below √N, violating the lemma's own
    premise. The fifth case met the premise and passed.
  - **A10 torus:** the check used z from a=0, i.e. z=−1 (Correction 2), so
    almost every tuple "survived".
- **Observation:** with the opposite labelling, z^(N−1)=z^(q−p) held for 3 of
  55, 7 of 195, and 1 each of the larger cases. Every one is a small-order
  coincidence, illustrating the no-large-order caveat.

posthoc.py is labelled post-hoc, was not preregistered, and ran once (25 assertions). It
**exited 0**:
- P-A7: 4/4.
- P-A10: survivors exactly (a,−a,−a,a).
- P-A11 and its premise: 5/5.
- P-A6 and P-A8 with nontrivial z: 5/5.
- The recorded orders of z show how small orders occur. For example, at
  N=1005973 one value had ord_q(z)=72.

## 9. Primary prior art and exact overlap

Read in full or at the cited parts, with frozen copies:
- **Williams, "A p+1 method of factoring," Math. Comp. 39 (1982) 225–234,
  §§1–4.** The PDF fetch succeeded this time.
  - Lehmer's theorem gives the local order statement for norm-one / Lucas
    elements.
  - Williams notes the F_{p^2} interpretation (attributed to Brent).
  - The global gluing z^(N−1)=z^(p−q) does not appear there. It follows in
    one line from the CRT, and no novelty is claimed for it.
  - The LUC-cryptosystem literature, where Ψ(N)=(p+1)(q−1) appears, was not
    checked.
- **Hittmeir, arXiv 1608.08766v6 (Math. Comp. 2018), §§1–2 and §7.**
  - Lemma 2.2 is u^(N+1)=u^(p+q), and Lemma 2.1 is S^2−D^2=4N recovery.
  - Theorem 7.1 is BSGS on S with modular-hyperbola residue restriction,
    which is the real content of C's "coupled" search.
- **Harvey, arXiv 2010.05450, §1 and Remark 3.4** (frozen copy).
  - The S trick is due to Pollard 1978, §3 (secondary citation; not read).
  - McKee–Pinch turn it into a deterministic N^(1/3) algorithm (secondary
    citation; not read).
  - Remark 3.4 contrasts chunked BSGS (Hittmeir 2020) with a single sweep.
    That is the per-block versus shared question of §4.
- **Harvey–Hittmeir, arXiv 2105.11105v1, §1 and the abstract.** They use the
  component congruence α^(aq+bp) ≡ α^(aN+b) (mod p), the coprime-to-m
  candidate sieve, and the ≥3-factor reduction.
- **Galbraith–Ruprai, the IMA C&C 2009 multidimensional DLP paper, §1,
  Definition 1.** The rectangle search is their d=2 problem, with BSGS cost
  O(sqrt(Ñ1·Ñ2)) citing Matsuo–Chao–Tsujii (not read).

## 10. Report items required by RESEARCH_LOOP

- **Best supported claim:** for balanced semiprimes, Card C's global encoding
  reduces exactly to S-coordinate BSGS, N^(1/4) poly(log N) (known). The
  displayed rectangle schedules cost N^(5/12) or N^(2/7).
- **Verified improvement:** NONE.
- **Evidence for:** the identities are all correct, and global matching
  avoids the batch gcd, a poly(log N) saving.
- **Evidence against:** Lemmas C, S, E and D, and the cost comparison in
  §4.3.
- **Limitations:**
  - no generic lower bound;
  - multi-instance DLP literature not surveyed;
  - Pollard 1978, McKee–Pinch and the LUC literature not read;
  - the r=3 constant in §6 is heuristic.
- **Disposition:** rejected as an asymptotic route. The identities are
  retained as known background.
- **What could change this:** a certificate generator with fixed residue
  class at unconstrained Dirichlet cost, the λ-condition of §6, or a global
  public exponent beyond S and D, which Lemma C excludes for G and this torus.
