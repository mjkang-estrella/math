# W010 Jacobi filter: independent algebra and protocol review

2026-10-08. Disposition: **equations (1)–(5) ACCEPTED with scope corrections;
counterexample to inherited drift CONFIRMED but QUALIFIED.** Verified factoring
complexity improvement: **NONE**. No reachability, rate or speedup claim.

## Scope and frozen evidence

Inputs were frozen before the audit; see
[input manifest](W010-jacobi-review-inputs-manifest.json). They are the governing
instruction files, contextual STATE, the
[frozen proposal](W010-jacobi-review-input-research--findings--W010-jacobi-asymmetry.md),
the prior [W010 review](W010-jacobi-review-input-research--findings--W010-norm-cubic-review.md)
and [disposition](W010-jacobi-review-input-research--findings--W010-norm-cubic-disposition.md).
No external primary source was needed; everything below is proved here or
certified exactly. The [certificate](W010-jacobi-review-certificate.py)
([output](W010-jacobi-review-certificate-output.json), 55/55 checks) uses
Euler's criterion and `Fraction` only, at the two named fields F_167 and F_5.
Its enumerations are limited to the 36 ordered pairs of the one fixed
six-point support, the 16 nonzero pairs of F_5, and one explicit odd fibre
assignment on F_167. It includes no candidate run, prime or weight search,
or sweep. No shared source, Lean, state, package, commit or publication.
B's Deligne-envelope task is not duplicated.

## 1. Selector, same-stage asymmetry and the no-full-gcd channel (1)

For N=pq, with p and q distinct primes >3, and a unit beta,
(beta/N)=chi_p(beta)chi_q(beta). The value −1 means exactly one component is
a nonzero square. At the nonsquare prime, P^2=beta has no solution, so
P^3−beta*P vanishes only where P does: no new roots and A=B=0 there. At the
square prime, the roots ±sqrt(beta) can be absorbed.

**(1) holds as stated.** If w^2≡beta held modulo p and modulo q, beta would be
a square at both primes, giving Jacobi +1. So gcd(w^2−beta,N)≠N for *every*
residue w, whether or not w is a unit. The masking remark is also correct. If
P(x)≡0 mod q (an old root) and P(x)^2≡beta mod p, then P_new(x)≡0 mod N. The
product gcd is then full, while the quadratic factor gives p.

Scope corrections:

* **Per stage only.** The square prime can switch between stages, and the
  Jacobi symbol does not say which prime is the square one. Endpoint roots
  can therefore come from different primes in different stages, so the
  endpoint gcd(P_k(x),N) can still be N. Using (1) at a probe means testing
  each stage's quadratic factor separately. That is up to k extra gcds per
  probe. The circuit computes those values anyway, but this is a protocol
  change from the W010 endpoint probe and must be priced.
* **N=p^2.** Every unit has Jacobi +1, so the filtered process *never
  updates*. Square inputs must be removed first, for example by a
  perfect-power test. For three or more primes, −1 means an odd number of
  nonsquare components. Then "exactly one positive" is false, though (1)
  still holds.
* **No root guarantee.** gcd≠N says nothing about how often gcd≠1 happens;
  see §5.

## 2. Equations (2)–(4): statewise CRT laws

Fix the complete current map modulo N, i.e. the stopped and frozen state.
Fresh r,s modulo N give independent field pairs at p and q. The Jacobi test
requires both beta components to be nonzero. Acceptance therefore means
chi_p(beta_p)chi_q(beta_q)=−1 on the joint legal chart. Its probability is

    C = L_(p,+)L_(q,-) + L_(p,-)L_(q,+).                         (2) ✓

On acceptance with chi_p=+1, Delta v_p=K_p−A_p. With chi_p=−1, A_p=0 and
Delta v_p=K_p. Weighting by K_pK_q gives (3) exactly. The same argument gives
Delta m_p=B_p, and B_p vanishes for nonsquare beta and for beta=0, so
E[Delta m_p]=L_(q,−)G_p ✓. D_−≥0 is trivial. ell=L_++L_−+Z ✓.

**(4) ✓**, read as a raw joint probability. The event is that both anchor
charts are legal and exactly one beta component is zero. It is not a
probability conditional on legality, which the word "after" might suggest.
Z_pZ_q is the full-gcd no-op. Also, Z_p=0 whenever chi_p(−3)=−1, because
Q(z,u)=0 then has no nonzero solutions.

Paid no-ops are illegal anchors, a full beta gcd, and Jacobi +1. Each raw
attempt costs two O(j+1) evaluations, five gcds and one Jacobi symbol. The
Jacobi symbol costs O(n^2) by reciprocity and needs no factorization.

**New coupling compared with the unfiltered process.** There, the q-state
enters the p-drift only through the positive scalar ell_q, so the drift's
sign does not depend on q. Under the filter, the *sign* of E[Delta v_p]
depends on the q-side ratio L_(q,+)/L_(q,−). If D_(p,+)<0<D_(p,−) and
L_(q,−)>0, then

    E[Delta v_p | state] < 0   iff   L_(q,+)/L_(q,-) < -D_(p,+)/D_(p,-).

Root mass m_p is still pointwise nondecreasing, so it remains a
submartingale. The total collision mass m^2+v increases by K+A+2mB≥0 on
every update. Only the *residual* potential v loses the submartingale
property established in theorem (10) of the prior review.

## 3. Equation (5): uniform start

From the accepted counts k_beta=C0−D0·chi(beta) on (p−1)/2 squares and (p−1)/2
nonsquares, and k_0=(p−1)(1+epsilon), we get L_±=(p−1)(C0∓D0)/(2p^2) and
Z=(p−1)(1+epsilon)/p^2. Their sum is (p−1)(p−3)/p^2 ✓. B=2/p exactly on
nonzero squares, so G=2L_+/p ✓. The asymptotics hold: C→1/2, the raw root
increment is ~1/(2p) (unfiltered ~1/p), and the per-accepted increment is ~1/p.

The small-prime caveat is concrete. **C0=D0, hence L_+=0, at both p=5 and
p=7.** This is (5) evaluated at those two primes, not a search. For N=35 at
the uniform start, C=0: the filter never accepts, and the only progress
channel is the beta gcd, through Z_7>0. For q≥11, C0−D0≥q−9 and
C0+D0≤q+1, so L_(q,+)/L_(q,−)≥(q−9)/(q+1)≥1/6.

## 4. The p=167, q=5 counterexample

Everything the parent states is exactly certified.

* Euler criterion mod 167: 49 and 19 are squares; 79, 37, 109 and 39 are
  nonsquares. The six parameters are distinct and nonzero. They meet the
  occupied root squares {9,25,49} only at 49. F_49(3)=F_49(5)=−120≠0,
  F_49(7)=0, and the third root −8 is unoccupied.
* K: K(49)=K(19)=4t^2, and K=4tH at the four nonsquares, with ordered
  four-element orbits. A(49)=2H^2, B(49)=2H. This gives L_(p,+)=8t^2,
  L_(p,−)=16tH, Z_p=0, D_(p,+)=32t^4−8t^2H^2 and D_(p,−)=64t^2H^2.
* q=5, uniform start (direct count and (5) agree): epsilon=h=−1,
  L_(q,+)=0, L_(q,−)=8/25, Z_q=0. Acceptance happens exactly when beta_p∈{49,19}.
* t=1/12, H=1/4, m=1/6: D_(p,+)=−5/2592. The raw filtered drift is
  −1/1620, C=4/225, and the conditional drift is −5/144. As a direct check,
  each accepted parameter has probability 1/2, so the mean is
  ((4t^2−2H^2)+4t^2)/2=4t^2−H^2. The unfiltered local D_v=67/2592>0, and the
  unfiltered composite raw drift is (8/25)·D_v=67/8100>0.
* Integral version, t=14/167, H=42/167, m=27/167: D_(p,+)=−40t^4, and the
  conditional drift is −5t^2. Odd-map realizability holds. The 83 input
  pairs {x,−x} are assigned as 13 to zero, 14 to ±3, 14 to ±5 and 42 to ±7.
  This gives the fibre sizes 27/14/14/42, and the certificate builds this
  odd function explicitly. Lagrange interpolation of an odd function gives
  an odd polynomial; adding X^167−X makes it monic of degree 167.
  Coefficientwise CRT with X^167−X^3+X, which is the identity map mod 5,
  gives one monic odd map modulo 835. The rational masses
  (1/12, 1/4, 1/6) cannot be a uniform pushforward on F_167.

**Verdict.** This is a valid falsifier of *automatic inheritance* of the
universal positive residual drift by the filtered sampler. The universal
claim would have to cover q=5, and it fails there. The parent's expectation
is confirmed by proof, not just accepted.

**Qualification the parent did not state.** The sign threshold for this
p-law is −D_(p,+)/D_(p,−)=5/72 in both versions. The negative drift needs
L_(q,+)/L_(q,−)<5/72. A uniform q-state reaches that only at q∈{5,7}, where
L_(q,+)=0. With the same p-law and a uniform q-state at any q≥11, the
filtered p-drift is **positive**, since the ratio is at least 1/6>5/72.
So the counterexample relies on a degenerate small-prime partner. A version
with a large partner prime needs a non-uniform q-state with strongly
imbalanced sectors. That is not constructed here, because constructing it
would need a search. The q-side drift in the example is positive
(16/5625). The root drift at p is also positive (1/225 raw): the "loss" in v
is mass moving into the root atom. Nothing here is reachable by the cubic
acquisition rule, and nothing is claimed about reachability.

## 5. The proposed response: unfiltered training plus a filtered final detector

**Invariant preservation is valid.** Suppose the training updates use the
unfiltered rule, and the Jacobi-selected parameter is used only for gcd
tests at the end, never applied as a map update. Then every training law is
exactly a W010 law, and theorem (10) applies to the training phase without
change. If the detector *applies* a filtered update, that one step falls
under §2 and is not covered.

**Performance is unproved.** Here is the exact detector law at a fixed final
odd map. Acquire (z,u) at depth k, at a cost of 2·O(k+1). Accept a Jacobi
−1 beta. Then probe gcd(P(x)^2−beta,N) with fresh x, at O(k+1) each. A probe
succeeds exactly when P(x)^2≡beta at the square prime, which has
probability B_(square prime)(beta), and by (1) it is never full. The raw
probability that one attempt plus one probe succeeds is

    L_(q,-)G_p + L_(p,-)G_q,

which equals the filtered root increments E[Delta m_p]+E[Delta m_q]. Probes
that reuse one beta are conditionally independent given beta, not
unconditionally. The filter does two things. It discards both-nonsquare
parameters, which are useless; that is a saving. It also discards
both-square parameters, which would give proper gcds with probability
B_p+B_q−2B_pB_q; that is a loss. The only masking it removes is the
both-hit event, of order B_pB_q. Whether the gain exceeds the loss, and
whether either beats the fresh pair-collision test with expected root
increment v, depends on the unknown reachable G and B profiles. No
advantage is established.

## Strongest survivor, falsifier, next question

* **Survivor:** (1)–(5) hold exactly for N=pq with distinct primes p,q>3,
  with the scope corrections in §1–§3. Root mass and total collision mass
  remain pointwise nondecreasing under the filter. Unfiltered training plus
  an off-line filtered detector keeps theorem (10).
* **Falsifier:** filtered residual drift has no universal sign. Its sign is
  governed by the cross-prime ratio L_(q,+)/L_(q,−) against
  −D_(p,+)/D_(p,−). The certified example sits at the degenerate partner
  q=5.
* **Next question:** on the reachable unfiltered process, compare the
  end-of-training value of L_(q,−)G_p+L_(p,−)G_q per paid attempt (counting
  rejections) with the unfiltered detector channels, i.e. the both-square
  part and the pair-collision value v. In particular, does reachable
  training move the sector ratio away from 1? No speedup or benchmark
  follows from this review.

[Delivery manifest](W010-jacobi-review-manifest.json).
