# W029 review — Frobenius degree probe and the normalized-derivative consumer

**Disposition:** sections 1–3 are correct as scoped, with a few wording fixes.
The section 4 consumer is fully accounted for by existing tests. As a value,
H_N(x) is an ordinary evaluation of the same circuit's second output:
H_N(x) = (F_N(x) − G_N(x))/(2x) mod N. It equals −2·U_{N−1}(2,4x), a Lucas
U-sequence value. Its gcd is the Lucas/quadratic-torus analogue of
gcd(b^{N−1}−1, N), which is Williams p±1 with the fixed exponent M = N−1.
I give an exact formula for the x-sampling zero count, so "no general split
bound" can be replaced by a theorem. It also gives an infinite family on which
the consumer never splits (e.g. N=35). Normalized Hasse derivatives of order
below the smallest prime contain no further invariant. Verified complete
factoring improvement: **NONE**. No novelty or factoring bound is claimed.

## Scope and provenance

This review owns only this file and
[its evidence directory](W029-frobenius-degree-review-evidence/). It made no
delegation, installs, commits, or shared solver/Lean/STATE/task-file edits.
W028 was not read or re-audited. The full brief is in
[brief.txt](W029-frobenius-degree-review-evidence/brief.txt), SHA-256
`d39f7416ca0155b78367171f0383b53b204d4635bd1dc3d87184e788cad7ee39`.
The audit target was read in full and snapshotted as
[W029-probe-snapshot.md](W029-frobenius-degree-review-evidence/W029-probe-snapshot.md), SHA-256
`65be1f049e81319ba3fac32824ca6573d31b90c4c9f8907ca4bca80f3450e86f`.
[input-freeze.json](W029-frobenius-degree-review-evidence/input-freeze.json)
records byte counts, hashes, and the exact read scope of every input:

- governing files read in full;
- W021 §C (lines 115–140) and selected ranges of its review and disposition;
- W001-algebra Card D and W022 §B, found by targeted grep;
- W001/W005/W019, grep only.

Web checks:

- arXiv 1707.06877: the abstract page was fetched. It is Bluher, "Permutation
  properties of Dickson and Chebyshev polynomials and connections to number
  theory". It concerns Dickson permutation criteria and polynomial
  factorization formulas, not integer factoring. No theorem text was read and
  nothing from it is load-bearing here.
- MDPI 2227-7390/14/13/2378: the fetch failed with HTTP 403 (the parent saw
  429). No content was read and nothing was adopted.

## 1. Construction and component degrees (§1): correct

- **Basis expansion.** F_r = Σ_j C(r,2j)(1−4X)^j and
  G_r = Σ_j C(r,2j+1)(1−4X)^j.
- **Dickson/Lucas form.** u = 1+a and v = 1−a are the roots of
  T² − 2T + 4X. Hence 2F_r = V_r(2,4X) = D_r(2,4X), and G_r = U_r(2,4X). The
  Dickson identity the parent suggested is correct.
- **Frobenius.** In F_p[X][a],

      (F_q + aG_q)^p = F_q(X^p) + a·(1−4X)^((p−1)/2)·G_q(X^p).

  So F_N ≡ F_q(X^p) mod p, as stated. The finding omits the companion
  identity G_N ≡ (1−4X)^((p−1)/2)·G_q(X^p) mod p, which §4 below uses.
- **Degrees and leading coefficient.** For odd q, F_q has degree (q−1)/2 and
  leading coefficient q(−4)^((q−1)/2), which is a unit mod p. The degree mod p
  is (N−p)/2 and the degree mod q is (N−q)/2. The top index mod N is
  r = (N−p)/2, and its coefficient has gcd q with N. N − 2r = p. Signs are
  correct.
- **Scope note.** This holds only for N = pq. For general odd N with
  p^k ∥ N, the same argument gives degree (N − p^k)/2 mod p. The top index
  then exposes the smallest prime-power divisor, not necessarily the smallest
  prime.
- **Support.** The support mod p is at most (q+1)/2 indices and mod q at most
  (p+1)/2. The union bound is ≤ (p+q)/2 + 1. This is an upper bound only, as
  the finding already says.

Certificate C2 checked N = 15, 21, 35. All degrees, top indices, gcds, and
leading residues match.

## 2. Aliasing scope (§2): correct, with three wording fixes

- **Base ring vs. extension rings.** "Over Z/NZ, all base-ring evaluations
  inherit this aliasing" is correct. In extension rings
  R = (Z/N)[Y]/(f), the aliasing becomes F_N(y) ≡ σ_p(F_q(y)) mod p, where
  σ_p is Frobenius. The values are then related by a ring automorphism rather
  than identical. That is the ordinary Frobenius/AKS/Grantham setting already
  catalogued in the W021 C review §5. Extension evaluations are therefore not
  an unexplored escape from §2. The sentence should name both cases.
- **Hasse derivatives.** "First useful Hasse derivatives require paid access to
  high-index coefficients" should be made exact:
  - D^(k)(X^{pj}) = C(pj,k)X^{pj−k} ≡ 0 mod p for 0 < k < p.
  - So the first Hasse derivative of F_N that is nonzero mod p has order
    exactly p, and D^(p)F_N ≡ (F_q')(X^p) mod p. Mod q, the first such order
    is q.
  - Computing it means evaluating the circuit over (Z/N)[Y]/(Y^{k+1}) with
    k ≥ p. That costs Θ(p) coefficients per gate, i.e. trial-division scale.
    This is W021 C's adaptive-truncation cost transposed from (1+X)^N to this
    circuit, not a new barrier.
- **Real circuit cost.** One pair multiplication is about 4–5 modular
  multiplications plus the constant multiplication by A = 1−4x. Evaluation
  costs O(log N) pair operations, i.e. O(n·M(n)) bit operations. This is
  correct. The O(log r) gate count over Z[X] hides degree growth, so it is a
  straight-line-program length only.

## 3. Section 4: exact corrections

**(a) The identity is correct.** Use a' = −2/a and compare the 1 and a
components of the derivative of (1+a)^r. This gives

    F_r' = −2r·G_{r−1}
    (1−4X)·G_r' = 2G_r − 2r·F_{r−1}

The first identity was checked exactly over Z for r = 2..12 (certificate C1).
So H_N = −2G_{N−1}, and computing it needs no division by N.

**(b) Main correction: H_N is an evaluation of (F_N, G_N).** Since uv = 4x,
for every unit x we have u^{N−1} = u^N·v/(4x). Taking a-components:

    G_{N−1} = (G_N − F_N)/(4x),   so   H_N(x) = (F_N(x) − G_N(x))/(2x)  mod N.

Certificate C3 found zero mismatches over all units for N = 35 and 91. A
non-unit x already gives gcd(x,N) > 1. So the normalization adds nothing
beyond the observation model of §2 applied to the circuit's other output.

It also inherits the aliasing. As functions on F_p, F_N(x) = F_q(x) and
G_N(x) = χ·G_q(x). Hence

    H_N(x) ≡ (F_q(x) − χ·G_q(x))/(2x)  mod p.

The finding's sentence "genuinely recovers information killed by ordinary
differentiation" is true of the polynomial F_N'. It is false as a claim about
information beyond base-ring evaluations, and should be revised.

**(c) The order condition is confirmed, with a simpler gcd.**
- H_N(x) ≡ 0 (mod p) iff u^{N−1} = v^{N−1}. This needs 2 and a to be units
  (excluded: 1−4x ≡ 0) and v to be a unit (excluded: x ≡ 0).
- t = u/v lies in μ_{p−1} if χ = 1, and in the norm-one group μ_{p+1} if
  χ = −1, because Frobenius swaps u and v.
- N − 1 ≡ χq − 1 = χ(q − χ) mod (p − χ), so the condition is t^{q−χ} = 1.
- The subgroup size is gcd(N−1, p−χ) = **gcd(p−χ, q−χ)**.

The exceptional points are nonzero mod p:
- H_N(0) = −2^{N−1}.
- If 1−4x ≡ 0, then a is nilpotent and G_{N−1} ≡ N−1, so H_N ≡ 2.

**(d) Exact x-sampling count, replacing "no subgroup-fraction bound".**
Let g₊ = gcd(p−1, q−1) and g₋ = gcd(p+1, q+1).

The parametrization is x = t/(t+1)², a = (t−1)/(t+1). It is a bijection
between F_p \ {0, 1/4} and unordered pairs {t, t^{−1}} with t ≠ ±1:
- (p−3)/2 pairs come from the split group and (p−1)/2 from the norm-one group,
  for a total of p − 2.
- t = 1 corresponds to the excluded x = 1/4. t = −1 corresponds to no x.

Both g₊ and g₋ are even, so ±1 always lie among the solutions. Therefore

    #{x ∈ F_p : H_N(x) ≡ 0 mod p} = (g₊ − 2)/2 + (g₋ − 2)/2 = (g₊ + g₋)/2 − 2 =: Z.

The same Z counts zeros over F_q, because g₊ and g₋ are symmetric in p and q.
For x uniform mod N, the CRT components are independent, so

    Pr[gcd(H_N(x), N) is proper] = (Z/p)(1 − Z/q) + (Z/q)(1 − Z/p).

Certificate C4 matched Z exactly at both primes for (3,7), (5,7), (7,13),
(11,31), and (13,29). C5 shows N = 21 splits for 8 of 21 values of x, as
predicted.

**(e) Concrete total-failure family.** If g₊ = g₋ = 2, then Z = 0 and
gcd(H_N(x), N) = 1 for every x coprime to N. Certificate C5 confirms this for
N = 35, with gcd 1 for all 35 residues, including the exceptional ones.

The family is infinite. For p = 5, every prime q ≡ 7 (mod 12) has
gcd(4, q−1) = 2 and gcd(6, q+1) = 2, and Dirichlet's theorem supplies
infinitely many such q. Generic random p and q have small g₊ and g₋, so the
success probability is O(1/p), exponentially small in n.

**(f) Accounting against existing tests.**
- The test U_{N−1}(P,Q) ≡ 0 is the fixed-exponent Lucas analogue of the Fermat
  gcd. It is Williams p±1 with M = N−1 in the split/norm-one torus.
- W001-algebra Card D already analyses the N+1 multiplier version, using the
  identity gcd(p+1, N+1) = gcd(p+1, q−1). H_N is the same mechanism with
  exponent N−1. Its success condition, "(p−χ)/gcd(p−χ, q−χ) small or absorbed",
  is the familiar shared-p±1 special family.
- The standard Lucas probable-prime test uses U_{N−(D/N)} instead. The zero
  count Z is the expected liar-count shape (cf. Monier and Baillie–Wagstaff).
  I did not check it against their theorem text and claim no priority either
  way.

## 4. Is any different cheap scalar invariant left in this normalization?

None of the following is new.

- **Higher normalized derivatives.** From (a), every F_N^(k) is a
  Z[X, (1−4X)^{−1}]-combination of the components of (1+a)^{N−j} for j ≤ k.
  At a unit x, these are fixed rational functions of x times (F_N(x), G_N(x)).
  So any scalar consumer is again a function of the single torus element u^N.
- **Normalized Hasse derivatives of order m < min(p, q).** Use the Taylor
  expansion (u + aε)^N, where a(x+Y) = a·√(1 − 4Y/A) has coefficients in
  Z[1/A]. The relevant coefficients are C(N,k)/N = C(N−1,k−1)/k, with k a
  unit, and C(N−1,k−1) ≡ (−1)^{k−1} mod p. So mod p,

      (1/N)·D^(m)F_N(x) = [Y^m] component of u^N·log(1 + aε/u),

  which is a public series in x times u^N. Again there is no new invariant.
- **Orders at or above p.** Nonzero information appears only there, at Θ(p)
  cost (§2 above).

The displayed consumer is therefore fully accounted for. A genuinely different
invariant would have to leave the algebra generated by u^N, for example a
non-evaluation symbolic operation on the circuit, and no such operation is
supplied.

## Exact text corrections requested

1. §1: add G_N ≡ (1−4X)^((p−1)/2)·G_q(X^p) mod p. Add that for p^k ∥ N the
   degree is (N − p^k)/2.
2. §2: base-ring aliasing is identical values. Extension-ring aliasing is
   σ_p-twisted values, which are already covered by W021 C §5. The first Hasse
   derivative nonzero mod p has order exactly p and costs Θ(p) jet width.
3. §4: replace "genuinely recovers information killed by ordinary
   differentiation" with "H_N(x) = (F_N(x) − G_N(x))/(2x) mod N. This is
   base-ring evaluation data of the same circuit and equals −2U_{N−1}(2,4x)."
4. §4: replace "potential zero set … size gcd(N−1, p−χ) … no bound supplied"
   with the exact count Z = (g₊ + g₋)/2 − 2, the split probability formula,
   and the Z = 0 family (N = 35; p = 5, q ≡ 7 mod 12).
5. Deduplication: also cite W001-algebra Card D (Williams p+1, N±1
   multiplier) as the antecedent of the §4 consumer.

## Certificate record

There was one frozen run with fixed inputs and no sweep.

- The [code](W029-frobenius-degree-review-evidence/certificate.py) has SHA-256
  `445ab68d…313087`.
- [certificate-freeze.json](W029-frobenius-degree-review-evidence/certificate-freeze.json),
  SHA-256 `fccad540…61a5`, was written before execution. Its budget was 20,000
  events and 60 s.
- Exactly one invocation ran, guarded by the exclusive `RUN-MARKER`.
- Status ok: 4,634 charged events, about 0.001 s, empty stderr.
- [Output](W029-frobenius-degree-review-evidence/certificate-output.json) has
  SHA-256 `32bfb09b…a166`.
- Checks C1–C5 all agreed with the symbolic predictions. No row failed. Every
  row, including the non-splitting N = 35 histogram, is retained.

The run verifies identities on toy inputs only. It is not evidence of any
complexity.
