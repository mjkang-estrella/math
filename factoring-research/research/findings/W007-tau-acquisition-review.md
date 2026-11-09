# W007 tau-model and prior-art review of the rational split-circuit branch

2026-10-08. Independent T3 child review (Claude Opus 5.5, user-authorized).
Scope: the final section of the parent NEW NOTE ("A distinct escape from the
rational circuit branch") and its relation to the Shub–Smale tau conjecture
and to factoring. No recursive delegation, experiment, numerical or PTE search,
package, shared-state/solver/Lean edit, commit or publication. Not re-audited:
the fixed degree-eight Galois computation (W007-split-circuit-review.md) and the
16-root additive-triple construction (live task B). Sources, read scope and hashes
are in `W007-tau-acquisition-review-sources/` (manifest.json).

**Disposition.** The parent's division-free conversion is **correct**. It needs
two small corrections and one addition: lowest terms are not needed; the cost
of the constants must be stated as tau cost, not height; and the adaptive
constants a_j=P_j(r_j) have an explicit cost. A family with superpolynomially
many distinct rational roots whose constants have polynomial total tau cost
**would refute the Shub–Smale tau conjecture**, an open conjecture. Uniformity
is not needed for that. Constants of unknown or exponential tau cost cancel the
tau conclusion, but not a weaker additive-complexity conclusion (§3). Neither
consequence yields a factoring algorithm without further hypotheses, listed in
§5. **Verified factoring improvement: NONE.** The rational branch should stay a
finite-stage algebraic probe; it should not be the main asymptotic bet.

## 1. The exact statements actually in force

**Tau conjecture.** I checked the wording as quoted by Rojas from Shub–Smale
[SS95] and [BCSS98, Thm 3, p.127]. The original SS95 paper and BCSS were not
retrieved. Rojas math/0304100, Definition 1: an SLP is (1, x, f_2, ..., f_N),
with f_0=1 and f_1=x. Each f_i is a sum, difference or product of two earlier
entries. **No other constants are allowed.** tau(f) is the least N−1. The
conjecture: there is an absolute κ ≥ 1 such that every f ∈ Z[x]\{0} has at most
(tau(f)+1)^κ distinct roots in Z. Status as stated there (2003): open, even for
κ=1. Shub–Smale proved: tau conjecture ⇒ P_C ≠ NP_C. This is a one-way
implication. A refutation does **not** give P_C = NP_C, and it gives no
factoring algorithm.

**Proved bounds (theorems, not conjectures).**
- deg f ≤ 2^tau(f), so the trivial bound is 2^tau integer roots.
- Rojas math/0304100 Thm 3 bounds the rational roots of f ∈ Z[x] with additive
  complexity σ_Z(f) ≤ s by 1 + s^3(s+1)(7.5)^s s!.
- Rojas math/0201154 Thm 1 gives an analogous Q_p bound. These bounds contain
  a factor (p−1), together with Np(s) or (p^d−1).
- In 0201154 (2002), Rojas states that it "isn't even known if there is a
  family of f with 2^{Ω(σ_{Q_2}(f))} roots in Q_2". I did not check whether this
  question has been settled since.
- The real analogue fails. Rojas 0304100 Example 1: g_{j+1}=4g_j(1−g_j) gives
  g_j(x)−x with 2^j real, irrational roots and tau O(j). This is the same nested
  quadratic shape as P_k.

**Straight-line factoring (Brown, eprint 2010/047, read in full).** The model
uses one fixed constant-free SLP from 1, with no input variable and no dependence
on n. There is no division, randomness or branching. It is evaluated mod n,
followed by one gcd. The proved bounds are definitional:
- L ≥ Λ(n,µ) = min λ(I) over integers I that split a µ-fraction of inputs;
- a concrete bound L ≳ s, about the bit length of the primes, for RSA-like
  n=pq and µ=1/2.

Brown lists division, randomization and branching as future work. This is a
linear lower bound for a restricted nonadaptive class. It must not be extended
to adaptive, randomized or input-variable procedures, and it is no barrier to
anything in W007.

**Lipton 1994 (ANTS-I, LNCS 877, pp. 71–79).** Only the abstract was
retrievable: "if polynomials with many rational roots have polynomial length
straight-line complexity, then integer factorization is 'easy'". The full text
is paywalled, and Springer serves a bot check. I have **not** verified its
theorem's hypotheses: root range or height, uniformity, nonuniform versus
uniform "easy", or average versus worst case. Nothing below relies on it. §5
derives independently what such a connection minimally requires.

## 2. The conversion, corrected and with exact operation counts

Write a_j = u_j/v_j with u_j, v_j integers and v_j ≠ 0. **Lowest terms are not
required.** This matters, because gcd reduction is not an SLP operation. Set
D_0=1 and A_0=X, and define

    A_(j+1) = A_j (v_j A_j − u_j D_j),     D_(j+1) = v_j D_j^2.

Then A_j = D_j P_j by induction:
v_j D_j^2 P_j(P_j − u_j/v_j) = (D_j P_j)(v_j D_j P_j − u_j D_j).

A_j ∈ Z[X] has degree exactly 2^j and leading coefficient D_j ≠ 0. There is no
cancellation: lc(A_{j+1}) = D_j · v_j D_j. By the rational root theorem, every
rational root m/d (in lowest terms) of A_k has d | D_k.

**Integer roots need a paid scaling, not just cleared coefficients.** A_k itself
has rational, non-integer roots. Let A_j^h(Y,V) = V^{2^j} A_j(Y/V) be the degree
2^j homogenization; the D_j are numbers, not powers of V. Then

    A_(j+1)^h = A_j^h · (v_j A_j^h − u_j D_j V^(2^j)),     A_0^h = Y,

and H_k(Y) := A_k^h(Y, D_k) = D_k^{2^k} A_k(Y/D_k) ∈ Z[Y]\{0}. Its roots are
exactly D_k·r for the roots r of P_k. Every rational root becomes an integer,
and distinct roots stay distinct. This is the parent's H_k. The construction is
correct as written, and it remains correct with non-reduced (u_j, v_j) of either
sign.

**Constant-free SLP for H_k, in variable Y from {1, Y}:**
- D_1, ..., D_k: 2 operations each, so 2k. (D_1 = v_0 is free once v_0 exists.)
- Set V = D_k, W_0 = V and S_0 = Y. Each stage j performs:
  - W_{j+1} = W_j^2;
  - t = v_j S_j;
  - s = D_j W_j;
  - s' = |u_j| s;
  - S' = t ∓ s', with the sign chosen from sgn u_j, so no negation is needed;
  - S_{j+1} = S_j S'.

  That is 6 operations per stage, or 6k−1 in total.

So **tau(H_k) ≤ 8k + T**, where T is the length of one multi-output
constant-free SLP producing (|u_j|, v_j)_{j<k}. Distinct rational roots of P_k
become distinct integer roots of H_k one-for-one.

**Adaptive constants a_j = P_j(r_j), with r_j = m_j/n_j.** Then

    a_j = A_j^h(m_j, n_j) / (D_j n_j^{2^j}),

so take u_j = A_j^h(m_j, n_j) and v_j = D_j n_j^{2^j}. Both come from the same
recurrence with V = n_j: 6j+2 operations for u_j and v_j (n_j^{2^j} is the last
W), plus 2 for D_{j+1}. Summed over j<k this gives 3k^2+k. Allow 2 operations
per negative m_j. Therefore

    tau(H_k) ≤ 3k^2 + 11k + Σ_(j<k) [tau(|m_j|) + tau(n_j)],

with tau(m) ≤ 2⌈log2 m⌉ by double-and-add (Brown eq. 3). This equals the
parent's Θ(k^2) training cost, so nothing is hidden.

**Hand check on the frozen 8-root P_3.**
- r = 1, 2, −4/5, so a_0 = 1, a_1 = 2 and D_1 = D_2 = 1.
- u_2 = A_2^h(−4,5) = (−4)(−9)(−14)(1) = −504 and v_2 = 5^4 = 625. This
  matches a_2 = −504/625.
- D_3 = 625. So H_3 has the eight integer roots
  625·{−1, 0, 1, 2, −4/5, 9/5, −2/5, 7/5} = {−625, 0, 625, 1250, −500, 1125, −250, 875}.

D_k overscales; the true lcm of denominators is 5. This is harmless, because
only tau is charged.

**Division-generated constants.** Suppose a constant is produced by a
length-L SLP from 1 that uses {+, −, ×, ÷} and never divides by zero. Track
each value as a pair (num, den):
- + and − cost 3 multiplications and 1 addition;
- × and ÷ cost 2 multiplications each.

This gives a division-free (u, v) pair, with v ≠ 0 and not reduced, in ≤ 4L
operations. That suffices by the remark above.

## 3. What each kind of constant implies

Let R_k be the number of distinct rational roots of P_k, so R_k ≤ 2^k.

1. **Arbitrary rational constants (no cost bound).** The tau conclusion is
   **nullified**. The bound tau(H_k) ≤ 8k + T is then just an unknown upper
   bound, and T can be ~2^k if the heights are ~2^k. A non-trivial
   consequence remains, by a theorem rather than a conjecture:
   - With Z_j = v_j A_j − u_j D_j, we get A_k = X ∏_{j<k} Z_j and
     Z_j = v_j X ∏_{i<j} Z_i + (−u_j D_j). Each stage is exactly one additive
     step of Rojas's definition, so σ_Z(A_k) ≤ k for any constants.
   - Rojas's proved bound 1 + k^3(k+1)7.5^k k! exceeds 2^k for every k ≥ 1,
     so it does not exclude full splitting.
   - A family with R_k ≥ 2^{ck} for all k, with any rational constants, would
     answer affirmatively the question Rojas stated as open in 2002: a family
     with 2^{Ω(σ)} roots in Q_2. As of 2002 this is a research-level result,
     not a contradiction.
2. **Constants with paid division-free SLPs (or poly-size binary, or
   poly-length division-SLPs, via ≤ 4L).** If R_k is superpolynomial in
   8k + T, then H_k refutes the tau conjecture for every κ. With 2^k roots this
   holds whenever T = 2^{o(k)}. Using only binary size in the adaptive form, the
   condition is **Σ_j h(r_j) = 2^{o(k)}**, where h is the bit height of the
   training points. The heights of a_j and of the roots are irrelevant to tau.
   Exponential root count with polynomial-size constants is far more than
   enough. Even R_k = 2^k with T = 2^{k/2} only gives R = tau^{~2}, which
   refutes κ < 2 and not the conjecture. **Uniformity is irrelevant** to a
   refutation; existence suffices.
3. **Constants generated by division.** Same as item 2 after the ≤ 4L
   conversion. Division by zero inside the constant SLP must be excluded,
   because the pair form then has v = 0.
4. **Bit-efficient modular-only procedures.** Examples: r_j uniform mod N in
   the residual-fiber route, or constants that exist only mod N or mod p. No
   polynomial in Z[x] is defined, so the tau conjecture, Rojas's Q/Q_p bounds
   and Brown's model (no inputs, no randomness) are all silent. Conversely,
   nothing from them helps such a procedure. If a modular procedure merely
   evaluates a rational family mod N, the rational family's status is
   unchanged.

**Answer to the central question.** Yes, with an explicit transformation:
exponentially (in fact superpolynomially) many distinct rational roots in a
polynomial-size division-free rational circuit refute the original integer-root
conjecture. "Polynomial size" must include producing every constant from 1;
binary or division-SLP descriptions convert at the costs above. An unknown,
exponentially costly constant does nullify the tau conclusion. Because the
conjecture is open and widely believed, a scalable rational construction with
cheap constants would be a major theorem, which is evidence against it. **It is
not a proved obstruction:** no theorem I read excludes it.

## 4. Finite milestones prove nothing asymptotic

Eight roots exist now, and task B may reach sixteen. Any finite k is compatible
with every κ, so no finite depth can refute or support the conjecture. The
genus-25 result for the fixed cover concerns only that fiber. The only
asymptotic statements that matter are the threshold Σ h(r_j) = 2^{o(k)}
together with R_k ≥ 2^{Ω(k)} (tau), or R_k ≥ 2^{Ω(k)} with any constants
(Rojas question).

## 5. What a factoring use would additionally need (derived here, not from Lipton)

Evaluating H_k or A_k mod N costs tau multiplications mod N (Brown Lemma 1). If
gcd(D_k, N) is proper, that gcd is the factor; otherwise D_k is a unit. A
τ-refuting family still needs all of the following:

- **F1 (uniform acquisition).** A poly(n)-time algorithm must output the r_j or
  the SLP. Existence alone does not suffice.
- **F2 (root mass at the unknown prime).** Let the R distinct rational roots
  have numerators and denominators < 2^B. For p ∤ denominators, a collision is
  p | num(r_i − r_j). Cauchy–Schwarz gives #residues ≥ R^2/(R + 2C_p). Each
  nonzero numerator has at most (2B+1)/log2 P prime factors in [P, 2P]. Hence
  the average C_p over those primes is O(R^2 B/P), and Markov's inequality
  applies.
  - Result: if R ≥ P, then **at least half the primes in [P, 2P] have
    z_p = Ω(1/B)**.
  - So one needs R ≥ 2^{n/2}, hence k ≥ n/2 stages, and **root heights
    B = poly(n)**. B is irrelevant to tau but essential here.
  - This is an average over primes, not a guarantee for the specific p | N.
  - If R ≪ p, then z_p ≤ R/p, which is useless.
- **F3 (separation).** Test gcd at every depth j ≤ k. The roots are nested, so
  for uniform x the first-hit depths J_p and J_q are CRT-independent.
  Then Pr[J_p = J_q] ≤ max_j Pr[J_p = j] + (1 − z_p)(1 − z_q).
- **F4 (worst case).** F2 is distributional over primes. A per-N worst-case
  claim needs more.

So even a refutation of tau leaves factoring conditional on F1, F2 (with
polynomial heights), F3 and F4.

## 6. The changed computation that evades each barrier, and what it still pays

| Barrier | Exact scope | Changed computation outside it | Still-paid cost |
|---|---|---|---|
| Tau conjecture (open) | one fixed f ∈ Z[x]; distinct **integer/rational** roots | finite-field root richness without rational splitting: adaptive r_j uniform mod N (residual route) | Θ(k^2) training ops mod N, Θ(k) per probe, and an unproved growth law for v (E[Δv] = zR + Q − D − t; audit belongs to the parent/residual task) |
| Rojas Q / Q_p bounds (theorems) | roots in Q, Q_p in terms of σ; carry a factor (p−1) | F_p-root density up to p/poly: simple F_p roots Hensel-lift to Z_p, but the bound already allows ~p·e^{s log s} | none from the bound; the bound itself does not constrain residue density |
| Rational splitting of P_k | fiber must split over Q | split only mod p: x^M − 1, division polynomials (p−1, ECM), i.e. Brown's class | smoothness probability: the known baselines, not new |
| Brown SLP bound (theorem) | fixed, input-free, nonadaptive, division-free, single gcd | random inputs mod N, adaptive choice, multi-gcd | bound is only ≈ s anyway; gives no budget |
| N-dependent constants | — | polynomial changes with N | tau never applies; useful only via F2-type root mass |

**Rho comparison for the residual route (one prime; heuristic cost model; not
audited dynamics).** Let z_k be the zero mass after k stages. The cost to
success is about k^2 + k/z_k. To beat √p, one needs some k ≤ p^{1/4} with
z_k ≥ k/√p.
- The pseudorandom heuristic (v linear, so z ~ k^2/p) never meets this. It
  reaches only rho parity at k ~ √p, even if training were amortized to O(k).
- With Θ(k^2) training, rho parity needs **z_k ≳ k^3/p**, i.e. E[v_j] ≳ j^2/p,
  for j up to p^{1/4}.
- Beating rho needs strictly faster growth.

This is the concrete threshold for the main bet.

## 7. Conclusion and next gate

- **Proved here (elementary).** The corrected division-free conversion and
  tau(H_k) ≤ 3k^2 + 11k + Σ[tau(|m_j|) + tau(n_j)] for the adaptive rational
  family; the 4L division conversion; σ_Z(A_k) ≤ k; and the F2 counting
  statement.
- **Conditional.** Scalable full splitting with Σ h(r_j) = 2^{o(k)} ⇒ the tau
  conjecture is false. With arbitrary constants ⇒ Rojas's 2002 open question is
  answered. Neither yields factoring without F1–F4.
- **Not established.** Any proved lower bound against the route (tau is a
  conjecture), Lipton's exact hypotheses, the original SS95 text, or the
  post-2003 status of Rojas's question.
- **Recommendation.** Keep the rational branch a finite algebraic probe, and do
  not plan beyond task B's 16-root milestone. Any structural all-depth argument
  would be a τ-counterexample or a Rojas answer, and it would need F2 heights
  before it mattered for factoring.
- **Next algorithmic gate (main bet, symbolic).** For the residual adaptive
  route, decide exactly, as rational functions of p from the uniform start,
  whether E[v_j] grows superlinearly. The threshold is E[v_j] ≳ j^2/p (giving
  z_k ≳ k^3/p) for rho parity under Θ(k^2) training. If an exact or bounding
  argument shows E[v_j] = O(j/p) uniformly in that range, reject the route
  against rho. Any experiment for this needs a separate authorization.
