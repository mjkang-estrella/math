# W027 review: exact optimum of the weighted coefficient carry envelope

2026-10-08 local / 2026-10-09 UTC. **Accept W027 as stated, with three scope repairs.** (2) computes the exact minimum of F over 1≤c<Q in polylog bit time per fixed-D chart, and Lenstra supplies a witness. Normalization, the floor bound, the W024/W020 interfaces, and inclusion of every W025-review truncation and hybrid are correct. The minimum is a genuine global minimum over the whole class of precision-≥ℓ constant-scaled representations in a fixed basis (proof in §3).

The repairs:
1. Exact domination of the review options holds only in the **same monomial basis**. A substituted singleton-y basis is uniformly better, and §4 has a counterexample to cross-basis domination.
2. The per-chart optimum can choose c'≠1 when a c'=1 truncation is only moderately worse (§5). This does not hurt the existing explicit-anchor consumer, but it does hurt any evaluator that shares the α^(u+Nv) progression.
3. Every class member pays at least W/Q (§6). So W027 cannot cross the W025 consumer-frontier envelope.

**Verified complete factoring improvement: NONE.**

Scope: the verbatim [brief](W027-optimal-envelope-review-evidence/task-brief.md), W027.md at SHA-256 `3499ca39…16bc416d`, plus the [hashes](W027-optimal-envelope-review-evidence/input-hashes.sha256) and [read scope](W027-optimal-envelope-review-evidence/read-scope.json). W022, W024, W020 and the W025 consumer are imported at their accepted interfaces and were not re-audited. The W026 affine-exception task was not touched. No numerical run was made. The two examples below are synthetic and checked by hand.

## 1. Formulation (2): correct

For fixed c, minimizing Σw_ν t_ν subject to t_ν ≥ |c d_ν − Q k_ν| gives t_ν = min_k |c d_ν − Qk| = |centered_Q(c d_ν)|, because every w_ν ≥ 1 > 0. So min{cW+Σw t} over feasible points equals min_c F(c).

The explicit bounds lose nothing:
- c, d_ν ≤ Q−1 gives c d_ν/Q ≤ (Q−1)²/Q < Q−1, so the nearest k lies in [0, Q−1].
- Q is odd, so |centered| ≤ (Q−1)/2 < Q.

**Witness.** Let B* be the least feasible B, and take any feasible point (c,k,t) at B*. Then F(c) ≤ cW+Σw t ≤ B* = min F, so c is optimal. Positive weights then force each t_ν = |c d_ν − Q k_ν| = |centered|. **Recommendation:** recompute e_ν = centered_Q(c d_ν) from c rather than trusting k. It costs nothing and removes any dependence on the solver's auxiliary values.

**Binary search.** Feasibility is monotone in B, and B=0 is a legal lower end. F(c)=0 does occur, for example with W=0 and c d_ν ≡ 0 (mod Q) for all ν. Also F(1) ≤ W + ((Q−1)/2)Σw ≤ F0. That gives ⌈log₂(F0+1)⌉+1 = O(log W + log Q + log Σw) calls.

**Bit cost.** Lenstra's data length is n·m·⌈log(a+2)⌉. Here n = 2D+1, m = O(D), and a ≤ max(F0, Q², Q·max w). Lenstra's paper produces a feasible integer point when one exists (W025-review evidence, `full.txt` lines 30–60). So the cost per chart is poly(log N) when Q, W, w_ν are poly(N). The polynomial's degree is exponential in n.

**Fewer integer variables.** Lenstra §5 (text lines 930–975) handles mixed ILP that is polynomial for a fixed number of integer variables. The t_ν can be real, so only the D+1 variables (c, k_ν) need to be integral. For a total-degree-4 bivariate chart that is ≤16 integer variables instead of 31. Either way the cost is constant in N and astronomically large in absolute terms. The W025 review's restricted searches (dimension ≤3) are far cheaper concretely. No practical claim is made, which matches W027.

**Edge cases:**
- **Q=ℓ (L=1):** every c in [1, ℓ−1] is a unit. Then r=1 and Q'=ℓ, and direct enumeration is trivial.
- **W=0:** valid. S≡0, and the optimizer may choose any c reaching F_min.
- **D fixed:** required. D grows with chart degree, not with N.
- **Ties:** Lenstra returns an arbitrary optimal witness. For reproducibility, optionally add a second binary search on an upper bound c ≤ C with B=B* fixed. This costs O(log Q) more calls and returns the least optimal c.

## 2. Normalization and the carry bound: correct

c* < Q gives v = ν_ℓ(c*) ≤ L−1, so Q' ≥ ℓ. Since r | c* and r | Q, r divides every e_ν = c* d_ν − Qk_ν, and e_ν/r = c' d_ν − Q' k_ν. Because |e_ν/r| ≤ (Q−1)/(2r) < Q'/2, the coefficient e_ν/r is in fact centered_{Q'}(c' d_ν).

The ratio is unchanged: numerator and denominator both scale by r. From S ≡ σR (mod Q) and Q' | Q we get c'S ≡ σP (mod Q'), so c'S = σP + Q'τ with

  |τ| ≤ (c'W + Σ w_ν |e_ν/r|)/Q' = F/Q.

τ is an integer, so the bound can be floored. When F < Q, the singleton {0} is correct.

Every coefficient of R, other than the constant, carries a factor of H. So, as in W025, P ≡ c' r₀ (mod ℓ) and the W024 residue becomes c'·ε_σ, a nonzero multiple of a unit. Retained exponents are nonzero integers, as W020 requires. c' depends only on (d, w, W, Q), so it is alpha-independent. Exponent width grows by at most log₂Q bits. Child boxes can keep (c', P, Q', interval), since their weights can only shrink.

## 3. Global optimality within the class: proved

**Class.** Triples (c', Q', P) where Q' | Q, Q' ≥ ℓ, c' is a nonzero integer, and P has the supplied support with P ≡ c'R (mod Q'). The objective is (|c'|W + Σw|P_ν|)/Q'.

A Q' that does not divide Q is not implied by the mod-Q data. And Q' | Q forces Q' = ℓ^j with 1 ≤ j ≤ L.

**Claim.** The minimum over the class equals min_{1≤c<Q} F(c)/Q.

*Proof.* Take any member, and let a ∈ [0, Q'−1] be the residue with a ≡ |c'| (mod Q').

- **Case a ≠ 0.** Then a ≤ |c'|, and |centered_{Q'}(a d_ν)| = |centered_{Q'}(c' d_ν)| ≤ |P_ν|. Put c = (Q/Q')·a. Then 1 ≤ c ≤ Q − Q/Q' < Q. Since centered_Q(c d) = (Q/Q')·centered_{Q'}(a d), we get F(c)/Q = (aW + Σw|centered_{Q'}(a d)|)/Q', which is at most the member's objective.
- **Case a = 0.** Then Q' | c', and Q' ≥ ℓ, so ℓ | c'. The W024 residue c'·ε_σ is then ≡ 0 (mod ℓ), and the filter deletes every exponent, including the true leaf. This is exactly W027's exclusion of multiples of Q. The class is filter-compatible only if ℓ ∤ c', and under that definition this case is empty. A member with ℓ | c' and a≠0 is covered by the first case, and its normalization strips the ℓ-power.

Conversely, normalizing any c < Q gives a member with the same objective. ∎

This also confirms the other two exclusions:
- **c ≥ Q, not a multiple of Q:** its remainder in [1, Q−1] has the same coefficients and a W term no larger.
- **Negative c:** equivalent under σ ↦ −σ.

Caveat: in the excluded direct-enumeration, precision-1 world, F(Q)/Q = W can be smaller than F_min/Q. For example, W=1 with huge weights. That is a different representation with no filter. W027's "optimal" does not compare against it, and it should not be quoted as optimal against no-chart alternatives.

## 4. Inclusion of the review's options: exact, but per basis

These all check:
- **Truncation:** c = ℓ^(L−j) gives centered_Q(c d) = c·centered_{ℓ^j}(d) exactly. The centered value has magnitude ≤ ℓ^(L−j)(ℓ^j−1)/2 < Q/2, so it is the unique centered representative.
- **Hybrid:** c = (Q/Q_j)·a.
- **W025 original:** c ≤ B < Q.
- **The review's §3 domain repair:** J ⊆ {4}, c ≤ B < Q.

Each objective is the exact centered envelope, so it is at most the stated bound for that option. The review's O(log²) two-parameter search is superseded. W027 also catches cases its formulas miss, such as K2's vanishing quartic, and needs no generic-coefficient assumption. **No review option is missed, provided W027 is run in the basis that option uses.**

**Repair: basis dependence.** The review priced singleton-y charts after substituting y = y₀. For every c,

  Σ_i Z^i |centered(c Σ_j d_ij y₀^j)| ≤ Σ_{i,j} Z^i |y₀|^j |centered(c d_ij)|.

The inequality holds because Σ_j y₀^j·centered(c d_ij) represents the same residue, and the centered representative is smallest. So the substituted optimum is never worse, and it can be strictly better.

Synthetic counterexample (not a W022 instance, since W022 would force d_xy ≡ 0 mod 9). Take Q=9, ℓ=3, monomials {1, x, xy}, d = (1, 3, 6), weights (1, 100, 100) with y₀=1, and W=10.
- **Bivariate basis:** F(1)=611, F(2)=622, F(3)=33. For c≥4, 10c > 33. So F_min=33 and the carry is 3.
- **Substituted basis:** the x coefficient is 3+6 ≡ 0, so F(1)=11 and the carry is 1.

The statement "includes all review hybrids" is therefore exact only when W027 is applied to the same supplied basis. **Rule:** substitute all singleton coordinates first, then run the optimizer. Chart shifts and coordinate changes remain outside the class.

## 5. Objection: the optimal carry can be worse for product sharing

Synthetic example. Take ℓ=3, Q=27, R = 1 + 12x (constant term a unit, linear term divisible by ℓ), w=(1,100), W=100. F(2)=502, and F(c) ≥ 100c, so only c ≤ 5 can compete. Those values, plus the truncation c=9 for comparison:

| c | Q' | c' | F | carry ⌊F/27⌋ |
|---|---|---|---|---|
| 1 | 27 | 1 | 1301 | 48 |
| **2** | 27 | **2** | **502** | **18** |
| 3 | 9 | 1 | 1203 | 44 |
| 4 | 27 | 4 | 1004 | 37 |
| 5 | 27 | 5 | 1105 | 40 |
| 9 (truncate to 3) | 3 | 1 | 909 | 33 |

The best c'=1 option, truncation to Q'=3, gives 33. The optimum gives 18 with c'=2.

**Existing consumer: no loss.** In the explicit-anchor consumer (W025 frontier), each giant α^(c'(u+Nv)−σP−Q'τ₀) is formed per explicit point anyway. Records are grouped only by stride (O(log Q) classes) and dyadic length. So the cost O~(K+√(KT)) is monotone in T, and the optimum is weakly better up to polylog factors.

**Sharing evaluators: possible loss.** Any evaluator that shares the α^(u+Nv) progression, or the linear part, across charts would need one progression per distinct c'. W025's truncation keeps c'=1 and one stride per stratum.

**Repair.** Also output the c'=1 restricted optimum, min_j F(ℓ^(L−j)). This needs O(L) direct evaluations and no ILP. Let the consumer choose between it and the full optimum, and price the choice.

## 6. Correction to the prior-review wording

I checked the arithmetic for p=7, q=11, ℓ=3, u=2, v=1: up − vq = 3, and E = (p−1)(vq−u) = 6·9 = 54 ≠ 0, but 54 ≡ 0 (mod 3). So "E' nonzero exactly when p ≢ 1 (mod ℓ)" is false as an integer statement. Integer nonzeroness of the true leaf needs only p ≠ 1 and vq ≠ u. The ℓ-condition governs **filter retention**: retention iff (p−1)(vq−u) ≢ 0 (mod ℓ), since c' is a unit. In this example vq−u = 9 is also ≡ 0, so whether vq−u is guaranteed to be an ℓ-unit is a W024/W022 interface fact I did not re-audit. The parent records this.

## 7. Prior art

The problem is fixed-dimensional weighted-ℓ¹ minimization over the lattice {(c, c d − Q k)} with c ≥ 1, i.e. a best simultaneous approximation with a bounded denominator. Relevant prior art: Lenstra 1983 (ILP and mixed ILP), and Lagarias 1985 (sup-norm best approximations; abstract only, cited in the W025 review). No novelty or priority claim, which agrees with W027.

## Disposition and next obligation

**Accepted:**
- (1)–(3) of W027: exact minimum, constructive witness, polylog bit cost per chart for fixed D, with a constant that is enormous.
- Floor bound, normalization, filter, alpha and localization interfaces.
- Global optimality within the filter-compatible constant-scaling class (§3).
- Inclusion of all W025-review truncation and hybrid options in the same basis.

**Repaired:**
- Substitute singleton coordinates before optimizing; domination is per basis (§4).
- Report the c'=1 restricted optimum as well, for sharing evaluators (§5).
- Reduce to D+1 integer variables via mixed ILP; take e from c.
- Do not compare against the no-filter Q'=1 representation.

**Not claimed:** the true sup of P, cancellation across monomials, chart shifts, variable multipliers, product cost, or factoring complexity.

**Next mathematical cost obligation.** Every member satisfies F(c)/Q ≥ cW/Q ≥ W/Q, so W027 cannot go below the genuine common width A ≈ W/Q. The W025 frontier's explicit-record envelope O~(K+√(KT)) with K≈M still balances at m=1/5, even with ideal T=A. W027 only removes representation inflation. In the thin M=N^(1/4) regime it is at most the review's N^(39/120); its exact exponent is uncomputed, between 15/120 and 39/120, and it cannot change the factoring conclusion there.

The obligation that matters is still a computation of the joint nonlinear anchor family without K explicit records, priced end to end, or a cover with smaller genuine width. Any such evaluator must declare whether it needs a shared c' (§5). **Verified complete factoring improvement: NONE.**

No delegation, install, commit, run, or edit outside this report and its evidence directory.

At handoff, W027.md and every other load-bearing input still matched its frozen hash, with two exceptions. `research/hypotheses/W025.md` and `research/findings/W025-consumer-and-cost-frontier.md` changed concurrently after the freeze, and the changed versions were not read. The review relies on the frozen versions: W025.md `54eefe45…155826`, the same version the W025 review audited, and the frontier note `7c42198b…`. The [delivery manifest](W027-optimal-envelope-review-evidence/delivery-manifest.sha256) records this report as it stood before this paragraph was added.
