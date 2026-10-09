# H039 information operators — raw Grok report

Unaccepted proposer report; consult H039-information-disposition.md for corrections.

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h039-nonlinear-information-grok-20261008-r1`

Provider: grok / grok-4.7. Terminal: completed.

No survivor. Three public recovery operators fit the lens, and none has a gain source against negation-rho or x-only interleaved BSGS. Verified improvement stays **NONE**. The square-root reference is unchanged.

Memory from earlier sessions is labeled below and is not evidence. This pass did not read other H039 proposals, did not touch the H038 Farey/height-lattice role, and did not run anything.

## What was read

Accepted scopes: H002 predicate/circuit gates and the learning-card corrections, H013 group-action features, MCL disposition, and coordinate cards, H017 information disposition, H019 information disposition, H026 information scope and window conversion, H038 implicit disposition and bounded-recovery graphs. H038’s raw Gauss-period and convolution text was used only to avoid repeating those priced schedules.

Primary, this pass:

- Mérai–Winterhof, arXiv:1509.06909v2, full text. Theorem 1 needs an Edwards model with a pole at an ideal point. Theorem 2: a nonconstant f of degree deg(f) < |G|^δ, δ<1, on the power generator of multiplicative order t, has linear complexity ≫ t / (|G|^{2/3} (deg f)^{1/3}).
- Mérai, arXiv:1609.03305, Theorem 1, Algorithm 1, and the addition identities (4)–(5). Seven consecutive abscissae determine a curve and a step (x(G), y(G)^2, A, B) over Q or Z/mZ. The index is not an output. The proof was truncated after the linear system, so nothing past that is used.

Kohel–Shparlinski is used only as already scoped in H026 (unnormalized 2d√p, nondegeneracy required, not every rational expression). It was not re-opened.

## Operator 1 — integer-halving chain

**Procedure.** Let the unknown representative be k ∈ {1,…,q−1} and let ι = 2^{-1} mod q. Set Q_0 = Q. At step i compute the two rational halves A = [ι]Q_i and B = [ι](Q_i − G). Emit bit b_i from a public predicate and set Q_{i+1} to A or B accordingly. After t = ⌊log_2(q−1)⌋+1 steps, assemble k̂ = Σ b_i 2^i and accept only if [k̂]G = Q.

Named predicate used to make the operator definite: b_i = 0 when x(A) < x(B), treating O as larger than every field element, and breaking a tie by the same comparison on y.

**Gain source, if the bits were the integer LSB at every residual.** Each step is one known-scalar multiplication. The whole chain is polylog group operations, against about 0.886√q negation-rho iterations.

**Paid.** ι is free. Each step pays a scalar multiplication, coordinate comparisons, and one final verification. A mismatch pays the whole chain and returns failure. No training set. No retry tree is part of the operator: one wrong bit fails verification.

**Prior art.** This is H002’s predicate bridge with the predicate named. H002 L2 already gives exact zero correlation for every function of x-only dilations c·[k]G against LSB and against the half-predicate. The comparison here also sees the translate by [ι]G, so L2 does not apply. Mérai–Winterhof Theorem 1 does not apply either: a prime-order ordinary curve has no rational point of order 4, so it has no Edwards model over F_p.

**Screen for rational-character predicates.** Define λ(k) = (−1)^k on representatives 0,…,q−1. Its normalized Fourier coefficients on Z/qZ are

|S(a)|/q, |S(a)| = 1/|cos(π a/q)|,

and the normalized L1 norm is O(log q). The zero frequency contributes O(1/q). Therefore any h whose nontrivial group-Fourier coefficients are O(d/√q) has correlation O(d log q / √q) with λ. That covers one nondegenerate rational character, and a boolean function of s such characters up to a factor 2^s s. The bound exceeds 1 once s is about (1/2)log_2 q, so it is not a universal nonlinear exclusion.

A correlation that small means the named comparison is not identically the LSB. One deterministic chain then succeeds only on the scalars whose entire halving orbit matches. That density is not estimated here, and no gain follows from it.

**Unsupported assumption.** x(A) < x(B) equals the integer LSB of the current residual at every step.

**Falsifier, not run.** On [2]G the true bit is 0 and the two halves are G and [ι]G. The predicate fails if x([ι]G) < x(G). On [3]G the true bit is 1. Two known scalars decide exactness for this predicate. A pass would not create an advantage bound.

## Operator 2 — consecutive-window algebra

**Procedure.** From Q form x(Q+[j]G) for j = 0,…,6 by six additions. Substitute that window into Mérai’s Algorithm 1. Verify any returned point by a scalar multiplication.

**What the operator returns.** Theorem 1 recovers a model of the step and the curve, over Q or over Z/mZ with p dividing m. In this project the curve, p, and G are already public. The system (5) solves for (x(G), x(G)^2, A, B, y(G)^2, x(G)^3). The index k is not a variable.

**Gain source.** None. Extending the window is ordinary addition. Recovering G from a window of translates of Q is recovering a public input.

**Paid.** Six additions plus the 5×6 integer determinant/gcd arithmetic in Algorithm 1, then one verification if a candidate point is emitted. Failures are the cases already excluded by that theorem (repeated abscissae, a translate equal to ±G).

**Prior art.** Mérai, arXiv:1609.03305, Theorem 1 and Algorithm 1, read this pass. The paper’s hidden object is a secret curve and secret seed of an LCG. That hypothesis is false for this target.

**Unsupported assumption.** That the same linear system isolates k if the window is centered at Q. The displayed unknowns do not include k.

**Falsifier.** Substitute the public symbols x(G), A, B, y(G)^2 into (5) with x_i = x(Q+[i]G). The identity is the addition law in the x-coordinate. It holds for every Q and does not cut the scalar down.

The same window does not revive H017’s parked polynomial-agreement decoder. Exact equality x([k]G) = P(k) for a polynomial P over F_q has to satisfy the duplication formula

x([2]R) = (x^4 − 2Ax^2 − 8Bx + A^2) / (4(x^3+Ax+B)).

Leading terms give the necessary condition 2^{d+2} = 1 in the prime field when deg P = d ≥ 1. That is only a constraint, not a claim that every sparse exponential expression is impossible. Approximate agreement stays the H017 bridge and is not resubmitted.

## Operator 3 — short nonlinear statistic, then a named decoder

**Procedure.** Fix s = O(1) and set

z_j(P) = (x(P+[j]G)/p), j = 0,…,s−1,

by s additions and s Legendre symbols. Let F be either the majority bit or the full product. Decoder, in three mutually exclusive versions:

1. Coset decoder: treat F([k]G) as a multiplicative character of k and run the H013 calibration-plus-coset-BSGS schedule.
2. Dictionary decoder: precompute F([n]G) for T known scalars and match F(Q).
3. Chain decoder: use F as the bit in Operator 1.

**Gain source.** Absent in all three versions.

Version 1 is H013’s conditional reduction. A product of these Legendre symbols is one Legendre symbol of a rational function of degree O(s), so it stays inside a single character sum. Majority expands into 2^s such sums. No identity makes the correlation larger than the accepted O(q^{−1/12} log^{1/3} q) ceiling for an additive phase of x, and that ceiling is not a construction of a usable correlation.

Version 2 with T stored keys has success at most T/q on a uniform unmatched target if F is treated as a label, unless distinct scalars share a label and the collision is solved by another method. Shared labels are a fiber search. The fiber of a coordinate statistic is not shown to be a coset, an interval, or any other set with a cheaper internal solver. Covering the group returns the usual T + q/T shape before feature and verification cost.

Version 3 inherits Operator 1’s screen.

**Paid.** s additions, s symbols, and either H013’s calibration sample (two scalar starts per progression block, character-to-phase table, coset BSGS, verification, failure fallback to a full baseline) or a T-row table plus lookup. Training labels are known multiples, not free. Samples along one orbit are not an iid training set. Adaptive choice of the next j does not remove the per-step correlation limit for a fixed F.

**Prior art.** H013 MCL reduction and landmark dictionary. H019’s elementary bound that a product of a fixed number of binary digits has Fourier L1 O(log^{O(s)} p). H038’s convolution identity: one point-count aggregate of a translate pair is one integer of size O(√p) under the stated coefficient bounds, and for the even coordinate factors it is a function of x(Q), which is already public. A second evaluation of a function of the known point does not encode k.

**Unsupported assumption.** F([k]G), or an adaptively chosen tuple of such values, equals a character, an interval index, or the LSB often enough that version 1 or 3 beats a full baseline after calibration failures.

**Falsifier.** For version 3, the same two-scalar test as Operator 1. For version 1, the H013 gate already stated: with C_pre the full attempt cost and s the success probability, a gain needs C_pre < s W_0. No feature in this family has a proved s large enough. A finite sample is not accepted as that proof.

## What this does not close

- A boolean function of s ≈ (1/2)log_2 q coordinate bits, or an adaptive rule whose description grows with q. The character-sum union bound becomes vacuous there. No such formula is supplied, and a search over that grammar is H002 L2 without a new predicate.
- H026’s missing target-dependent fibre signal and useful PRF-action decoder. No fibre or PRF was constructed.
- H013’s unused opening for a compressed Couveignes–Lercier basis with sparse index extraction. Writing the degree-q kernel element is still Ω(q) before any index is read.
- H038’s missing o(k_e) trace of a pairing value. The priced Gauss-period split was not reopened.
- Long or adaptive relation graphs. Those sit with the other lane.

Mérai–Winterhof Theorem 2 blocks a short linear recurrence for a power generator f(e^n G). It is a predictability lower bound, not an index-recovery algorithm. The ordinary addition recurrence for consecutive x([n]G) is short and nonlinear, and it computes the next point rather than the index.

## Wave report

- Best supported complexity: generic square root. Low memory: negation-rho, heuristic (1+o(1))√(πq/4) iterations on the negation quotient. High memory: x-only interleaved negation BSGS.
- Verified improvement: **NONE**.
- Hypothesis under test: none promoted.
- Evidence for a gain: none. Evidence against these three operators: the halving predicate is not the LSB under the rational-character screen and is one known-scalar comparison away from an exact-match kill; the seven-term window solver returns the public step, not k; a short Legendre statistic does not feed H013, a dictionary, or the halving chain any cheaper than the schedules already priced.
- Next conclusion-changing step: a named branch predicate that survives the checks on [2]G and [3]G and has a proved match density along whole halving orbits, with chain, failure, and verification cost included. Until that predicate exists, the two-scalar check is the only falsifier worth stating, and it was not run.

