# H002 predicate and circuit gates

Status: scoped analytical negative findings and unresolved candidates, no new
ECDLP algorithm. Native Astra `/root/encoding_review` independently reviewed G1/G2;
Factory Opus reviewed L1/L2 in `ecdloop-h002-predictor-reduction-review-20261008-r1`.
Raw predictor report is retained separately and is NOT accepted wholesale.

## G2: large coordinate-interval Fourier spike fails its stated gate

Let H=⟨G⟩ have prime order q, over F_p with p>2. Set f(m)=1_I(x(mG)) for
nonidentity points, and f(0)=0. For nonzero scalar frequency a, expand 1_I in
additive field characters. The zero field-frequency term contributes −|I|/p.
For each nonzero field frequency the mixed elliptic character sum has magnitude
≤3√p: x has one pole of order2. Every H-character extends to E(F_p); averaging
over characters trivial on H preserves this bound. The normalized interval
Fourier l1 norm is ≤1+log(p). Consequently

`|Σ_m f(m) exp(−2πiam/q)| ≤ 1+3√p(1+log p)`.

For a ±1 interval predicate and an arbitrary bounded identity convention use the
corresponding factor2/O(1) adjustment. The asymptotic bound is unchanged. When
q≍p it excludes the proposed ≫q^(3/4) spike. Source: [Kohel–Shparlinski,
Theorem1 and Lemma3](https://www.i2m.univ-amu.fr/perso/david.kohel/pub/character.pdf).
Root retrieved the primary text and checked the subgroup averaging and trivial
frequency term. This is our application of those results, not a quoted theorem
about ECDLP algorithms. It excludes this strong-spike bridge, not arbitrary
coordinate features or all statistical reconstruction methods.

Calibration also matters: f_Q(r)=f_G(kr) gives hat(f_Q)(b)=hat(f_G)(b/k).
A known base frequency a matched to b recovers k=b/a, up to ambiguities needing
verification. A target spike alone has no base label. Random samples cost scalar
multiplication; a short consecutive FFT does not resolve arbitrary frequencies
modulo q automatically. Charge calibration, precision, sampling, frequency
reconstruction, restarts and verification. No finite FFT experiment is needed
to resolve this particular asymptotic gate; no source-impossibility claim beyond it.

## L2: exact negation null, with scope

For odd q, pair k with q−k among1,…,q−1. Their parities and half predicates are
opposite, while every x(c_i[k]G) equals x(c_i[−k]G), including identical treatment
of identity. Therefore every deterministic function of these views has exactly
zero signed correlation with these predicates over the complete nonzero group.
The same holds in expectation for randomized predictors with the same output
distribution on identical features. Including k=0 adds only its1/q contribution.
Finite random samples can show chance correlations; this alone is NOT a bug.

This elementary pairing argument is independently checked by root. It excludes
the x-only multiplicative-view grammar for these odd predicates, not shifted
x(Q+jG), y-dependent features, or negation-even scalar predicates. Even predicates
would still need a full recovery reduction. No generic learning impossibility
follows. This result needs no huge toy training run.

## Predictor review: useful references, limited adoption

The reviewer inspected [Håstad–Näslund](https://www.csc.kth.se/~johanh/hnrsaacm.pdf)
and [Akavia–Goldwasser–Safra](https://www.cs.tau.ac.il/~safra/PapersAndTalks/hardcore.pdf).
Retain polynomial reconstruction as a candidate bridge under its fixed predictor,
average advantage and query hypotheses. The proposed epsilon^(-11) sufficient
route is a reviewer derivation requiring further check, NOT an optimal exponent.
Its absence of a better source is not proof that no better reduction exists.
Likewise its Fano bound requires a precisely specified noisy oracle; it is not a
universal lower bound on structured coordinate predictors. Do not adopt blanket
beta≥1/4 rejection or beta≥1/22 'no proven solver' claims.

Random-base learning bounds do not rule out a particular fixed base or features
depending on it. Multi-view overlap is a leakage control, not automatically a
usable label leak for every predicate. Any accepted learner must charge labels,
selection/training, storage, certification, feature/query-point computation,
reconstruction, list verification and failures; compare applicable automorphism
baselines and matched preprocessing. The raw proposed large pilot is not funded.

## G1: compact segment circuit remains a missing primitive

Use F(X)=∏_(1≤j<T)(X−x(jG)), T<q; handle giant-step identity separately. Root
membership does not return j or its sign. The complete proposed gain requires
`C_build+(q/T)(C_giant+C_eval)+C_index+C_verify = o(sqrt(q))`.
Explicitly generating T roots/moments fails when T≫sqrt(q). But high
Berlekamp–Massey recurrence complexity does NOT refute short arithmetic circuits:
X^N−1 has an O(log N) circuit despite a sparse coefficient sequence with long
finite-prefix recurrence complexity. Reject only the tested recurrence model.
Next gate is an explicit uniformly cheap circuit construction AND index recovery;
no broad circuit search or Lean infrastructure authorized.

Best supported ECDLP complexity remains the applicable classical square-root
baseline. Verified improvement NONE. Next concrete evidence: corrected EDS
identity/bias diagnostic, and marked-surface representation review; no GPU claim.
