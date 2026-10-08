# H019 information proposals: scoped review and rejected exclusions

2026-10-08. Improvement **NONE**; no numerical experiment admitted.
Factory Fable's independent proposal and Claude Opus's independent probability
review are retained verbatim in H019-information-fable-raw.md and
H019-information-opus-review-raw.md. Exact task IDs/briefs are in the H019
hypothesis records. Both completed, terminal results read, no pending children.
Root independently checked the counterexamples and algebra below. These are
paper results, not new Lean claims. The reviewer made no source fetches; its
memory-only literature assertions remain unverified.

## A1: prediction advantage is not a universal information budget

For uniform binary X, let P(Y=1|X=1)=2e and P(Y=1|X=0)=0, 0<e<1/2.
Predicting X by Y has accuracy 1/2+e but

    I(X;Y)=H2(e)-H2(2e)/2=e+O(e²).

Thus the proposed universal bound 3e² bits per answer is false. Furthermore,
advantage on a particular predicate of K need not control I(K;Y), much less
adaptive conditional information. Deterministic coordinate features can have
entropy without being useful scalar predictors. The full public point Q=[K]G
already determines K information-theoretically. A Fano argument charging only
new queries cannot be an ECDLP computational lower bound with Q unaccounted for.
Correction to the reviewer: x(Q) identifies the pair ±K, not literally all of K.

A valid narrow oracle model has no other unknown-dependent side information,
uniform K, and every answer is one requested bit XOR fresh independent noise
with crossover 1/2-e. Channel capacity and Fano then imply

    T (1-H2(1/2-e)) >= (1-P_error) log2(q)-1.

Adaptive query choices do not exceed this channel capacity. This is not the
coordinate ECDLP model. The reviewer's proposed automatic replacement of the
denominator by 2e also requires an explicit conditional channel model; it is
not adopted as a general predictor theorem. Neither e*sqrt(m) aggregation nor
a universal e>q^(-1/4) threshold follows.

## A2/A3: narrower Fourier statements, not decoder exclusions

Any imported mixed additive-character estimate needs its exact source theorem,
centering/DC terms, poles, effective degree after pullback, and nondegeneracy of
every actual frequency combination. Individual nonconstant features can cancel
in a combination. Pullback by [c] can increase degree by c². Both reports cite
the needed mixed bound from memory. A multiplicative-character theorem cannot
replace it. Consequently that bound is conditional here, not newly established.

Even a valid per-correlation estimate says nothing universal about nonlinear,
multi-query, or raw-coordinate algorithms. If normalized Fourier coefficients
are bounded by B and total nonzero-frequency energy is E, their support has size
at least E/B². The reviewer's flat-spectrum claim omitted a LOWER bound on E;
Parseval's upper bound alone does not supply it. Flatness does not imply a BSGS
runtime lower bound.

For any |h|<=1 on Z_p, normalized Fourier L1<=sqrt(p), by Parseval and
Cauchy-Schwarz. The raw Thue-Morse L1 estimate p^0.79 is therefore impossible.
The reviewer's substitute literature exponent is memory-only and is not used.
H018's rejected N2 dichotomy must not be cited as an accepted obstruction.

One elementary lemma survives. Put B_j(x)=(-1)^floor(x/2^j) and T=2^(j+1).
Its normalized period-T Fourier coefficients vanish at even frequencies and
have magnitude 2/(T*|sin(pi*r/T)|) at odd r, hence L1=O(j+1). Restrict the
periodic expansion to x=0,...,p-1. The normalized Dirichlet kernel obeys

    |D_p(theta)| <= min(1,1/(2p*||theta||)).

Summing this bound over the p equally spaced Fourier frequencies costs O(log p)
uniformly in the shift. The triangle inequality therefore gives
L1_Zp(B_j)=O((j+1)log p), or O(log² p) for the relevant binary digits.
Higher digits are constant. Products of a fixed s bits have L1=O(log^(2s)p)
by convolution submultiplicativity. The Z_p mean need not vanish. This modest
Fourier-size lemma does not close a class of attacks.

## C1: repaired window identity, no justified screening experiment

For normalized Fourier transform on Z_q, define

    K_L(a)=|sum_(j=0)^(L-1) exp(2*pi*i*a*j/q)|²/L,
    F_L=sum_a |hhat(a)|² K_L(a).

This is an exact nonnegative weighted autocorrelation identity. The raw lower
bound on all |a|<=q/L is false: L=2, a=(q-1)/2 gives
K_2(a)=1-cos(pi/q), tending to zero. Taking h=tau to be that unit character
gives correlation one despite the vanishing window statistic.

On the narrower band |a|<=q/(2L), K_L(a)>=4L/pi². If h is centered with
E|h|²<=1, B>0, L<=q/(2B), and e=|E h*conj(tau)|, the reviewed repair is

    e <= (pi/2)*L1(tau)*sqrt(F_L/L)
         + ||tauhat restricted to |a|>B||_2.

Proof: each low-frequency coefficient of h is at most
(pi/2)*sqrt(F_L/L); sum against tauhat and bound the tail by Cauchy-Schwarz.
MSB is not exactly bandlimited. Uncentered h adds a DC contribution L|mean|².
No null distribution, test power, or claimed standard deviation was derived.
Random-point sampling, all window points, feature evaluations and rejection
costs must be charged. No concrete positive feature was supplied, so this is
not permission for a broad sweep.

## Remaining cost claims

Under the SPECIFIED conditional cost m²/rho²+sqrt(q/m), write m=q^d,
rho=q^(-b). An exponent improvement requires d>0 and b<1/4-d. Combining a
separate conditional upper bound b>=1/12 leaves a window d<1/6, not a positive
construction. It is neither the sole opening nor a universal boundary.

W log(W)/e² can be a sufficient uniform-convergence sample bound for specified
model classes, not a necessary training lower bound. An iid worst-case
mean-discrimination task can require order e^-2 samples at fixed error, but
ECDLP candidates can instead be checked directly against Q. Gradient methods
are not automatically statistical-query algorithms without precision/noise
conditions. Unread nonuniform-circuit or decoder exponents are not accepted.
Genus-2 point counts, low-entropy walks and other broad exclusions need their
own arguments; none is furnished here.

## Decision and source limits

No proposed observable has a supported positive scalar signal. Preserve the
narrow elementary lemmas and reject the blanket impossibility claims. Fable's
reported primary-source access varied (some full text, some abstract only);
Opus fetched none. This disposition uses independently checked elementary
derivations, not their memory-only literature claims. No claim that all
coordinate, learning, spectral, or nonalgebraic approaches are closed.
Next useful work is a specified positive mechanism with charged extraction,
not more universal exclusion infrastructure.
