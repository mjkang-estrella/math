# H003 conditional noisy-predicate recovery: proposed explicit cost

Native Astra `/root/encoding_review` supplied this construction after reviewing
A1 output. Root transcription of its full algorithm and cost obligations.
Original derivation, now mathematically reviewed with repairs; see
H003-noisy-recovery-disposition.md. Not an optimal literature bound or new ECDLP attack.
No implementation/experiment/Lean theorem. Main gain remains NONE.

Prior framework: [AGS](https://www.cs.tau.ac.il/~safra/PapersAndTalks/hardcore.pdf)
and [Galbraith–Laity–Shani §§3–5](https://arxiv.org/pdf/1607.01842). Proposer's
epsilon^(-6) bound below is its own conservative specialization, not attributed
as a theorem to those sources. It is an alternative to treating the earlier
unverified epsilon^(-11) route as the only explicit threshold.

## Predictor and reduction

Fix E,G and odd prime order q. A fixed-base stateless B_G takes values in[-1,1]
and has full canonical-domain parity correlation
`E_(r in Z_q) B_G([r]G)*(-1)^r >= 2*epsilon`, epsilon>=1/q.
Arbitrary fixed errors are permitted. A1 identity-window exclusions can be
defined as B_G=0: reported numerator N becomes full-domain N/q, not N/(q−|A|).
No claim that the observed tiny data meets an asymptotic/concrete requirement.

For Q=[k]G, return0 if Q=O. Otherwise define
`f0(x)=B_G([x]G)`, `f1(x)=B_G([x]Q)=f0(k*x)`.
All offsets still use the ORIGINAL base G, never replace B_G by B_Q.
Let H=ceil(log2 q), L=4H+4, eta=epsilon/L.

Run HeavyFrequencies on f0 and f1, retaining all amplitudes>=eta, each with
failure budget delta/2. For every pair of nonzero returned frequencies(a,b),
test k'=b/a modq by actual scalar multiplication k'G=Q. Return only a verified
answer; otherwise failure. Base calibration is fully paid, not supplied advice.

Use normalized Fourier transform hat(f)(a)=q^(-1)Σ_x f(x)exp(−2pi*i*a*x/q).
For g(x)=(-1)^x, hat(g)(a)=2/[q*(1+exp(−2pi*i*a/q))], hat(g)(0)=1/q,
and ||hat(g)||_1<=L. The constant-frequency contribution has magnitude<=1/q.
The claimed correlation therefore implies a nonzero |hat(f0)(a)|>=eta;
hat(f1)(b)=hat(f0)(b/k) gives a matching b=a*k. Lists of all heavy coefficients
are sufficient; their phases need not be estimated.

## HeavyFrequencies: interval-energy estimator

For an interval I of integer frequencies define
`D_I(y)=Σ_(a in I) exp(2pi*i*a*y/q)` and `E_I=Σ_(a in I)|hat(f)(a)|²`.
Partition Z_q into H bins: {0}, then cyclic-distance shells
`2^j <= |y|_q < 2^(j+1)`, truncating the last shell. Choose a bin uniformly,
then y uniformly in the bin, so p(y)=1/(H*size(bin)). Independently sample x
uniformly. One sample is
`Z_I = Re(f(x)*f(x−y)*D_I(−y)/(q*p(y)))`.

Claimed identities: E Z_I=E_I, and |Z_I|<=H. For nonzero y the Dirichlet bound
`|D_I(y)|<=min(|I|,q/(2*|y|_q))` combines with shell size<=2*lower_distance.
For y=0 use D_I(0)=|I| and its atom probability1/H. Real f is assumed.

Binary-subdivide [1,q−1]. Retain I if its estimated energy>=eta²/2, with total
estimation error<=eta²/4. Then amplitudes>=eta survive and retained intervals
have energy>=eta²/4. Parseval gives at most4/eta² retained intervals per level.
Enforce this width cap and a total-test cap; abort on violation, bounding work
even when a statistical estimate fails.

Conservative proposed parameters for each search:
`Ntests=ceil(8H/eta²)+2` and
`m=ceil(128H²*eta^(-4)*log(4*Ntests/delta_search))` samples per interval.
Here delta_search=delta/2 for each of the TWO searches; spelling this out avoids
the proposer's overloaded delta notation. Fresh samples for every adaptive test.
Hoeffding is intended to bound statistical error by eta²/8, reserving eta²/8
for numerical error. Union bound over the enforced test count and both searches.

Compute D_I through its geometric-series formula, NOT an |I|-term sum. Certified
complex arithmetic and rounding must be specified and charged. The proposer
has not implemented those or established an explicit bit-precision formula.
The numerator/denominator near-zero cases and y=0 require careful treatment.

## Costs and quantitative gate

Each sample calls f twice; two searches give at most4*Ntests*m predictor calls.
Streaming storage O(eta^(-2)) intervals/frequencies plus point/numerical workspace.
At most16*eta^(-4) frequency pairs need modular inversion/multiplication and
actual scalar verification. One can reuse one inverse per base frequency, but
its computation is not free. All calls form chosen multiples of G or Q; a simple
binary implementation costs O(log q) group operations each. A1 further pays
shifted points, five pointwise phi/character evaluations, and all parameter setup.

`W = W_selection + W_certification + W_setup
     + Q_calls*(C_point+C_B+C_estimator) + L_candidates*C_verify`.

Under polynomial-logarithmic predicate and numerical costs, this yields the
proposed sufficient ~epsilon^(-6) total-work exponent; epsilon=q^(-beta) then
requires beta<1/12 to beat sqrt(q), subject to all setup/memory/success conditions.
This is NOT necessary/optimal and hides large log powers/constants; it provides
no finite-size speed guarantee. No GPU conversion or benchmark inference.

If B is randomized, independent fresh coins per invocation, including repeated
points, make the estimator target its mean function. Do not majority-amplify
arbitrary-error points or assume errors at distinct points independent. Stateful
query-sensitive predictors are outside the argument. Exact sampling/random bits
and finite precision remain implementation costs.

Later SFT constructions need exact hypotheses: [Akavia COLT2010](https://people.csail.mit.edu/akavia/akaviaCOLT10.pdf)
has Fourier-l1/random-noise qualifications, not a free improved bound for this B.

## Root's initial objections/questions for independent review

1. Check Fourier signs/normalization, dyadic bin count including {0}, boundH,
   adaptive fresh-sample union bound, width and test caps, list sizes, all costs.
2. Supply a realizable certified arithmetic/precision bound for the weighted
   Dirichlet estimator; no real-number or transcendental constant-time oracle.
3. Is the positive-sign premise unnecessarily restrictive? The same triangle
   argument appears to work from ABSOLUTE full-domain correlation>=2epsilon.
   If so, a known orientation is unnecessary for this algorithm, though a genuine
   magnitude guarantee and full-domain/memory costs remain necessary. Correct
   the earlier 'orientation required' gate narrowly if confirmed.
4. Distinguish a valid sufficient conservative construction from prior-art novelty,
   optimal epsilon exponent, and actual usefulness of A1. No larger A1 run or
   recovery implementation authorized until these gates and a concrete threshold
   survive independent review.
