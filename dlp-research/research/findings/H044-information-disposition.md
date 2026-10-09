# H044 information review: exact identities, missing signal and decoder

2026-10-09 UTC. Raw Factory Fable report and its task ID are retained in
H044-information-fable-raw.md. Root and native Astra reviewed the mathematical
claims; native Sol independently reviewed the decoder/cost claims. The report's
decoder domination, universal feature closures and comparator reduction are
not accepted. No experiment, new Lean claim or verified complete-work gain.
The working exponent remains 1/2. This is paper analysis, not a lower bound
against arbitrary coordinate-aware algorithms.

## Pair correlation: necessary spectral mass is not a decoder

Let q be an odd prime subgroup order, F:Z/qZ -> C with |F|<=1, and
c_a=E_n F(n)e(−an/q). With the raw report's convention, the centered additive
correlation has the corrected sign:

    R_tilde(tau)=E_n F(n)conj(F(n+tau))−|c_0|²
                =sum_(a!=0) |c_a|² e(−a*tau/q).
    sum_tau |R_tilde(tau)|² = q*sum_(a!=0)|c_a|⁴
                           <= q*max_(a!=0)|c_a|².

The last step uses Parseval and E|F|²<=1. Consequently t distinct centered
peaks of height at least epsilon require t*epsilon²<=q*max|c_a|². The named
H041 ideal peak-search criterion t*epsilon²>sqrt(q) thus requires a coefficient
larger than q^(−1/4). This does not locate a coefficient, calibrate its phase,
price its discovery or establish a recovery algorithm. Two algorithms can
share a necessary signal threshold while having different available inputs
and full costs. Withdraw the claim that first-order decoders dominate all
second-order decoders or eliminate their separate review.

On the nonzero scalar multiplicative group, use

    R_times(u)=E_(n!=0) F(un)conj(F(n))
              =sum_chi |c_hat_chi|² chi(u).

For k,c!=0, E_(a!=0) f(aQ)conj(f(acG))=R_times(k/c).
Subtract the trivial-character term before applying the analogous inequality
with q−1. Constant features refute the uncentered version. The raw
q/(t*epsilon²) invoice remains only a modeled search/sample stage, omitting
peak construction, separation gaps, recovery, false candidates and confidence.
The H013 bounds remain confined to their originally checked observables.

## Quadratic phase: conditional differencing identity

Define S_F(alpha,beta)=E_n F(n)e(−(alpha*n²+beta*n)/q), alpha!=0.
Expanding the square and putting the second index n+tau gives exactly

    |q*S_F|² = sum_tau e((alpha*tau²+beta*tau)/q)
                 *sum_n F(n)conj(F(n+tau))e(2alpha*tau*n/q).

If the absolute value of the inner sum is bounded by B_tau for every
nonzero tau, the triangle inequality and |F|<=1 imply

    |S_F|² <= (q+sum_(tau!=0)B_tau)/q².

In particular B_tau<=4d*sqrt(p) implies
|S_F|<=sqrt(1/q+4d*sqrt(p)/q). Here p is the base-field size; d must price the
actual translated-product function and its character conductor, not an
unrelated polynomial description. Exceptions, poles, subgroup restrictions,
degenerate characters and Fourier expansion norms must all be checked.
No such hypothesis is established here for every bounded observable.

For invertible u modulo q, change of variable proves

    S_(F(u dot))(alpha,beta)=S_F(alpha*u^(-2), beta*u^(-1)).

Thus these dilations permute quadratic-spectrum magnitudes. The zero
multiplier and arbitrary changes of curve/feature need separate treatment.

The proposed consecutive-window FFT would need a coherent local signal,
a bound on other peaks, paid feature evaluation and adequate numeric precision.
A nonzero global S_F alone supplies none of these short-window guarantees.
For a purely logical counterexample, multiply the exact chirp by the indicator
of a scalar interval of length floor(epsilon*q). Its global coefficient is
floor(epsilon*q)/q, yet most translated windows of length N much smaller than
q miss that interval entirely. This supplies no cheaply evaluable point
feature; it shows which inference does not follow from the coefficient alone.
If they are separately supplied, resolving 2alpha*k within O(q/N) gives a
short arithmetic progression of possible k with known step (2alpha)^(-1),
not a secretly assumed input range. Its residual BSGS and verification are
paid. The stated N+sqrt(q/N) is a conditional operation count, with FFT logs,
feature cost, scalar updates, confidence, storage and failed recoveries omitted.
It does not certify a q^(1/3) ECDLP solver.

Within that stated noise model, epsilon=q^(−b) requires roughly N>=q^(2b)
up to confidence factors. The q^(1/3) choice needs b<=1/6 with margins;
1/6<b<1/4 can still allow a weaker exponent improvement in the same conditional
model. An O(q^(−1/4)) ceiling prevents an exponent gain by this sampling
argument, not every finite constant gain or every other decoder. Naively
searching q² coefficient pairs is one search strategy, not a lower bound.

The suggested first-order mixed-sum falsifier is invalid. For the abstract
sequence F(n)=e(alpha*n²/q), |S_F(alpha,0)|=1, while every normalized linear
Fourier coefficient has magnitude q^(−1/2). To see the latter, square the
unnormalized sum; each nonzero shift has a nontrivial linear phase and sums
to zero, leaving q. This is a counterexample to the proposed implication,
not a cheap ECDLP feature: evaluating this F from a point has not been supplied.
The differencing route instead needs bounds for the translated products.
To force |S_F|=o(q^(−1/6)) by that route, their average bound must be
o(q^(2/3)), with the appropriate confidence margins, not merely q^(3/4).

## Source and division-polynomial scope

Root read [Kohel–Shparlinski, Section 3](https://www.i2m.univ-amu.fr/perso/david.kohel/pub/character.pdf).
The source defines rational-function degree by its polar divisor and derives
mixed additive-character estimates through conductors. Its subgroup step
averages extending characters; this does not introduce an index multiplier.
Application still needs nondegeneracy of the actual Artin–Schreier character;
nonconstant notation alone is insufficient when a function is h^p−h+c.
The H041 separated-pole checks are scoped sufficient conditions, not a theorem
about all cheaply computable high-degree features.

Root also read [Shparlinski–Stange, Lemmas 2, 4–5 and Section 6](https://arxiv.org/html/0912.5246v4).
Its mixed multiplicative-character bounds require the stated non-power
condition. Section 6 says their method fails for the analogous additive
index-sequence problem. It establishes neither absence of all other bounds
nor an exhaustive current literature claim. Point-variable and index-variable
sums must not be interchanged. Lemma 2 supplies the multiplication identity;
division requires a nonzero denominator. No positive chirp premise follows.

In particular, with the relevant nonzero values and conventions,

    Psi_n(kG)=Psi_(nk)(G)/Psi_k(G)^(n²).

Here n² is quadratic in the public multiplier n, not directly in the unknown
scalar k. k=0 needs separate dispatch; n=0 modulo q makes the point feature
trivial. The feature's cost and conventions at zeros and poles must be given.
For ordinary odd n prime to p, the polynomial-in-x degree (n²−1)/2 and its
polar degree as a function on E (n²−1) are different conventions. No numerical
constant is accepted by silently exchanging them. Thresholds where a degree
upper bound becomes inconclusive supply no evidence that correlation exists.

## Learned comparator: average advantage is not adaptive-query advantage

The submitted binary search is not a proved reduction. Common translation
of two scalars preserves their cyclic difference. It samples one fixed-gap
diagonal, not independent uniform pairs; held-out average advantage can be
absent or reversed on that diagonal. Common multiplication likewise retains
a ratio and does not preserve canonical integer order. Wrap corrections and
chosen-multiplier citations do not establish the required conditional law.

A valid noisy binary search needs a justified re-randomization, appropriate
conditional advantage at every adaptive stage, confidence amplification and
paid point generation/evaluation. The raw comparison count and one-addition
invoice do not follow. Training, validation, inference and failures are also
unpriced. No learner or measured advantage is supplied. Neither this omission
nor a hard-core theorem for a different oracle proves the raw universal
classification of every learnable target. A public function of Q can carry
information; efficient extraction is the issue, not whether it is a function.

## Constructive follow-up and present disposition

Root identified a different conditional decoder question during review:
arbitrary public d queries to f(Q+dG), after quadratic demodulation, give a
global linear Fourier coefficient at 2alpha*k whenever the named S_F exists.
Could a primary-source sparse Fourier list-recovery algorithm on Z/qZ find
it with a competitive explicit epsilon dependence? Such a decoder could
avoid the short-window assumption, while still requiring a real public
feature, a known alpha/beta, all query/precision costs and paid candidate
verification. Native Astra located the exact source theorem; root independently read and
checked the Boolean lift. H044-global-chirp-decoder.md records a conservative
soft-O(epsilon^(−11)) conditional operation bound, including paid queries and
candidate verification. No correlated feature or actual improvement is supplied.

Native Sol separately checked the learned-comparator reduction and the
decoder invoices. Initial report retention is not acceptance. No experiment
is admitted: the next conclusion-changing evidence is a specified efficient
public signal with a justified recovery algorithm, or a source-supported
conditional reduction that changes its exact admission threshold. Existing
H034 cap is untouched; no runs, imports, training or spectral sweeps.
