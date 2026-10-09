# H045 recurrence signals: scoped bounds and an unpriced exact observable

2026-10-09 UTC. Factory Opus's report and task ID are retained in
H045-public-signal-factory-raw.md. Native Astra independently reviewed recurrence
mathematics; native Sol reviewed evaluation and recovery costs and primary
sources. Root checked the identities and source scopes below. No verified
ECDLP improvement, experiment or new Lean claim. Working exponent remains1/2.

## Miller coefficient: a valid bounded-character screen

Use the accepted H027 ordinary setting, with q!=p, b(P)=a_P/q in Fp and
b(O)=0. The normalized Miller coefficient has defect

    b(P+T)=b(P)+b(T)−lambda(P,T),

with vertical and identity conventions handled separately. For nonzero
odd-order T, the chord slope as a rational function of P has simple poles
at O and −T; its tangent value at T is removable. For nonzero additive
frequency t, these pole orders prove Artin–Schreier nondegeneracy. Apply the
H044 differencing identity to F_t(n)=psi(t*b(nG)). For every nonzero shift,
the remaining sum is a mixed group/additive-character sum of the slope.
Its absolute bound is 4sqrt(p)+2, including the two exceptional point values.
Thus the independently derived finite estimate is

    |S_(F_t)(alpha,beta)|²
       <= 1/q+(q−1)(4sqrt(p)+2)/q²
       <= (4sqrt(p)+3)/q.

For Phi=sum_t c_t psi(t dot), triangle inequality gives the Fourier norm
L=sum_t|c_t| factor in the amplitude bound. Require alpha!=0 for the stated
quadratic-decoder application: the t=0 component is then handled by the
quadratic Gauss sum. The raw claim for every (alpha,beta), including (0,0),
fails for constant Phi. Nonzero linear frequencies may be treated separately.
The difference between two normalized defect solutions is an additive
homomorphism into Fp, hence zero under q!=p. Uniqueness supplies no decoder.

Root and Astra read [Kohel–Shparlinski, Section3](https://www.i2m.univ-amu.fr/perso/david.kohel/pub/character.pdf).
The conductor estimate and subgroup character averaging provide the source
ingredient; the displayed application is our derivation. The pole test matters:
arbitrary rational perturbations cannot simply inherit the same constant or
nondegeneracy. Root also reread the retained Rück paper at /tmp/h027rev/ruck.txt;
its recovery theorem concerns p-primary divisor classes, not this ordinary q.
H027-miller-priorart-reconciliation.md retains source provenance and PDF hashes.

## EDS normalization: two differences, with explicit exceptional shifts

Adopt the corrected H002 pointwise normalization, q odd and
gcd(q,p−1)=1. It satisfies phi(nP)=phi(P)^(n²)*Psi_n(P); phi is nonzero away
from O and is assigned zero at O. The division-polynomial identity implies

    phi(P+T)*phi(P−T)
      =phi(P)²*phi(T)²*(x(T)−x(P)).

For nonzero shifts h1,h2, write M=(h1+h2)/2, D=(h1−h2)/2 in the subgroup.
When M,D are nonzero, the second multiplicative difference is

    phi(P+h1+h2)*phi(P)/(phi(P+h1)*phi(P+h2))
      =phi(M)²/phi(D)² * (x(M)−x(P+M))/(x(D)−x(P+M)).

Here M!=±D. Its two zeros and two poles are distinct and simple. The
degenerate expressions are instead

    h1=h2=h:  phi(h)²*(x(h)−x(P+h)),
    h1=−h2=h:  1/(phi(h)²*(x(h)−x(P))).

They also have a simple zero or pole. For any nonprincipal multiplicative
character extended by zero at zero, these valuations establish geometric
nonpower, regardless of the character order. Zero shifts give trivial
differences and are counted separately. Two Cauchy–Schwarz/differencing steps
therefore give the conservative bound

    |S|⁴ <= (2q−1)/q² + (q−1)²*(4sqrt(p)+O(1))/q³.

For q~p this is |S|<=(sqrt(2)+o(1))*q^(−1/8). Principal-character components
need the separate quadratic-Gauss estimate with the omitted identity point;
for alpha!=0 their amplitude is at most q^(−1/2)+1/q. Triangle inequality
extends the result with the actual multiplicative Fourier L1 norm.

Root and Astra read [Shparlinski–Stange, Lemmas4–5](https://arxiv.org/html/0912.5246v4).
Use the already-recorded geometric nonpower interpretation, not the defective
literal wording involving roots in a full algebraic closure of the function
field. The simple valuations above meet the needed condition. These sources
provide character-sum estimates, not a new scalar-recovery theorem.

## Higher characters also admit a scalar reindexing

The raw assertion that order m>=3 cannot reduce to a rational character is
false. Root supplied, and Astra independently checked, the correction:
if m=ord(chi) divides ell² and gcd(ell,q)=1, then

    chi(phi(R)) = chi(Psi_ell([ell^(-1) mod q]R)).

Taking ell=m works; ell=2 already covers order four. This is a reindexing
on the finite subgroup, not a rational inverse of the multiplication morphism.
For fixed ell prime to p, translated ell-torsion zero divisors are disjoint
under nonzero q-shifts. A degree-dependent one-difference bound gives
O(ell*q^(−1/4)) when q~p. Growing ell carries its degree/evaluation dependence;
it does not invalidate the order-uniform two-difference screen above.

A joint Miller/EDS feature requires its actual joint Fourier L1 norm and a
mixed conductor calculation. The second additive defect is
lambda(P,h)−lambda(P+t,h), potentially with four simple poles, giving generic
wild conductor contribution eight. The raw 4sqrt(p) constant cannot simply
be reused for the mixed product. No universal perturbation theorem is accepted.

## What these ceilings do and do not say

Bounded-L1 instances cannot meet the particular strong signal regime
epsilon=q^(−gamma), gamma<1/22, used in the conservative H044 AGS invoice.
That regime is SUFFICIENT, not necessary: failing it does not prove that
the decoder actually takes square-root time or fails, and does not exclude
another recovery algorithm. The raw unconditional decoder-closure language,
depth extrapolation and asserted necessity of Weil/Tate pairings for arbitrary
real-valued chirps are withdrawn. Coprimality kills specified homomorphisms
and bilinear maps into the indicated finite groups, not all public observables.

For the narrow coordinate feature exp(2pi*i*t*x_tilde(P)/q), with integer
x_tilde in [0,p), geometric-series Fourier coefficients over Fp have L1
O(log p): bound coefficients by reciprocal distance to the nearest frequency
and sum the harmonic tail. Combining the separately scoped coordinate-phase
bound with this expansion screens that feature under alpha!=0 and q~p.
It is not a conclusion about every cross-modulus decoder or every bit function.

## Exact scalar Legendre symbol via a half-orbit product

For a smooth short Weierstrass curve in odd characteristic, let
h=(q−1)/2 and Q=kG!=O. Then the following identity is exact:

    product_(j=1..h) y(jQ)/y(jG) = chi_q(k).

The right side is the field element +1 or −1 representing the SCALAR-field
Legendre symbol; it is not a coordinate-field character applied to y(Q).
For proof, write kj=epsilon_j*r_j modulo q, with epsilon_j=±1 and r_j a
permutation of 1,...,h. Oddness of y cancels the permuted product, leaving
product epsilon_j. Multiplying the scalar congruences and applying Euler's
criterion identifies this sign with chi_q(k). No denominator vanishes because
nonzero odd-order points are not two-torsion. Dispatch Q=O separately.
Root and Sol independently checked this proof; no numerical test was needed.
The proposer's small hand check is retained only in the raw report.

An actual evaluator at cQ+dG gives chi_q(ck+d). For c!=0, multiplying by the
known chi_q(c) gives chi_q(k+d/c); zero is recognizable as the identity point.
This is a valid conditional shifted-Legendre oracle interface. Query points
and the entire evaluator must be paid. The elementary sequential half-product
has an O(q) strategy, not a runtime lower bound. The raw soft-O(sqrt(q))
evaluator was recalled from memory and is not accepted: square-root Velu and
general polynomial-product methods do not automatically preserve this ordered
half-system's ordinate signs. The division-polynomial expression requires

    2^(−h) * product_j Psi_(2j)(Q) / (product_j Psi_j(Q))^4,

not an unspecified single EDS factorial. No nodal degeneration provides an
algorithm on ordinary smooth curves.

## Paid recovery upper bounds, not an oracle impossibility claim

[BBUV, Table1 and Sections3.1–3.4](https://cosicdatabase.esat.kuleuven.be/backend/publications/files/journal/3130)
give optimized word-machine upper bounds T(M)=O(M²+q*log²(q)/M²),
space O(M²/log(q)), using M consecutive oracle answers. Root and Sol read
the table and source scope. Short-sequence candidate and clustering assumptions
remain; this is not an unconditional all-input recovery theorem.

[KKK, Sections2.1 and5](https://www.math.auckland.ac.nz/~sgal018/ANTS/papers/Kaluderovic-Kleinjung-Kostic.pdf)
give the improved schedule T(M)=O(M²/log(q)+q*log(q)*loglog(q)/M²),
with balanced upper envelope O(sqrt(q*loglog(q))). Sol read this author-hosted
ANTS PDF after the published MSP fetch returned empty HTML. Uniqueness and
search-distribution assumptions remain. H027-legendre-backend-scope.md records
the same qualified schedules and balancing; these are not lower bounds.

Add evaluator setup, M*E(q), query-point generation, scalar arithmetic,
filtering/failures, memory and exact final verification. The named backends
do not establish an exponent improvement even with a cheap evaluator, but
neither rules out better recovery or a material matched-cost gain. The raw
assertion that a free oracle is useless is rejected again.

The formal product-quotient shear in CardE uses the unknown scalar k. Its
existence gives no public construction or decoder. Neither degree-q isogeny
size nor a recalled upper-bound algorithm proves a runtime lower bound.
The polarization computation remains unverified. Higher-residue O(q) product
strategies likewise supply no universal exclusion.

## Research disposition

Retain the scoped recurrence identities/bounds and exact half-product signal.
No supplied observable has both a useful established signal and competitive
complete evaluation/recovery cost. The next decisive object is a public
evaluator or a genuinely different signal with a priced decoder; no spectrum
scan, generic Lean infrastructure or experiment is admitted from this report.
Root alone integrates. Validation command/results in STATE concern unchanged
Lean artifacts; they do not certify these paper arguments.
