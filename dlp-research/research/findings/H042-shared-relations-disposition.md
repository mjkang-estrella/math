# H042 shared relations: valid orbit invariant, missing solver

2026-10-09 UTC. Raw report: H042-shared-relations-opus-raw.md. Native Astra
independently reviewed the mathematics; native Sol reviewed reuse and costs.
Root checked the elementary accounting and primary sources. No improved
algorithm, new experiment, Lean claim or H034 cap reset.

## Known-ratio orbit variant

In an order-q subgroup, take gcd(ell,q)=1 and seed points S0 with unknown
logarithms z_P. Define S_i=[ell^(-i)]S0. The exact public relation is

    log_G([ell^(-i)]P) = ell^(-i) z_P mod q.

These are known ratios of unknown logs, not a precomputed inverse table.
Relations extracted over the expanded set can substitute these coefficients
into columns for the seeds and be checked by group arithmetic. The construction
is valid, but the report has not supplied a faster decomposition/extraction
method or a justified useful-relation/rank law for it.

For t layers, the union size B is at most t B0, where B0=|S0|. Overlaps,
negation and already shared representatives must be accounted for. Equality
and the proposed t-fold reduction in unknowns do not follow automatically.
Counting coefficient patterns does not prove a matching increase in distinct
decompositions. Enumerating all t^m patterns is one implementation, not an
unavoidable cost.

When ell is prime to the characteristic, the x-map of multiplication by ell^i
has degree ell^(2i). This is not a runtime lower bound for a solver or for a
compact composition. Multiplication is bijective on the order-q subgroup. Under
the FULL rational prime-order group hypothesis, each rational point has one
rational point preimage. For a valid finite x-map equation with a nonzero
odd-order rational target, a rational x preimage cannot lift only to points
with Frobenius(P)=-P: multiplication would make the target simultaneously
rational and anti-rational, forcing two-torsion. Cleared denominators, infinity
and invalid roots still require dispatch. Inseparable cases need different
degree/root counting.

Therefore comparing this degree with tiny Gröbner degree-of-regularity tables
is not a decisive falsifier. If t is fixed or polylogarithmic, the nominal
t and t² savings alone do not change exponents; no such restriction on t proves
a general exponent exclusion. Actual construction and solving costs control it.

## Correct full-work conditions

Keep the H041 gate: at fixed m and B=p^(1/m+o(1)), ordinary collection has
conditional exponent 1/m+d+s for replay cost p^(d+o(1)) and justified useful
relation overhead p^(s+o(1)). With B² linear algebra, the latter dominates
when d+s<1/m, ties at equality and is dominated when d+s>1/m. Thus the raw
claim that linear algebra is never the bottleneck for m>=5 is false.

For an orbit variant a candidate must instead justify an invoice of the form

    A_orbit + R_orbit D_orbit / sigma_orbit
      + L_orbit + witness/recovery/verification,

where R_orbit is a sufficient useful relation count, not merely the number of
seed symbols. Rank deficiency, dependent rows, failed traces and invalid
witnesses remain charged. If disjointness and rank justified R_orbit about B0,
the possible collection saving must be compared to the changed D_orbit and
sigma_orbit; it is not confined in advance to linear algebra. No such bounds
are established here.

More explicitly, if U=p^u independent columns suffice, conditional expected
replay costs p^d, justified rank overhead is p^s, and linear algebra costs
U^eta, the conditional exponent is max(a,u+d+s,eta*u,v_final), retaining
any additional expanded-base construction exponent. The named solver must
price detection of bad pivots, fallback/relearning and valid witness extraction.
These quantities are not instantiated by degree/root counts alone.

A shared trace may have a once-paid setup A and a genuinely smaller replay D.
It could change an exponent if justified; target dependence alone does not
limit its benefit to constants/polylogarithms. Conversely, shared equation
syntax does not prove a common pivot schedule or cheap valid witness extraction.
There is no accepted rank theorem for these rows from an analogy with random
sparse matrices over a different field.

The explicit-materialization screen is narrower. Suppose a method writes one
record for each of sigma p decomposable values, requires B useful relations,
samples independent uniform targets, and gains at most one useful relation
per successful target. Then its paid invoice includes terms proportional to
sigma p+B/sigma, whose unit-cost minimum is2 sqrt(Bp). This applies to that
materialized search, not an arbitrary compact representation, batched algorithm,
multi-output sampler or compressed polynomial. A set's size is not a lower
bound on every program representing it.

## Rational-Hom scope

Different full F_p-point counts imply Hom_Fp(E',E)=0, since a nonzero rational
homomorphism would be an F_p-isogeny. This does not imply the geometric Hom
group vanishes; twists can be geometrically isomorphic. PKM uses a smooth
subgroup, not necessarily a wholly smooth auxiliary order. If the target's
full order is prime q and the auxiliary group contains a subgroup of size
1<B<q, its order differs from q, so the rational obstruction applies. For a
target having only an order-q subgroup the premise needs separate verification.

Regular correspondences induce homomorphisms on Jacobians; an associated point
map may include a constant translation. Arbitrarily selected branches or coset
sums need not be such maps. No general structured-factor-base or selector
exclusion follows from this Hom argument.

## Sources and decision

Root reopened [PKM2016 sections4–5](https://people.maths.ox.ac.uk/petit/files/16PKC_primeECDLP.pdf):
the reported decompositions use two factor-base points; the final comparison
with plain Semaev equations is preliminary. Those measurements are not a
cost bound for m>=5 or for the orbit variant.

Root read the [Joux–Vitse abstract](https://eprint.iacr.org/2010/158), which
describes F4 work reuse across similarly shaped systems. The PDF browser open
returned403; `curl --fail --location --max-time 20 --silent
https://eprint.iacr.org/2010/158.pdf | pdftotext -layout - - | rg -n -A 18 -B 8
'trace|same shape|probab|unlucky|specializ|generic'` produced an empty-document
parse error, exit1. No full-paper claim or asymptotic replay bound is accepted.
Other abstract/search-only attributions in the raw report remain unverified.

Retain known-ratio orbit expansion as an unvalidated variant, not a discovery
or a rejected entire class. The next useful step requires a concrete system
representation and decomposition/replay schedule predicting a paid gain;
degree comparison alone does not justify an experiment. Best supported
exponent remains1/2; verified complete-work improvement NONE.

Both native final draft checks accepted these scopes. Root launched a NEW
Claude Opus5.5 construction round, with the original brief, report and all
objections above. It must supply an actual orbit membership/system representation
and decomposition/replay schedule predicting complete work; merely repeating
ratio reduction or degree inflation is not sufficient. Read-only, no experiment.
Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h042-orbit-construction-opus-20261009-r2`.
Launch accepted the exact provider/model and returned running.
