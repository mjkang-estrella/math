# H004 recent-result bridges: qualified disposition after independent review

Status: no supplied competitive algorithm; several proposer exclusions rejected.
Fable r2 delivered substantive independent ideation after r1 non-delivery. Raw
report is H004-recent-bridges-fable-raw.md; it is not accepted wholesale. Native
Astra /root/h002_arithmetic_ideas independently inspected primary sources and
returned the corrections below. No edits or numerical experiments by either
reviewer; root integrates. Existing square-root baseline and NONE improvement
remain unchanged. This record supplies reopening conditions, not universal
impossibility claims or a certification that the literature search was exhaustive.

## 1. Higher-dimensional isogeny interpolation

Robert's direct theorem invocation requires auxiliary torsion and the unknown
isogeny's images on it, with degree/factorization information. G,Q do not supply
those data. Retain that missing-input objection to this specified bridge.
Primary: https://www.math.u-bordeaux.fr/~damienrobert/pro/publications/articles/breaking_sidh.pdf
Theorem1.1 and Remark1.2, inspected by the independent reviewer.

Do not retain the stronger numerical/structural claims: degree q^(3/2) combined
with N_A^2>degree only requires N_A>q^(3/4), not automatically q. Auxiliary
extension degree depends on Frobenius; no uniform Theta(N_A) lower bound was
proved. Minimal coset degree was heuristic and curve-dependent. Known scalar
endomorphism actions do not exclude all coordinate-aware uses of the ring.
Reopen with an explicit paid construction of the missing images, including
extension arithmetic and preprocessing; no such construction was supplied.

## 2. Structured factor bases / chained polynomial systems

PKM leaves the point-decomposition cost T(E,m,L) unresolved. Its total-work
framework is a legitimate target for a future concrete solver, not a closed
route. The p^(1/m) auxiliary-curve trial example uses smoothness bound B=2;
it is not universal across smoothness choices.
Primary: https://christophe.petit.web.ulb.be/files/16PKC_primeECDLP.pdf

One explicit join matching hashing proves no universal join lower bound; a
Bezout bound is not a lower bound for finding one solution. Published losing
implementations do not rule out all dedicated solvers.

YYTK is not interval-only: the inspected conference version treats arbitrary
factor-base root polynomial F in <S_(m+1),F(x1),...,F(xm)> and includes subgroup
binomial experiments. Proposition8 uses an S-polynomial-count assumption;
another route needs a genericness assumption and cost conjecture. Those
conditional solver/representation results do not automatically apply to every
auxiliary-variable chain or point-decomposition algorithm. Primary inspected:
https://nutmic2019.imj-prg.fr/confpapers/SemaevECDLP.pdf
The final journal PDF was unavailable to the reviewer; no claim of inspecting it.
Reopen with an explicit solver whose relation yields, failures, setup and linear
algebra meet the PKM threshold. Fable supplied none.

## 3. Representation transfer

For explicitly enumerating both proposed labelled lists, |S1||S2|=qR implies
|S1|+|S2|>=2sqrt(qR); this named generation algorithm already loses. The bound
does not cover implicit lists, batching or another labelled-point generator.
Selecting coordinates directly loses known labels, but that fact does not
identify the resulting problem with a particular YYTK solver representation.
Primary: https://nutmic2019.imj-prg.fr/confpapers/SqRootECDLP.pdf
Delaplace–May supplies a conditional Zero-Join bridge over quadratic extensions
and a concrete slower-than-rho method, not a general prime-field lower bound.
Reopen with a specified representation and full-cost labelled-list construction.

## 4. Minors

Primary: https://arxiv.org/html/2310.04132v1
Distinct points and a nonzero coefficient of the unknown logarithm are needed
for the useful relation. Subset/minor correspondence alone does not establish
uniform independent success after conditioning, pivoting or adaptive selection.
The 414-row setting is amplified GESC, not the APM setting. Three deviations
already predominate around32–34 bits in Table4; the44-bit statement concerns
APM total kernels. Thus Fable's purported quantitative match is not supported.
Its multiplication of the reported algorithm complexity by a fresh determinant
cost also needs justification.

A predetermined original-subset family may permit an F/q expectation under an
explicit sampling model. It does not prove every induced minor-search procedure
must test candidates separately: row-ratio hashing batches zero2x2-minor searches.
The initial-minor conjecture needs an efficiently constructible uniform family.
If such a family is provided, scanning it locates a zero minor; the raw
'detection only' objection is wrong. No competitive solver is established, but
no exhaustive-search lower bound is accepted either. Reopen with constructive
minor selection and conditioned success plus total-cost analysis.

## 5. Coordinate-character ceiling

Primary: https://www.i2m.univ-amu.fr/perso/david.kohel/pub/character.pdf
Kohel–Shparlinski Theorem1 allows general polar support; later specializations
restrict it. Require a nontrivial additive character and geometric nondegeneracy.
A pole order prime to p ensures ramification that the unramified group-character
twist cannot cancel; nonconstant degree d<p is a sufficient setting. Poles must
be excluded or explicitly masked. Suitable complete normalized coefficients have
size O(d*sqrt(p)/q). This does not cover arbitrary bounded coordinate functions
or uncontrolled nonlinear postprocessing.

The raw sample/window inference is algebraically reversed: identifying both
variables as L, L>=const*epsilon^(-2) and epsilon<=const*d*sqrt(p)/L gives an
UPPER compatibility bound L<=const*d^2*p, not L>=p. Sample count and scalar-window
length should instead be distinct variables. Incomplete scalar intervals also
need completion/log factors; a coordinate-interval theorem is not a scalar-window
theorem. The scoped complete-domain obstruction remains useful for the specified
bias-estimation route. No new universal coordinate-method ceiling is accepted.

## Decision

No new experiment is justified by these reports alone. Classify the routes as
missing a supplied bridge, losing specified enumeration, or a conditional analytic
obstruction. Preserve the disputed claims and corrections, rather than converting
an unproved proposal into an equally unproved impossibility assertion. Root also
opened the minors, YYTK conference and Kohel–Shparlinski primary sources; no
primary material was executed or added to the repository. No Lean claim follows.
