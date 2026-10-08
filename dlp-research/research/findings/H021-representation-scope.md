# H021 representation and trace screens: corrected scope

2026-10-08. Factory initial report and independent native Sol translation
review /root/h010_early_dependencies COMPLETED; Claude trace/ray-class review
COMPLETED, terminal result read/no pending children. Root checks below.
Raw Claude report retained in H021-trace-rayclass-opus-raw.md, not endorsed.
Exact tasks in H021-public-signal-reviews.md. No numerical run or Lean change;
paper claims only. Improvement NONE.

## Exact projective orbit dimension

Let q be prime, q!=p, k=F_(p^r), and z_i=A^i z_0 a nonconstant q-periodic
orbit in projective k-space, with A invertible. Let n be the dimension over k
of the vector span of its lines. Then

    n >= max(2, ord_q(p^r)).

Lift A to B and z_0 to v_0. B^q v_0=c v_0 with c!=0; commuting powers
give B^q=cI on the orbit span. If ord_q(p^r)>1, raising to q is bijective
on k*, so rescale B to M with M^q=I. Since q!=p, its minimal polynomial
divides the separable polynomial X^q-1. A nonconstant projective orbit forces
a nontrivial q-th-root eigenvalue. Its Frobenius orbit has length ord_q(p^r),
so its irreducible polynomial requires that many dimensions. When the order
is1, nonconstancy alone gives n>=2. If k'=ord_q(p), then

    rn >= r*k'/gcd(k',r) >= k'.

This is an exact finite-orbit linear algebra statement. It requires no map
defined geometrically on the whole curve, but does require an exact linear
projective action and a nonconstant orbit. It gives no universal evaluation,
storage or full-solver bound for compressed coordinates or operations.

## Separate geometric statement

If a nonconstant morphism phi:E->P^(n-1) intertwines translation by G and A
as morphisms, use L'=phi*O(1). Equivariance gives translation invariance of
L'. The divisor-class sum rule gives q divides deg L'. Remove any fixed
base divisor from the proposed linear system before identifying that degree.
Finite rational-orbit equality alone does not imply geometric equivariance.
The independent reviewer inspected [Stacks projective-space construction](https://stacks.math.columbia.edu/tag/01ND)
and [Milne, I.4, Remark4.11(c)](https://www.jmilne.org/math/Books/EC2.pdf).

Nonconstant as a morphism does not mean nonconstant on the rational orbit:
x composed with pi-1 has compact evaluation and collapses rational points.
Degree divisible by q does not mean coordinate dimension at least q.
For full prime group order q>3, Hasse implies q does not divide p-1:
otherwise p>=2q+1 whereas p<=(sqrt(q)+1)^2, forcing q<=4. This is not a
claim for arbitrary prime subgroups, and q=p is separately excluded.

Abstract complex characters do not supply efficient evaluation, eigenbasis
construction, calibration, precision or decoding. No general quadratic
Vandermonde zero-search bound is proved. The arbitrary convolution exclusion
is false (delta at O returns the other function). Nonlinear, approximate and
compressed candidates remain open. No broad formalization is warranted.

## Trace card: retain identities, reject unsupported cost conclusions

For odd rational group order q, Tr(R)=R+pi(R) on E(F_(p²)) is surjective
because its restriction to rational points is doubling. Each R uniquely
splits into its rational component [2^-1 mod q]Tr(R) and a trace-zero
component. Call it the rational component, not unconditionally the entire
q-primary component: the twist order can require separate coprimality checks.
If rational R0=R1+R2, then 2R0=Tr(R1)+Tr(R2). Conversely the trace equation
only places the ambient sum in a trace fiber; it does not fix that sum.

Thus the raw proposal mixes an ambient relation in a group of size roughly
p² with a trace relation in a group of size roughly p. Expected pair counts
alone do not construct a fast restricted-base relation finder. For a fixed
m-element trace-image table, a literal scan of m complements costs m lookups;
under an additional uniform-pair model the expected hit count is m²/q.
Its heuristic q-scale relation-collection ledger still requires useful rank,
image cardinality, paid base generation and success assumptions.

Neither the original p/m+m² nor the reviewer's p^(4/3) and p-scale totals
are accepted as exact general runtime bounds. The full ambient solver needs
nondegeneracy, root-lifting and success analysis; restricting parameters does
not preserve a free solver. A constant-degree algebraic trace parametrization
needs an explicit chart and exceptional cases before invoking it. No universal
poly(m) lower bound follows from a degree-m restriction polynomial.
The reviewer itself acknowledges unproved image size/equidistribution/rank;
its subsequent claim that the counting is an exact proof is too strong.
Current rejection is of the supplied gain rationale, not all trace algorithms.

## Ray-class lead: target conversion still missing

For paid O=End(E) and m=(pi-1) of prime norm q!=p, the rational generator
can serve as marked level data, subject to the action's orientation and
isomorphism hypotheses. The primary source [Arpin et al., Sections3.5/4](https://arxiv.org/html/2407.14450v1)
describes cyclic level structures and a vectorization reduction retaining a
discrete logarithm when restoring level data. Root read those sections.

A returned principal generator alpha, its residue and the compatible marked
isomorphism/unit ambiguity would recover a scalar for direct verification.
An ideal representative alone is not automatically that generator/residue:
principalization and representation costs cannot be declared irrelevant.
Writing alpha=k merely hides the answer. No cheap conversion of public Q to
an arithmetic target or direct marked-action solver was supplied.

Reject the raw review's stronger claims: equivariance alone does not show
that only a DLP comparison distinguishes points; every useful method need not
pass through the other eigenspace; and modular-unit degree does not prove a
q-scale evaluation lower bound. Unchecked conductor/splitting or remembered
principalization complexities are not adopted. No universal polynomial-time
equivalence from arbitrary ideal output has been established here.

Reopening requires an explicit paid target conversion, direct marked-action
solver, or restricted trace decomposition algorithm with useful complete costs.
The ordinary square-root reference and dashboard remain unchanged.
