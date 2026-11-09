# H013 — global count accepted; the full-cube model is closed

Date: 2026-10-08. Verified factoring complexity improvement: **NONE**.

The [independent review](H013-independent-review.md) accepts the complete
[proposer proof](H013-global-resultant.md), its coefficient-line count, exact
special family, and eta=2/5 model contradiction. The coordinator also checked
the proof and the reviewer's general-eta extension below. Frozen mathematical
input/report hashes match their manifests; the shared STATE changes are
intentional checkpoints, not changes to the reviewed argument. No finite
counting experiment or new solver is claimed.

For any monic integer degree-d polynomial f, the count for the specified
resultant threshold is at most

    d*(4d+3)*(2d²+3)*H²*(1+96H*N^(-6/(5d²))).

The argument partitions the cube into integer coefficient lines. Every line's
resultant polynomial has degree d and nonzero leading coefficient f(s)².
Its sublevel integers lie near one of d roots; integer points account for
the H² term even when those intervals are tiny. An interpolation bound finds
a suitable s<=d for signed f. Nonnegative base-m digits permit s=1. No random
root model or free enumeration primitive is used by this count.

At eta=2/5, this supplies tau>=min(a0,6/(5*delta²)). That necessary population
loss contradicts the stipulated full-scan/unchanged-smoothness inequality
when c<=1.93. This is a model contradiction, **not** a proved upper bound on
useful smooth survivors, which could have a different joint distribution.
The special irreducible f=gq+1 construction with Res(f,g)=1 and actual
height=M(g)=H confirms that cancellation cannot universally be replaced by
a small-actual-height condition. It supplies only one prescribed element
for special even inputs, not a useful population for arbitrary N.

## Checked extension: threshold tuning in the same model

For eta in [0,1] the same argument yields
tau>=min(a0,2(1-eta)/delta²). Write x=3a0 and

    F_eta = b + min(x/3,2(1-eta)/delta²)
              + [2(1+eta)/delta+x*delta/3]/(3b).

The proposed necessary condition is x>=F_eta. For fixed x,b,delta, F is
concave in eta, so it suffices to exclude both endpoints when x<=2.
At eta=1, AM-GM forces x³>=256/27>8. At eta=0, the branch where the
minimum is x/3 forces x³>=24>8. In the other branch, feasibility implies
delta<9b; increasing x to2 and minimizing the resulting b+A/b term gives

    2 >= 2/delta² + (2/3)*sqrt(2delta+6/delta).

For delta<=2 the right side exceeds2. For delta>=2, squaring nonnegative
sides requires P(delta)<=0, where

    P(delta)=2delta⁵-9delta⁴+6delta³+18delta²-9.

For v=delta-2>=0, expansion gives

    P=2v⁵+11v⁴+v*(14v²-2v+1)+15v+31 > 0.

The quadratic is positive by completing its square. Thus every eta in
[0,1] is excluded at c=max(x,2b)<=2 in this same relaxation. The coordinator
checked the concavity direction, both minimum branches, the monotonic step
in x, squaring conditions, and polynomial expansion. This is informal
reviewer mathematics checked by the coordinator, not a Lean theorem or a
new lower bound on factoring. The full original H013 proof was independently
reviewed; this extension originated with that reviewer.

## Next mechanism

Close the full coefficient-cube scan with this unchanged norm/smoothness model;
changing only eta does not provide a next experiment. H014 instead constructs
and costs the sublevel enumerator itself using exact univariate threshold
polynomials on coefficient lines. It remains live in tasks-H014.json. Its
output cost, useful survivor supply, norm-smoothness processing, algebraic
dependencies and factor-extraction success remain separate obligations.
