# A junction criterion and an actual fixed-system obstruction

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; code MIT.
Third-party inputs private, original rights. Full Q4 remains unresolved.

## The lattice condition is weaker than integral switch coefficients

Consider any one of R12's fixed two-segment systems. Suppose its combined
ordered roots B=(beta_1,...,beta_k,delta_1,...,delta_l) are an independent
basis of R^n. Let M be their matrix and w the global endpoint difference,
so M m=w in Q(D_n). Let F be the subset of columns belonging to the
first segment. Its junction satisfies

    z-(a+b) = (u_k b-b) - M_F m_F.

The first term is in Q. Thus only M_F m_F, rather than every m_i,
has to lie in Q.

Here is an exact criterion in this situation. The signed graph of B
is a disjoint union of unbalanced unicyclic components. Call a
component odd if the coordinate sum of w on it is odd. Then

    z in a+b+Q

if and only if (i) F contains either all or none of the cycle edges
of EACH odd component, and (ii) the number of odd-component cycles
wholly contained in F is even. Off-cycle edges and all edges of even
components impose no further condition.

Proof. Independence and full coordinate rank force each connected
component to be unbalanced with exactly as many edges as vertices.
Pruning its trees solves their coefficients integrally. The cycle
equations have determinant of absolute value two. On an even component
all coefficients are integral; on an odd component precisely its cycle
coefficients are half-odd-integral. This is also the signed-graph lattice
calculation in the source's lem:hard-case, which is credited.

Modulo integer vectors, twice the sum over a selected subset of odd
cycle edges is the ordinary incidence boundary of that subset, over F2.
Signs disappear modulo two. A simple cycle, including a two-edge signed
cycle, has zero boundary only for its empty and full edge subsets.
Different components have disjoint coordinate supports. Hence the first
segment displacement is integral exactly under (i). If an odd cycle is
fully selected, its integral displacement has odd coordinate sum:
the full component's displacement is w on that component, and the
remaining tree contributions are integral roots of even sum. Every
integral root-coefficient contribution has even sum. Therefore the
integral first-segment displacement has even sum exactly under (ii).
This proves the criterion. The number of odd components overall is
even since w is in Q. In particular, two odd cycles BOTH lying in the
same segment already give a good junction despite fractional switches.

This criterion makes no claim that every feasible pair can be replaced
by a combined root basis. R12 gives separate bases with up to 2n roots.
A global basis/minimality reduction would itself need a proof.

## A genuine Spin(8) tuple where the fixed polytope cannot be rounded

In D4 put

    a=(10,7,4,1),   b=c=(2,0,0,0),   d=(11,7,5,1).

These are dominant integral weights. Their sum is (25,14,9,2), whose
coordinate sum is 50, so the full external root congruence holds.
All D4 representations are self-dual. The construction uses the exact
straight-shape system and sign conventions of R12.

For the first segment start with velocity -2e1 and use the ordered
roots beta1=e1-e2 and beta2=e1+e2. The velocities after the successive
reflections are -2e2 and 2e1. Both totals C_i are 2. Set x1=x2=1/2,
so both switches are at time 1/4. Since the roots are orthogonal,
the gaps are

    (a1-a2)-1/2=5/2,   (a1+a2)-1/2=33/2.

The endpoint is z=a+2e1-(beta1+beta2)/2=a+e1=(11,7,4,1).
This z is dominant, but z-(a+b)=-e1 is outside Q(D4).

For the second segment start with velocity -2e3 and use
delta1=e3-e4 and delta2=e3+e4. Their totals are 2, and y1=y2=1/2
again puts both switches at time 1/4. The gaps at z are 5/2 and 9/2.
Its endpoint is z+2e3-(delta1+delta2)/2=z+e3=d.
All initial velocities are Weyl translates of b or c; even sign
changes on zero coordinates allow the displayed negative directions.
Times are weakly ordered, totals positive, and gaps strictly positive.
Thus these are actual schedules, not arbitrary normal cones.

For these fixed root lists and frames, endpoint balance forces

    x1 beta1+x2 beta2+y1 delta1+y2 delta2=e1+e3.

The four roots are independent. The coordinate equations give uniquely
x1=x2=y1=y2=1/2. The entire fixed feasibility polytope is a singleton
in coefficient space, and its ONLY junction is the bad z above. No
deformation in that fixed polytope can achieve the required coset,
even if switch integrality is not demanded. The two unbalanced
components have odd endpoint differences e1 and e3; exactly one full
odd cycle lies in the first segment, in agreement with the criterion.

It even comes from an actual selected scaled representation diagonal.
At N=2 these two rational moment couplings have integral labels and
differences 2(a+b-z)=2e1 and 2(z+c-d)=2e3 in Q. Rational occurrence
and the stipulated triple theorem give both scale-two occurrences.
Hence eta=2z is an actual diagonal in the doubled fourfold invariant.
Dividing it gives an integral weight z, but the wrong unscaled coset.
The general warning is already present in the credited source tail;
this is an explicit two-segment instance, not a new saturation failure.

## The same tuple has an unscaled invariant

This is NOT a Q4 counterexample. There is a different pair of schedules
with good junction t=a. Keep the first initial velocity and roots,
but set x1=x2=1, at time 1/2. Its gaps are 2 and 16 and endpoint a.
For the second segment start with velocity 2e3, use the single root
e1-e3 with total 2 and coefficient 1 at time 1/2. Its gap is
(a1-a3)-1=5, final velocity 2e1, and endpoint

    a+2e1-(e1-e3)=a+e1+e3=d.

Both couplings have rational moments by the actual stipulated
lem:schedule-moment. Their integral labels have root congruence:
a+b-a=b in Q and a+c-d=e1-e3 in Q. The moment/occurrence interface and
stipulated triple saturation therefore give

    V(a) in V(a) tensor V(b),
    V(d) in V(a) tensor V(c).

Self-duality and contraction yield the fourfold invariant. This is an
actual representation-theoretic certification relative to the allowed
sources, not an extrapolation from a finite checker. The alternative
uses three switches, so the four-switch bad system is NOT asserted
to be a globally minimal schedule. Nor are these diagnostic weights
required to be spinorial to reject a proposed universal fixed-system
rounding lemma. They fall within Q4, whose full spinorial scope is unchanged.

The new finite checker verifies precisely these two schedule pairs,
the root lattice arithmetic, and uniqueness for the bad fixed system.
It does not compute tensor decompositions or implement the stipulated
moment/occurrence theorem. No universal conclusion follows from it.
