# Mathematical checkpoints and abandoned dependencies

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

The final proof is the normalizer argument in `candidate.md`. The work
below records the finite-periodicity attempt and why its unpaid steps
were not inserted into that proof. These are technical observations,
not a second nomination.

## Actual finite orbit: what translation controls

Fix the relative category for X, let F=B_g, and suppose F^r P_f is
isomorphic to P_f. Put E_i=F^i P_f with indices taken modulo r at the
level of isomorphism classes. This includes the genuinely required
Artin action, rather than an arbitrary pair of transports.

For actual bigraded Hom, applying F^{-i} gives

    Hom^{n,v}(E_i,E_j) = Hom^{n,v}(P_f,E_{j-i})

as vector spaces up to chosen isomorphism. Thus the orbit endomorphism
dimensions are block-circulant, indexed by the difference j-i. Translating
both indices never changes this difference. For the sum Z of r orbit
members, counting with multiplicity,

    dim Hom^{n,v}(Z,Z)
       = r sum_{d mod r} dim Hom^{n,v}(P_f,E_d).

The same-transport calculation only supplies the d=0 term. Neither a
factor r nor averaging turns the other differences into zero. Moreover
F need not preserve minimal generator levels or the path-length Hom
filtration. One cannot identify linear-page h_1 by simultaneous
transport merely because actual Hom is invariant. These distinctions
prevent a cyclic cancellation claim at the null-layer step.

There is a genuine necessary constraint. The right simple U_f has
U_f B_g isomorphic to U_f as a right complex, by the exterior-simple
test in `cat:family`. For the unit label its value on each E_i is one
copy of the field in placements (0,0). The natural equivalence preserves
whether a map induces a nonzero map on this one-dimensional frame.

**Frame-map observation.** A bidegree-(0,0) morphism E_i -> E_j detected
nontrivially by U_f is an isomorphism.

To prove this, apply powers of F^{j-i} to the morphism and use the
finite orbit isomorphisms. After finitely many steps it is a composable
cycle returning to E_i, each map still detected nontrivially by U_f.
The composite has nonzero frame value, so is nonzero. Its bidegree is
(0,0), and End^{0,0}(E_i) is the field, because F^i preserves the
endomorphisms of P_f. Thus the composite is a nonzero scalar identity.
Cyclically starting at E_j gives the same conclusion there. The first
map therefore has both a left and a right inverse after rescaling the
remaining composite; it is an isomorphism. Alternatively its split
image is a nonzero summand of the indecomposable E_j.

Consequently, if E_j is distinct from P_f in an actual finite orbit,
there can be no frame-detected (0,0) map in either direction between
them. In a minimal E_j the unique f-generator is at (0,0). If its
outgoing linear arrows all vanish, the bare inclusion P_f -> E_j is a
chain map with frame coefficient one: there is no other f-generator
to receive a token differential. If its incoming linear arrows all
vanish, the bare projection E_j -> P_f is such a map. Thus a distinct
E_j must have both an incoming and an outgoing linear arrow at its
frame. This necessary condition does not force fixation. No equivariant
descent producing a forbidden frame map was established.

## Why a categorical finite symmetry is insufficient by itself

Here is a diagnostic outside the required Artin-word action; it is
explicitly **not** a counterexample to R. Take S={s,t}, m_st=3 and
X empty. The source adds f,o and all edges have label 3. Labels are
ordinary vector spaces. Normalize every two-arrow backtrack to its
vertex token. Every other positive-length product vanishes.

There is a graded algebra automorphism rho swapping s,t and fixing
f,o, arrows, units and tokens in the corresponding way. It induces an
order-two equivalence Rho fixing P_f and satisfying
Rho F_s Rho^{-1}=F_t.

Put P=P_f. The evaluation cones give

    E_s=F_s P=[P_s<1> -> P_f],
    E_t=F_t P=[P_t<1> -> P_f],

in cochain placements -1,0. Both are pure at level zero. Their linear
Hom has one length-zero basis map (f identity), three length-one maps
(s to t, s to f, f to t), and one length-two map (f token).
The first differential has rank one: the f identity maps to the s-to-f
map. The second also has rank one: the f-to-t arrow maps to the f
token. The s-to-t arrow is a cocycle because both compositions would
be nonbacktracking paths of length two. It is not a boundary. Hence

    h_1(E_s,E_t)=1,
    Hom^{*,*}(E_s,E_t)=k in bidegree (0,1).

The reverse pair gives the same result. The diagonal pairs have middle
cohomology zero by the same-transport source lemma. Thus the order-two
orbit {E_s,E_t} under Rho has aggregate h_1=2. All members have one
frame in the required placements.

Conjugating the symmetry gives T=F_s^{-1} Rho F_s, with T^2 isomorphic
to the identity. Its orbit contains P and E=F_s^{-1} F_t P. A direct
inverse-cone computation gives a minimal pure model for E:

    P_t<1> -> (P_s direct-sum P_f) -> P_s<-1>,
       -1              0                   1.

The first differential has nonzero t-to-s and t-to-f arrows; the
second has the f-to-s arrow. A sign on the first t-to-s component
depends on cone convention and can be removed by rescaling its isolated
target summand. Every displayed entry is radical, and d^2=0 because
t-to-f-to-s is not a backtrack. To obtain this cone, use
F_s^{-1} P_v=[P_v -> P_s<-1>] for v=t,f. In the map induced by the
t-to-f arrow, the s-to-s component is zero: it is the product of the
distinct-color path s-to-t-to-f. The remaining component is the original
t-to-f arrow. Taking the cone gives exactly the displayed model. This
justifies the transport, rather than asking finite Hom matrices to do so.

Applying F_s^{-1} to the actual Hom calculation gives
Hom(P,E)=k in bidegree (0,1); since E is pure at zero this is also its
middle linear Hom. The model has both an incoming and an outgoing
frame arrow, as predicted by the frame-map observation.

This finite symmetry is not an Artin word in the subgroup on s,t.
If T were B_a, its square would fix P in the X-empty category, and
`stab:single-detector` would give a^2=1. Stipulated torsion-freeness
would give a=1, contradicting E distinct from P. This uses only the
already-paid trivial-parabolic case. The example shows exactly that
finite symmetry, individual transported membership and one frame alone
do not imply aggregate middle vanishing; the specific Artin action
still matters. It does not describe a nontrivial actual finite Artin
orbit, and was not used to conclude anything negative about R.

## Independent reconstruction of the r11 rank-one calculation

For S={s}, X empty, again all labels in the extended three-vertex
algebra are 3. Let F=F_s and P=P_f. Evaluation gives
FP=[P_s<1> -> P_f] in cochain placements -1,0. Evaluating on P_s
cancels the unit component and leaves F P_s isomorphic to
P_s<2>[1]. Apply the invertible F to the defining triangle of FP.
Its source becomes P_s<3>[1]. The induced map to FP is nonzero:
the original projective arrow was nonzero in the homotopy category
and F preserves that fact. By placements, its only possible component
is a token into the P_s<1> term in placement -1. Normalize it by a
nonzero scalar. Its cone is

    F^2P=[P_s<3> --token--> P_s<1> --arrow--> P_f]
              -2                 -1                0.

The composite vanishes because its length is three, and the model is
minimal since every entry is radical. Its top layer at level one is
P_s<3> in cochain placement -2. Hom from Y^0(P)=P_f to that layer
has its one arrow class in bidegree (-2,4) and no length-zero or
length-two maps. This gives cross h_1=1. Within the F^2P-to-F^2P
layer pair the extra arrow-to-token differential has rank one,
consistently with source same-transport middle vanishing. On the sum
the middle dimension is two and outgoing rank one, so h_1 remains
one. This is not a periodic orbit. No archived finite checker was run.

## The successful change of route and error checks

The source screen then found DGM Lemma 2.7. Initially I considered only
its restriction where theta(n) lies in W_I, which would address just
a kernel of the Coxeter normalizer map. The full lemma applies to
theta(n) in N_W(W_I), so its zero-fiber argument covers **every**
normalizer coset. No Coxeter torsion case remains unaddressed.

The final proof checks inverse closure using injectivity of alpha_k;
product closure alone would not suffice. It checks that q^{-1}n
remains in the normalizer, and uses the left-Q product formula to
normalize its retraction. It uses normality of Q in N to form N/Q,
not normality of K. It never treats a general set retraction as a
homomorphism.

The retained Z^2 countermodel illustrates this distinction. A set
retraction onto 2Z times {0} is (a,b) -> (2 floor(a/2),0). Its zero
fiber contains (1,0), but not its double. Thus its zero fiber is not
a subgroup and cannot satisfy the product law used in the proof.
This does not reject the old countermodel; it identifies the extra
Artin-specific source operation excluding it.

All new proof steps after DGM's product law are explicit elementary
group operations in the candidate. No numerical test is needed to
extrapolate them. Their simplicity is also the contribution limit:
this round supplies a proposed full proof, not a substantial-result
nomination or an independent review.
