# An exact feasibility-preserving junction deformation

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; code MIT.
This is one actual two-segment construction, not a universal Q4 proof.

The bad fixed system in checkpoint-junction-lattice.md can be repaired
by CHANGING its combinatorial data. The following family does this
without treating the free reset as a break of a single shape.

Keep a=(10,7,4,1), b=c=2e1 and d=a+e1+e3. Set

    beta-=e1-e2, beta+=e1+e2,
    epsilon=e2-e3,
    delta-=e3-e4, delta+=e3+e4.

For 0<=s<=1, use the following exact schedules.

First segment: initial velocity -2e1, ordered roots beta+,beta-,
and coefficients

    x+=(1-s)/2,    x-=(1+s)/2.

The intermediate velocity is 2e2 and the final velocity is 2e1;
both totals are 2. The switch times are (1-s)/4 and (1+s)/4.
The gap formulas are 33/2+s/2 and 5/2-s/2, respectively.
They remain positive throughout the interval. Its junction is

    z(s)=a+2e1-x+ beta+-x- beta-=a+e1+s e2.                  (1)

Second segment: initial velocity -2e2, ordered roots
epsilon,delta-,delta+, and coefficients

    h=s,    y-=y+=(1+s)/2.

Successive velocities are -2e3,-2e4,2e3, so all three totals are 2.
The times are s/2,(1+s)/4,(1+s)/4. They are weakly ordered precisely
because s<=1, and all lie in [0,1]. The gaps, including the change
of the INITIAL position z(s), are

    epsilon:  (z2(s)-z3(s))-h = 3,
    delta-:   (z3(s)-z4(s))+h-y- = 5/2+s/2,
    delta+:   (z3(s)+z4(s))+h-y+ = 9/2+s/2.

The term +h comes from epsilon.delta-=epsilon.delta+=-1.
The two delta roots are orthogonal. These equations establish the
sign inequalities for EVERY real s in the interval, not just sampled
parameters. The final endpoint is identically

    z(s)+2e3-h epsilon-y- delta--y+ delta+
      =a+e1+e3=d.                                         (2)

At s=0 the first two roots are simply the commuting reorder of the
original simultaneous switches. The new second-segment epsilon switch
has coefficient and time zero; after it the velocity is the original
-2e3. Absorbing this boundary switch recovers exactly the old schedule.
Thus the family starts at the actual bad fixed-system realization.

At s=1, x+=0 and all other coefficients are 1. The junction is

    z(1)=a+e1+e2=(11,8,4,1),
    z(1)-(a+b)=-e1+e2 in Q(D4).

The second segment's three switches are simultaneous at time 1/2 in
the displayed order. The first segment's zero-time switch is removable.
Weakly ordered coincident switches are allowed by the exact interface.
Hence both couplings remain feasible and the junction reaches the
required root coset. Dominance of z(s) also holds for the whole family:
11 >= 7+s >= 4 >= |1|.

The lattice mechanism is the primitive relation

    -beta+ + beta- + 2 epsilon + delta- + delta+ = 0.

Half of this relation is the coefficient derivative. It preserves the
global endpoint, but moves the first-segment displacement by -e2;
therefore it really moves the junction by +e2. The added bridge joins
the two odd unbalanced components and generates the full D4 root
lattice. A root relation alone would not prove feasibility. The times
and gaps above pay it explicitly in this example.

## Arithmetic that survives a reset, and what does not follow

For general fixed two-segment data, concatenate its position-root lists
as r1,...,rK and its coefficients as m. The gap vector has the form

    G_i = A_i - sum_{h<i} m_h (r_h.r_i) - m_i,

where A_i=r_i.a in the first segment, while in the second segment
A_i=r_i.(a+u_k b). The linear coefficient-to-gap matrix T is therefore
exactly the same lower triangular integral unimodular matrix as in the
one-shape source. The reset changes its constants, not its linear part.

In particular, if K=n+1 roots generate Q and their coefficient fiber
has one-dimensional kernel, the primitive half-relation still has
|d_i|<=1 and |(Td)_i|<=1. Indeed the artificial cumulative velocity roots
gamma_i=(s_{r_{i-1}}...s_{r1})^{-1}r_i are roots, generate the same
lattice by triangular integral transformations, and satisfy

    Gamma T = p_K^{-1} M,

as follows by telescoping reflections. Thus Td is the corresponding
primitive half-relation in that root list. Maximal minors are 0,2,4:
delete one edge of the connected unbalanced signed graph, and every
full-rank remaining component is unbalanced unicyclic. Their gcd is 2.
Cofactors give primitive entries at most 2 in magnitude, in both lists.
This is the source half-kernel arithmetic, valid here by the displayed
identity; its nonroutine signed-graph input is credited to the source.

If each segment's roots are independent, a potential can also be
chosen SEPARATELY for each segment: solve L_j.gamma_i=d_i for its
local velocity roots. Surjectivity follows from their independence.
Its candidate-time equation is

    gamma_i.(v_j (t-tau)+s L_j)=0

for a straight segment with initial velocity v_j at a tied time tau.
This gives separate local sorting data. It does not produce a single
moving weight, compare directions across the reset, supply a local
link in every case, or establish the full no-boundary continuation
argument. Nor is independence in both segments guaranteed in a general
augmented system without another argument.

The construction above proves that the junction can be repaired in
one genuine coupled problem and identifies the moving-junction terms
that must be kept. It does not show that every possible obstruction
has an admissible bridge or another feasible route. That universal
existence assertion remains exactly the unpaid Q4 operation.
