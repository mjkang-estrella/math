# Four-factor type-D saturation: frozen target unresolved

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party inputs remain
private and retain their rights.

**UNRESOLVED_FULL_Q4.** No proof or genuine counterexample to the frozen
four-factor theorem was obtained. No substantial result is nominated,
no independent mathematical/contribution PASS is claimed, and no count
change, manuscript or Lean package is requested. The campaign remains 4/10.

This round develops one target from family 204, distinct from the retained
Artin, relative-CI, elementary-unimodality, Hamiltonian, analytic and crossing
lanes. The project's I104 S104 passage had already SCREENED all tensor
arities without selecting or developing it; I226 explicitly preserves that
unpaid compatibility issue. Thus this is not an invented new conjecture or
a claim that the common-diagonal obstruction was first noticed here. The
new work of this attempt is the faithful two-segment feasibility system
and the four-orbit profile diagnostics below. They are technical progress,
not a solution or substantial nomination. A bounded screen did not settle
whether a stronger existing polygon theorem already pays full Q4; no global
priority or present-open-status certificate is claimed.

## Exact unchanged target

For every n>=2, let G=Spin(2n,C), with D2=A1 x A1. For all four dominant
integral weights a,b,c,d, including arbitrary spin weights, assume
 a+b+c+d belongs to Q(Dn).
For EVERY positive integer N, Q4 asks

 (V(Na) tensor V(Nb) tensor V(Nc) tensor V(Nd))^G != 0
   iff (V(a) tensor V(b) tensor V(c) tensor V(d))^G != 0.

All ranks, zero/singular weights, chamber boundaries and dilation factors
are retained. No ordinary-weight, stable-range, generic, fixed-diagonal,
or factor-two/four restriction replaces this scope. The frozen original
scope has SHA256 adfa4c4898f9cc592089cf48d4a7ac15c448c15f494a39ccc2b11b0da3159e99.

The stipulated input is openai/math revision
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, *Tensor saturation for even spin
groups*, thm:main: the corresponding THREE-factor theorem. Its lower
schedule interfaces are read with their actual hypotheses, and its truth
is accepted as instructed. Neither its title nor its column list is an
arbitrary-factor theorem.

## The paid direction, with no factor-count restriction

If the unscaled fourfold tensor product has an invariant, choose a nonzero
invariant functional f on it (complete reducibility identifies nonzero
invariants and invariant functionals). The compact translates of a highest
vector span each irreducible module. Their pure fourfold tensors therefore
span the whole tensor product, so f is nonzero at some four flag vectors
v_a,v_b,v_c,v_d. The N-fold tensor power of f is an invariant functional
on the N-fold powers of each factor, after the canonical regrouping.
Its evaluation on v_a^N tensor v_b^N tensor v_c^N tensor v_d^N is f(v)^N,
which is nonzero. Each power of a flag vector belongs to the Cartan
summand V(Na), respectively V(Nb), V(Nc), V(Nd). Restricting the functional
to their tensor product proves the dilated invariant. Zero weights cause
no exception. This is the standard Cartan-power operation; the source
already uses it for triples, and its four-factor version is not a new
substantial contribution. Only the reverse implication is unpaid.

# Q4 checkpoint: the actual common-diagonal problem

For G=Spin(2n), write c(a,b;t)=dim Hom_G(V(t),V(a) tensor V(b)).
Complete reducibility and Schur's lemma give exactly

 dim(V(a) tensor V(b) tensor V(c) tensor V(d))^G
   = sum_t c(a,b;t)c(c,d;t*).

At scale N a nonzero summand supplies eta. The rational weight eta/N
need not be a weight, and even if it is a weight it need not be in
L=a+b+Q. Total external root congruence makes the two required central
cosets compatible: if t in L then c+d+t in Q. This does not supply t.

Let P(a,b) be the real dominant moment polytope of sums of compact
orbits a,b. Berenstein--Sjamaar 3.2.1--3.2.2 identify its rational
points with occurrence after some common dilation. Thus, using the
stipulated triple saturation, Q4 is exactly the following lattice
intersection assertion on the ORIGINAL inputs having scaled occurrence:

 [P(a,b) intersect (P(c,d))*] intersect (a+b+Q) != empty.

Here is the full reverse bridge, without assuming a lattice point.
Suppose a point t in that intersection ALSO belongs to a+b+Q. It is then
a dominant weight. Every simple reflection changes a weight by an integral
multiple of a root, so W acts trivially on P/Q, and t*=-w0(t) is congruent
to -t. Thus a+b-t and c+d-t* both belong to Q, the latter because the
external total belongs to Q. Berenstein--Sjamaar gives occurrence of V(Mt)
in V(Ma) tensor V(Mb) for some M, and occurrence of V(Lt*) in V(Lc)
tensor V(Ld) for some L. The stipulated triple theorem applies separately
WITH THESE INTEGRAL LABELS and congruences, giving c(a,b;t)>0 and
c(c,d;t*)>0 at scale one. Their product is a positive summand in the
four-invariant formula. Conversely, an unscaled four-invariant supplies
such an integral t by its own decomposition and the necessary central
character congruence. A dilated four-invariant supplies only eta/N in
the real intersection. This proves the claimed exact remaining operation,
without assuming that eta divides or has the unscaled congruence.

The forward Cartan-power implication is classical and works for any
number of tensor factors. Its proof is given above.

A generic normality argument does not prove this: the cones
 C1={(A,z): A>=0, 0<=2z<=A},
 C2={(B,z): B>=0, B<=2z<=2B}
have dilation-saturated lattice semigroups of all their integer points.
At A=B=1 their fibers are [0,1/2] and [1/2,1], each containing an integer,
but their intersection {1/2} does not. At A=B=2 their common fiber has
z=1. This refutes the indicated normality/projection inference only;
these cones are NOT asserted to be tensor cones or an associative fusion
semiring. It does not refute Q4.

An actual Spin(8) shortcut diagnostic uses a=b=omega1=e1 and
c=d=omega4=(e1+e2+e3+e4)/2. All four modules are self-dual (-1 is in W(D4)),
so pair contractions supply an invariant. Total sum is (3,1,1,1), in Q(D4).
Replacing V(a) tensor V(b) by its Cartan summand V(2e1) destroys it:
every weight of S+ tensor S+ has first coordinate at most 1, whereas
2e1 has first coordinate 2. Thus Hom(V(2e1),S+ tensor S+)=0.
The S+ weight description is the standard half-spin model, not a new
representation theorem. A common unrestricted diagonal does exist (0).
This is a counterexample to that Cartan replacement, not to Q4.

The source's own tail:fractional remark already gives the separate
warning against dividing an arbitrary diagonal: V(2e1) has a cubic
invariant, but V(e1) does not. In the four-vector problem at N=2, eta=2e1
can therefore be a selected diagonal; eta/N=e1 is outside 2e1+Q. Other
diagonals work at scale one. This warning is credited to the source,
not nominated as a new result.


# Q4 checkpoint: two schedules with a free junction

Put (a,b,c,d)=(lambda1,...,lambda4). The first schedule starts at a,
moves along the straight shape tb, and ends at a Weyl representative z
of the intermediate weight. Rotate the second schedule so it starts at
that SAME z; it moves along tc and ends in W(d*). The source basic-schedule
and schedule-moment interfaces permit at most n switches in each segment.
No assertion that their concatenation is a single source schedule is made.

Fix root lists beta_1,...,beta_k and delta_1,...,delta_l (k,l<=n),
initial direction frames u,v, and final endpoint frame r. Define
 u_i=s_beta_i ... s_beta_1 u, v_j=s_delta_j ... s_delta_1 v,
 C_i=-beta_i . u_(i-1)b, D_j=-delta_j . v_(j-1)c.
Delete zero-total switches. Thus C_i,D_j are POSITIVE integers.
Let x_i and y_j be switch coefficients. For straight shapes, times are
x_i/C_i and y_j/D_j. The exact feasibility equations/inequalities are

 0 <= x_1/C_1 <= ... <= x_k/C_k <= 1,
 0 <= y_1/D_1 <= ... <= y_l/D_l <= 1,
 z=a+u_k b-sum_i x_i beta_i,
 z+v_l c-sum_j y_j delta_j = r d*,
 beta_i.a - sum_(h<i) x_h beta_h.beta_i - x_i >= 0,
 delta_j.z - sum_(h<j) y_h delta_h.delta_j - y_j >= 0.

For an empty root list its time inequalities are omitted and its final
frame is its initial frame. All coefficients are rational (indeed integral
after clearing the positive C,D denominators). The listed x,y ranges are
bounded. Hence each fixed combinatorial choice gives a rational polytope.
There are finitely many root lists, frames and lengths for each n.

Proof of faithfulness: set each time to its displayed ratio and successively
integrate the constant Weyl-translated velocities. Induction through the
reflection identities gives y(t)=initial+w(t)shape(t)-sum(previous m roots).
Its beta_i gap is exactly the displayed expression, because
beta_i.u_(i-1)shape(time)=-x_i. The endpoint and weak time order therefore
give precisely source schedules. Conversely any such two schedules obey
these same equations. Coincident times retain their indicated order. A
Weyl rotation making z dominant turns the second one into the ordinary
source interface with a dominant initial label and end orbit W(d*).

Summing the endpoints removes the unknown junction:
 sum_i x_i beta_i+sum_j y_j delta_j = a+u_k b+v_l c-r d* in Q.
The last membership follows from total external root congruence and
Weyl action being trivial on P/Q. This pays an integral right-hand side,
NOT integral solvability with the inequalities. Integer x,y would give
z in a+b+Q, and would suffice via rational moment/occurrence and the
stipulated triple theorem. Requiring all x,y integral is stronger than
necessary: only z in that coset is the exact target.

The source one-segment continuation cannot be applied unchanged. It uses
one common shape, a fixed total moving weight and its one Bruhat order.
At this free junction the direction can RESET. Treating it as an ordinary
shape break would imply moment feasibility for (a,b+c,d*), which is false
for the actual Cartan-replacement example in the common-diagonal section above.
Global root balancing does not pay the missing two-segment continuation.


# Q4 checkpoint: the three-orbit profile estimate does not copy unchanged

This is a proved diagnostic of a proposed source-proof extension. It is
NOT a counterexample to Q4 or to an exceptional odd-parity schedule.

For k real skew-symmetric matrices on R^r summing to zero, suppose their
common skew centralizer and their joint kernel vanish. For matrix i let
z_i be its zero-eigenspace dimension and let m_i(a) be the multiplicities
of the real eigenlevels of iA_i. Put ||m||^2=sum_(i,a)m_i(a)^2.
The skew stabilizer dimension s_i satisfies 2s_i=||m_i||^2-z_i:
zero space contributes z_i(z_i-1)/2, and each nonzero positive rotation
level of multiplicity h contributes h^2.

The derivative of the sum map on the product of orthogonal orbits is
onto so(r), since its trace-pairing annihilator is exactly the common
skew centralizer. Its kernel contains the simultaneous-conjugation
orbit, of dimension dim so(r). Therefore

 sum s_i <= (k-2)dim so(r),
 ||m||^2-sum z_i <= (k-2)r(r-1).

The map v -> (A_1 v,...,A_k v) is injective into the kernel of addition
from sum_i im A_i to R^r. Addition is onto because the joint kernel is
zero. Its kernel dimension is (k-1)r-sum z_i. Hence sum z_i <= (k-2)r,
and

                 ||m||^2 <= (k-2)r^2.

For two blocks of sizes r,h, Cauchy--Schwarz consequently bounds the
weighted cross-tie count by (k-2)rh/2. The three-orbit proof in the
source can start from rh/2 and force strictness using additional
structure. The same dimension computation for FOUR orbits gives rh,
not rh/2. Removing that factor is a new missing step.

There is an explicit four-orbit example where the proposed strict
inequality itself fails, even though the FULL common skew centralizer
is zero. Identify R^4 with Hamilton quaternions. Let L_i,L_j,R_i,R_j
be left/right multiplications by quaternion units. Define
 A=L_i+2R_i,
 B=L_j+2R_j,
 C=(3L_i+4L_j)/5+2R_j.
Each is skew and has eigenvalues i times {-3,-1,1,3}, each once. Left
and right quaternion multiplications commute; a combination L_u+R_v
with |u|=1,|v|=2 has those four eigenvalues. Also
 tr(AB)=0, tr(AC)=-12/5.

The pairs (A,B) and (A,C) each generate the whole Lie algebra so(4).
Indeed their projections onto its two simple so(3) factors are onto,
since the two axes in each factor are nonparallel. A subdirect Lie
subalgebra of two simple factors is either the product or the graph
of an isomorphism: kernels of its two projections are ideals, so if
either is nonzero it is the full product, and if both vanish it is a
graph. A graph here would send the first component of A, of norm 1,
to the second, of norm 2, contrary to preservation of the Killing
form by a Lie isomorphism. Thus it is the product.

The vector representation on R^4 is irreducible and its real commutant
is scalars: commuting with all left multiplications makes a map a right
multiplication, and commuting with all right multiplications makes its
quaternion scalar real. A nonzero intertwiner between the two pairs
would be invertible by irreducibility, and would imply equality of
tr(AB) and tr(AC), which is false. Consequently the block-diagonal
quadruple on R^4 direct-sum R^4

 (diag(A,A), -diag(A,A), diag(B,C), -diag(B,C))

has zero sum and no common nonzero skew centralizer. Its two block
profiles are identical: for each of four members, each of the levels
-3,-1,1,3 has multiplicity one. Their weighted cross-tie sum is
4*4/2=8, exactly R=rh/2=8. Thus R minus the four tie counts is zero,
not strictly positive. No nonzero joint kernel occurs (A is invertible).

This example does not have the odd block-parity condition of a
hypothetical minimal counterexample to Q4. It therefore blocks only
a blind extension using zero-sum orbit geometry and absence of a
common skew operator; it does not show that an appropriately refined
four-factor continuation theorem is impossible. The precise paid and
unpaid conditions must remain distinct.

profile_diagnostic.py independently supports the displayed finite
matrices over Q: quaternion relations, skewness, their spectral
polynomial and trace, two 15-rank centralizer systems, one 16-rank
cross-intertwiner system and the tie equality. Its receipt is NOT a
general spectral or representation-theoretic implementation.

## Stronger analytical diagnostic: odd block parity can also occur

The preceding rational checker concerns its stated even-parity example only.
The following distinct exact construction also has ODD parity in each block.
It is proved analytically; no finite checker is claimed to implement it.

Use quaternion imaginary space R^3 with coordinates (x,y,z). For block P set
 a1=(sqrt(15)/4,0,1/4), a2=(-sqrt(15)/4,0,1/4),
 a3=(0,0,-1), a4=(0,0,1/2).
For block Q set
 a'_j=(sqrt(35)/6*cos theta_j, sqrt(35)/6*sin theta_j,1/6), j=1,2,3,
 where theta=(0,2pi/3,4pi/3), and a'_4=(0,0,-1/2).
In BOTH blocks use
 b1=(sqrt(3)/4,0,1/4), b2=(-sqrt(3)/4,0,1/4),
 b3=(0,0,1/2), b4=(0,0,-1).
Both lists of a vectors sum to zero, as does the list of b vectors.
The a lengths are (1,1,1,1/2); the b lengths are (1/2,1/2,1/2,1).
Define X_j=L_(a_j)+R_(b_j), Y_j=L_(a'_j)+R_(b_j).
Then sum X_j=sum Y_j=0. All eight matrices have the same four simple
spectral levels for i times the skew matrix, namely +/-3/2,+/-1/2.
For each list the left and right projections of its generated Lie algebra
are onto so(3) (already two nonparallel vectors suffice), and the unequal
left/right lengths of its first matrix exclude a graph. The preceding
subdirect argument gives full so(4) in each block.

The trace identity tr((L_a+R_b)(L_c+R_d))=-4(a.c+b.d) gives
 tr(X1 X2)=4, tr(Y1 Y2)=7/3:
 a1.a2=-7/8, a'_1.a'_2=-11/24, b1.b2=-1/8.
Thus the two ordered quadruples have no nonzero intertwiner. Their direct
sum has no common nonzero skew centralizer, by the same scalar-commutant
argument as above; no joint kernel occurs.

Their signed Cartan coordinates in each four-dimensional block are
 (3/2,1/2) for members 1,2,3 and (3/2,-1/2) for member 4.
This follows from the signed rotation coordinates (|a|+|b|,|a|-|b|)
for L_a+R_b. The block sum is (6,1), of ODD coordinate sum 7.
After assembling two such blocks, the four ambient D4 labels are all
Weyl-conjugate to lambda=(3/2,3/2,1/2,1/2). Indeed the final member has
two negative rotation coordinates, and their simultaneous sign change
belongs to W(D4). Total external sum 4lambda=(6,6,2,2) is in Q(D4).
Thus the external weights meet the original congruence, and each internal
assigned block has odd parity. Nevertheless the weighted cross-tie count
is again 8=R, not strictly less.

This proves that zero-sum moment data, absence of a common skew operator,
and the two odd block parities STILL do not imply a four-orbit version of
the source's strict comparison count. It does not prove that these data
arise from a minimal two-segment schedule with all required cover/continuation
properties. In particular Q4 holds on these four equal self-dual weights
by pair contractions. The example is a method obstruction, not a new
substantial result or a counterexample to Q4.


## Primary comparison and selection limits

This is a bounded operation comparison. The source's exact thm:main is
triple saturation. Its prop:basic-schedule and lem:schedule-moment relate
ONE schedule to a three-orbit moment problem. thm:integral-schedule assumes
integral root pairings of ALL three labels and, in type D, at most one
zero coordinate in the moving weight; its zero-tail branch then handles
the remaining triple inputs. prop:columns constructs the Cartan summand
of ONE moving representation from a column shape. None of these read
interfaces supplies the free-junction lattice choice above. In particular,
the three-orbit strict comparison count is not a four-orbit theorem.

Berenstein--Sjamaar, *Coadjoint orbits, moment polytopes, and the
Hilbert--Mumford criterion*, Theorems 3.2.1--3.2.2, already pay rational
moment-polytope description and occurrence after some integral dilation.
These are used for the diagonal formulation, not credited as a new bridge.
The diagonal embedding K -> K x K specializes their branching theorem
to tensor products. A rational diagonal may be cleared by one common
multiple; a weight-lattice diagonal with the specified central congruence
then permits scale one by the stipulated triple theorem.

Sam, arXiv:1009.3040v2, Theorem 1.1/Corollary 1.2, already works for
ARBITRARILY MANY factors: factor two for special orthogonal/symplectic
groups and factor four for spin groups. Its introduction explicitly
contrasts the root-lattice scale-one conjecture and notes the Pfaffian
obstruction in the quiver method. That factor-four theorem is not Q4,
and no factor sharpening is silently assumed. Hong--Shen,
arXiv:1404.4098v2, Theorems 1.1/1.2 and Corollary 1.3, use tensor-basis
folding and supply factor two for odd spin groups; this is not an
integral gluing theorem for two even-spin triangle polytopes. Their
introduction formulates saturation for arbitrary arity and refers to
Spin(8); the exact Kiers interfaces inspected here are triples; the original KKM proof was not freshly read in this round.
The scope discrepancy is retained rather than turned into a claim of
freshness or a universal triple-to-polygon reduction.

Kapovich--Millson arXiv:math/0508186v1 Conjecture 1.4(1) is explicitly
about triples; its semigroup structure and translated-cone results do
not alone ensure normality after projection of the coupled fiber.
Kiers arXiv:1804.09229v3 Theorem 1.3 and Section 2.1 are also exact
triple/saturated-cone interfaces. Their finite-rank computations are
not reconstructed here and no new finite-rank statement is claimed.
The argument cannot be nominated on absence of an identical four-factor
title: S104 already identified the actual operation, and the broad
polygon literature may contain stronger reductions not established by
this screen. The coupled-system reformulation and diagnostic obstructions
are technical; their proof does not certify full Q4 or its novelty.

Other screened families were rejected before freezing: 177 coefficient
changes require their actual congruence/cohomology hypotheses, not an
F2-to-all-groups assertion; 314 easy cyclic-series computations would
repackage paid group operations; 313 all-dualizable finite generation
is already false for invertibles at height two, as Li's primary
arXiv:2110.08397v1 introduction and Theorem 4.22 state. No such known
counterexample is called a new discovery. The complete preprint tree
contains one family-204 mathematical manuscript directory; all its text
blobs were authenticated, but not every proof body was read.

## Exact unpaid step

For EVERY original tuple with a dilated invariant, prove that its real
common-diagonal set meets a+b+Q(Dn), equivalently that one of the faithful
coupled-schedule polytopes has a junction in that coset, or produce one
actual spin-representation tuple violating the original scale-one claim.
No such lattice-point theorem or counterexample was obtained.

Global root balance has an integral right-hand side but no proved
feasibility-preserving lattice deformation. The one-shape continuation
uses a fixed moving weight and Bruhat order; a free reset is not that
operation. Copying the three-orbit strict count to four is unjustified,
even with odd block parities, by the analytical example above. This does
not rule out a different global argument, a refined minimal-counterexample
condition, or a stronger primary polygon theorem. No conditional lemma,
low rank, repeated equal-weight example, or factor-four result is offered
as the frozen theorem's success. Q4 remains UNRESOLVED unchanged.

## Verification and reading boundaries

profile_diagnostic.py is standard-library exact rational arithmetic for
ONE explicit rational quaternionic profile example. Its two scalar
commutants have dimensions one and its cross-intertwiner space is zero,
verified by ranks 15,15,16 on sixteen matrix variables. It verifies
quaternion relations, skewness, spectral polynomial, trace differences
and equality of the four tie counts with R. The stronger odd-parity
example is proved analytically above and is NOT implemented by that
checker. No representation census, tensor-product decomposition engine,
full coupled-polytope enumeration, universal root-graph continuation,
Lean claim, or independent mathematical review is supplied by the receipt.

The checker was read and SHA256-authenticated before its first execution.
No historical or third-party code was executed. The only failed retrieval
was the nonexistent math/0508186v2 PDF; the distinct v1 primary was then
retrieved and read. Large historical searches/read windows sometimes
truncated; decisive relied-on passages were followed by focused reads.
source-contracts.md records exact semantic extents. Retrieval/authentication
of additional text blobs is not a claim to have read those manuscripts.

Mandatory continuity includes the complete 119315-character older brief
(SHA256 97f5b23fcd79fa6abc3850e6efdd3e001530665e26e9811fc5a4e61dcef9fb57),
the snapshotted ledger, full r8/r10/relative-CI-r2 reports and specified
parent dispositions, the supplied full Artin history and actual r11
scope/contracts/notes/screen. The already proved full Artin R stays
TECHNICAL with its spherical splitting attribution and all former
cross-Hom/unique-root objections; no Artin deduction is reopened here.
No earlier checker is rerun. Mutable context is snapshotted INSIDE this
owned directory; final verification never binds the future live ledger
or whole parent directories.

inputs-manifest.json and outputs-manifest.json bind exact membership,
size and SHA256. seal.json binds the manifests, and its detached SHA256
is reported externally. verify.py is read-only and offline: it authenticates
the external anchor, all entries, source Git blobs against the COMPLETE
tree, and code before replaying only the one finite checker under a
write/network-denying audit hook, with bytecode disabled. It compares
immutable stdout/stderr, regenerates nothing, and checks whole own-tree
hashes before/after on success AND failure. Integrity controls reject a
wrong anchor and altered payload in disposable owned copies while
preserving the original. Hashes establish integrity, not mathematics or
independent acceptance.

All new writes are inside fresh-structural-discovery-r12/. No nested
agents, shared/sibling/frozen-file edits, staging, commits, external
messages, uploads, publication or submissions occurred. Private source
rights are preserved. No acceptance or substantial nomination is requested.
