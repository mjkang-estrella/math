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
