# Same-status lowering and the AH 8.6 counting interface

Live author derivation. This supplies a supporting interface, not the full target.
The deterministic order/label setup preceding AH Lemmas8.3–8.5 is still required.
AH extracted lines1500–1860 were actually read, including full8.3–8.6 proofs.
Use the cubic cap from cubic-wall.md throughout.

## A reversible single-edge change

Choose thresholds a_o<b_o<M and M<a_c<b_c with
P(t<=a_o)>0 and P(M<t<=a_c)>0, and let
p=min(P(t<=a_o | t<=M),P(t<=a_c | t>M))>0.
Take M sufficiently large that q=P(t>M) is arbitrarily small, and b_o
sufficiently close to the essential infimum that P(t<b_o) is arbitrarily small.
Nonatomicity allows a_o<b_o with positive lower mass. For unbounded G the
closed thresholds also exist. Put delta=min(b_o-a_o,b_c-a_c)/2>0.
An original edge is good when t in [b_o,M] union [b_c,infinity).
Its bad probability is at most P(t<b_o)+q, which we choose <1/144.
This does not assume an interval density; arbitrary nonatomic laws qualify.

For an edge e, condition on all other original weights, all auxiliaries U,
and the status I_e=1{t_e<=M}; independently resample t_e from its conditional
law given I_e. This kernel is reversible for the full underlying product law.
It leaves every open indicator, and therefore every L_f, unchanged. All
capped weights except s_e remain exactly fixed. If e is good and uncapped,
with conditional probability at least p the new original is in its lower
band (<=a_o or in (M,a_c]), and then
s'_e <= t'_e <= a_status < t_e-2delta = s_e-2delta.
In particular the strict decrement exceeds delta. Conditional on the full
outside capped field need not have this property; we use the underlying
reversible coupling instead and do not assert capped finite energy.

## High-probability geometric inputs

For every simple path of length ell, the probability of at least ell/2 bad
original edges is <=2^ell epsilon^(ell/2), where epsilon<1/144 is the bad mass.
There are at most 4*3^(ell-1) such paths from a fixed vertex. A union over
O(n²) starting vertices and ell>=n tends to zero, since 6sqrt(epsilon)<1/2.
Thus, with probability tending to one, every such long path starting in the
box [-2n,2n]^2 has at least half good original edges.

For fixed v, all capped edges on any s-ray from v lie in the finite set E_v
from tail-and-modification.md, simultaneously for all its rays. Hence with
probability tending to one every edge of every such ray outside [-n,n]^2
is uncapped. Combining these facts, every v-ray crossing the annulus between
[-n,n]^2 and [-2n,2n]^2 has at least gamma*n eligible (good and uncapped)
edges, with gamma=1/3 adequate for endpoint conventions. Use the subpath
from a last inner-boundary contact before a first outer-boundary contact;
its length is at least n-O(1). This is uniform over the rays from this fixed v.

The following elementary argument supplies the uniform length input C1,
without invoking the unknown full structural theorem for the cap law.
For integer R define a local cap by searching all protecting circuits of
length <=R inside the radius-R neighborhood of e, using their minimum length
when present and R otherwise. Put s_e^R=min(t_e,M((L_e^R)^3+U_e)).
It is bounded by M(R³+1), depends only on underlying variables within O(R)
of e, and equals s_e whenever L_e<=R. Indeed every length<=R circuit
surrounding e lies in that neighborhood. Consequently
P(s_e^R!=s_e)<=C exp(-c sqrt(R)), and
E s_e^R <= E s_e + M(R³+1) C exp(-c sqrt(R)) <= C_* uniformly in R.

Choose R=ceil((log(n+2))^4). In each horizontal or vertical box row, split
edges into at most c0 R residue classes with disjoint dependency neighborhoods.
The approximating variables within each class are independent. Hoeffding's
inequality and a union over these classes show that a row of O(n) edges has
sum exceeding C_1 n with probability at most
C_2 R exp(-c_2 n/R^7), for fixed sufficiently large C_1.
(The deviation assigned to each class is order n/R, its size order n/R,
and the squared variable bound order R^6.) A union over O(n) rows and the
O(n²) coupling failures tends to zero. On the resulting event every horizontal
and vertical route within [-2n,2n]^2 has cost <=C_1 n, so every pair of box
vertices has T_s<=2C_1 n by a two-segment coordinate route.

Finally choose a in (0,M) with P(t<a)<1/144. The preceding iid path count,
now with low-cost originals as bad edges, says that every path of length
ell>=n starting in the box has s-cost at least a*ell/2, with probability
tending to one: s_e>=min(t_e,M). Therefore every box-to-box geodesic has
length <=Ln for a fixed L>4C_1/a+1. This also proves existence of finite
minimizers: from each fixed starting vertex, sufficiently long simple paths
have cost diverging linearly, almost surely, by the summable path bound.
Call this uniform length event C1(n); P(C1(n))->1. Its version with 3L is C1'(n).
Uniqueness is a separate previously stated continuous-auxiliary fact; this
length proof does not rely on uniqueness.

## Conditional inverse counting

Let F_n be the sigma-field of original t_e and U_e for edges with both
endpoints in [-n,n]^2. These sigma-fields exhaust the underlying space;
A and all cap-geodesic events are measurable on that space. For edges in the
annular set E_n with an endpoint outside the inner box and both endpoints
in the outer box (adjust boundary convention by one lattice unit if needed),
the same-status resampling leaves F_n fixed. Reversibility thus holds
conditionally on F_n.

Fix AH's A=A(v,P1,P2,P3,delta), with all its finite paths inside the inner box.
Let D_e mean that e is good and uncapped. Assuming the deterministic AH8.5
setup applies to the cap geodesics, a successful decrement at e in g1 gives
A^c and puts e in the new clockwise-most g1. This is exactly the single-edge
reasoning in AH8.4–8.6: no other cap edge changes. Furthermore C1 implies
C1' in the modified configuration. A changed box-to-box geodesic must use e;
its two pieces avoiding e are old geodesics between box vertices, each of
length <=Ln, giving length <=2Ln+1<=3Ln. Unchanged geodesics already obey C1.
Reversibility and the success probability p therefore give

 p P(A intersect C1 intersect D_e intersect {e in g1} | F_n)
 <= P(A^c intersect C1' intersect {e in g1} | F_n).

Let C2(n,v) be the high-probability good/uncapped annular crossing event above.
On A intersect C1 intersect C2 there are at least gamma*n eligible g1 edges.
On C1', g1 has at most 3Ln edges in E_n: its subpath between first and last
visits to the outer box is a box-to-box geodesic of that maximum length.
Summing the preceding inequality gives

 P(A | F_n) <= P(C1^c | F_n)+P(C2^c | F_n)
               + (3L/(p gamma)) P(A^c | F_n).

If P(A)>0, Markov's inequality and P(C1^c)+P(C2^c)->0 show that, outside a
set of probability <P(A)/2, both conditional error probabilities are <1/4
for large n. Hence on that set P(A|F_n)<1-1/(2(1+3L/(p gamma))). This
contradicts martingale convergence P(A|F_n)->1_A. Thus P(A)=0, conditional
on the preceding deterministic AH order/geodesic setup. Equivalently the
AH8.6 density step has a replacement on the underlying iid space.

This does not establish the construction of the initial coalescing reference
families, their uniform Busemann/shape control, the label construction, or
label stability under the cubic-wall modification. Those remain separate
full-target obligations. In particular no blanket A2(v) or A2(vii) property
of the cap field is claimed.
