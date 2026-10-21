# PREFREEZE calculations: existing biregular-pattern scope

No theorem is frozen. The existing i13 target remains: a connected finite simple bipartite graph F, regular on each part, and a finite simple host G with p(G)>0 and t(F,G)<p(G)^e(F), counting ALL homomorphisms. The regular-triangulation incidence construction is a route, not a restricted replacement target. Full i13 Section3 and actual Source161 kernel proof were read before these calculations. The old pinning identity and averaged-sign obstruction are credited, not new results.

## Fixed-sign collapsed coefficients

Let K be a connected face-neighbor complex of distinct triples, every point pair in exactly two faces. Let E be its pairs, C its corners, m=|C|=2|E|. Make a graph L with vertex set E; each corner joins the two pairs meeting there. It is the line graph of the cubic face-neighbor graph, and is connected and 4-regular. At a fixed target corner k, the base moment matrix on nonempty subsets has 63 isolated diagonal states (nonempty subsets of Gamma_k), each diagonal1. The64 states containing k pair under alpha -> alpha XOR Gamma_k, giving32 blocks (1/2)[[1,sigma_k theta],[sigma_k theta,1]]. Remaining states have zero moments.

For a type map collapsing both parts to k, every nonzero label configuration lies in one of these blocks or singleton states. Therefore its coefficient is exactly

 C(k)=63+32*2^(-m)*sum_{s:E->{0,1}} (sigma_k theta)^(|delta_L(s)|).

Every cut of a4-regular graph has even size: |delta(S)|=4|S|-2|E(S)|. Thus this expression is independent of sigma_k and >=63+64*2^(-m). This is a fixed-sign version of the old diagonal lower bound, NOT a sign classification of all type maps. In particular the positive averaged sum in i13 does not exclude negative fixed-sign sums, and this formula still does not exclude them.

At a source face, XOR of the three successive subset differences vanishes. Signed local entries have difference Gamma at the corresponding target corner; diagonal entries have difference0. If the three target points in the target face are distinct, the three Gamma vectors are distinct, nonzero, and sum0, so there are either zero or three signed entries. If the image has only two distinct points, either none are signed or the two repeated target corners are signed. If all coincide, either zero or two are signed. Thus negative sign products arise only from fully signed nondegenerate faces, while degenerate faces contribute positive sign products. This does not yet constrain the global parity multiplicities of such target faces.

## Full matrix collapse (new route diagnostic, not an upstream audit)

Write v=number of points, f=number of faces, D=2r, b(a)=a(a+1)/2. For a fixed sign xi, the source elementary signed-rank mass is
 p_xi=(1/2+O_D(1/q))*q^(-b(r)).
For independent uniform symmetric D-by-D matrices at the pattern vertices, consider the exact event that ALL v point matrices equal. Its probability is q^(-(v-1)b(D)). Every face then has one center Y and three equal differences X-Y, and
 E_Y K_xi(X-Y)^3=p_xi^(-2).
So its contribution to the all-active, all-same-sign rank-layer integral is EXACTLY

 q^(-(v-1)b(D))*p_xi^(-2f),

with exponent E_D=2f b(D/2)-(v-1)b(D).
For d-regular points,3f=dv. For d=6,f=2v,
 E_D=(D^2+(v+1)D)/2 >0.
More generally if chi=v-|E|+f=v-f/2,
 E_D=((1-chi)D^2+(v-2chi+1)D)/2.
Thus the native half-rank all-activity limit cannot be transferred unchanged to regular triangular complexes with d>=6: this nonnegative singular contribution diverges, whereas the proposed parity expression is finite. This statement concerns a CHANGED pattern, not the stipulated source complex. For its v=13,f=22, E_D=(-D^2+10D)/2 is negative for D>10, compatible with the source proof.

For fixed finite type/activation parameters with any positive-probability nonempty activation atom (S,xi) at a positive-mass type pair(a,b), collapse all point types to a, all face types to b, and select that SAME activation atom at every incidence. Distinct incidences sample independently. On each coordinate k in S restrict all point matrices to coincide. The resulting lower bound on the oriented density is

 pi_a^v nu_b^f c^(3f) product_{k in S}[q^(-(v-1)b(D))*p_(xi_k)^(-2f)].

Here c>0 is the atom probability, including thinning if present. For d>=6 this tends to infinity as q->infinity, with all these finite parameters fixed. Therefore merely optimizing fixed signs and then importing the same rank-layer limit cannot close the old target. This does NOT exclude q-dependent activation/priors, truncated/conditioned kernels, changed geometry, other ranks, or other constructions. It also does not settle the finite coefficient's sign.

The exact finite lower bound and local moment formulas will be checked independently by small arithmetic diagnostics. Source transverse/orbit/tail proofs are being read, not audited. Classical host regularization and blow-up proofs still require full reading before an integrated stopping assessment.
