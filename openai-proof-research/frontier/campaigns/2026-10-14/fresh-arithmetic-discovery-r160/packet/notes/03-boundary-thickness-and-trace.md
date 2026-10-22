# Boundary calculations and strongest alternatives

These are feasibility calculations for the unchanged question in 00-scope.md. Numerical or local compatibility is not asserted to produce a global counterexample or a solution.

## A. A local contact model distinguishes scalar and vector extension

Let R=C[[tau]], let r>=1, and consider uv=tau^r. On a Darboux target with coordinates (q,p,z), use alpha=dz-p dq and the regular map

    q=v, p=0, z=u.

The pullback contact differential is du. In the relative dualizing generator gamma=du/u=-dv/v it is eta=u gamma. Along A=(v,tau), its generic order is zero; along J=(u,tau), its order is r. The special map on A is transverse and the map on J is nonconstant horizontal. These are the local features of an L-degree distribution (2,0), rather than (1,1). No compact realization of this local degeneration in the full b2=1 target is asserted.

For the first point use coordinate u on A; for the second use v on J. The common smooth-fiber coordinate is u in the first factor and tau^r/v in the second. Therefore the invariant source bivector is

    K partial_u tensor partial_v,
    K=-(uv-tau^r)^2/tau^r.

The map derivatives and their contact values are

    de_A(partial_u)=-(tau^r/u^2) partial_q + partial_z,
    de_J(partial_v)=partial_q-(tau^r/v^2) partial_z,
    alpha(de_A)=1, alpha(de_J)=-tau^r/v^2.

Thus the scalar value is

    xi=(uv-tau^r)^2/v^2,

regular at the mixed-component generic point (u and v are units there). W12 is xi times [-(tau^r/u^2) partial_q+partial_z] in the first slot and is regular. But W21 has partial_q coefficient

    -(uv-tau^r)^2/tau^r,

with pole of order r. Multiplying by two contact factors repairs the scalar; it does not repair both one-contact-factor vector lifts. This directly explains why scalar extension would make normalized trace useful but would not license the source's original test-line descent.

Nonconstant contact-degree-zero rational curves are not excluded by the contact condition alone. For example, let Z=P1×E with E an elliptic curve and X=P(T*Z). Along C=P1×{e}, the constant cotangent line pulled back from E defines a section j:C->X. Its tautological O(-1) and hence its contact line O(1) are trivial on C. The tautological contact condition is satisfied by the tangent to C because that cotangent vector annihilates the P1 direction. This is a genuine nonconstant horizontal degree-zero curve. This example has b2>=2, is not rationally connected, and is NOT a counterexample to 00-scope. It merely prevents eliminating such curves by a local contact assertion without using the missing global hypotheses.

## B. Additive thickness on a degree-two boundary tree

Take a regular semistable genus-zero family over a DVR, with special components C_i forming a tree, and a map to a contact target. Assume the generic contact degree is two and the generic contact differential is nonzero. Put e_i=deg(e*L|C_i), val_i=valence(C_i), and N=e*L tensor omega. On the generic P1, N has degree zero and eta is nowhere zero. Its effective divisor is therefore vertical:

    div(eta)=sum a_i C_i, a_i>=0.

Intersection on the regular semistable surface gives

    e_i-2+val_i = sum_(j adjacent i)(a_j-a_i).                 (B1)

Indeed C_i^2=-val_i, pairwise adjacent intersections are one, and deg omega|C_i=-2+val_i. For an edge whose removal cuts off a connected subtree S with boundary vertex v and outside neighbor w, sum (B1) on S. Internal edges cancel and sum_S val_i=2|S|-1, so

    a_w-a_v = e(S)-1.                                       (B2)

These equations are valid even if some e_i are negative. They make plain why total degree two alone is insufficient to infer the source's two degree-one components.

First suppose e_i>=0. If a single vertex has degree two, (B2) makes a_i=a_root+dist(i,root). On a chain, the mixed bivector pole is the distance between the selected components. Thus a_i+a_j>=dist(i,j): the two contact factors have enough total order for the scalar. One individual contact factor need not have enough order, exactly as in A. This is a valuation calculation; for general branching it is used as a conditional calculation once the analogous bivector pole bound is established.

If two vertices have degree one and all others degree zero, (B2) makes a_i constant, say c, along the entire path between them, and makes a_i grow by distance away from that path. Horizontality on a degree-one component implies c>=1 in a reduced semistable model. It supplies no bound proportional to the length of the path.

This discrepancy is explicit for a chain. Resolve the standard family xy=tau^R, which introduces a chain of R edges of thickness one. At the two end-component generic points the invariant bivector has exact order -R, as follows from

    -(xy-tau^R)^2/tau^R partial_x tensor partial_y.

For contact multidegrees (1,0,...,0,1), N has degree zero on every component, hence is trivial on the special tree. The source's cohomology argument gives N a global unit generator and eta=h_R m. Write c=ord_tau(h_R). The dualizing-image condition at each thickness-one node gives c>=1. For uncontracted nodes of thickness r_j it gives c>=max r_j. The mixed end-to-end scalar order is

    2c-R, where R=sum r_j,

and the generic vector-lift order, when its ordinary derivative on the other end is nonzero, is

    c-R.

For example, R=3 and c=1 satisfy the multidegree graph equations and all individual thickness-one ideal tests, but give scalar order -1 and vector order -2. These are COMPATIBLE NUMERICAL/LOCAL DATA, not an assertion that a global contact stable map realizing them exists. A global contact identity might rule them out; establishing that stronger identity is precisely an unpaid operation.

If every intermediate degree-zero component is actually contracted by the map to X, one can contract the source chain to xy=tau^R and descend the map. Then the source's ideal-intersection proof at the resulting thick node gives h_R in (tau^R), paying c>=R and both lifts. The obstruction concerns NONCONSTANT degree-zero components, which cannot be contracted as maps to X. Collapsing their source curves while silently retaining an evaluation map would be invalid.

Allowing negative e_i makes (B2) still less restrictive: differences a_w-a_v can have magnitude larger than one. No nefness of L on the exploratory target has been proved. Consequently even the nonnegative-degree boundary analysis does not exhaust its boundary types.

## C. Can primary divisor duality bypass the chain problem?

Buczynski's actual construction begins with a proper degree-one family whose through-point tangent geometry is controlled. It makes D_x the two-line locus, proves it is a divisor for EVERY x, and uses symmetry to produce a basepoint-free system in E=L^k. On a Moishezon manifold, if such a system and a nowhere-zero exact contact quadratic symbol in E could be obtained, one might force an immersion and positivity. But the actual proof of finiteness uses ampleness of E, and the exact weight k=1 is not a consequence of the duality argument. Its form can even be alternating before homogeneous identification. Neither a nonexistent degree-one family nor k=1 can be inserted into this route.

The source's symmetric-jet proof is nevertheless a complete downstream route once the correct tensor exists; Section 02.5 shows how its immersion itself proves projectivity. Thus the problem is not a missing homogeneous-model list. It is the global production, extension, and all-sheet compatibility of the tensor before projectivity.

## D. Arithmetic and low-dimensional comparison

The dimension-three primary succeeds without contact-line descent. It combines the contact Chern identities with a very specific Moishezon index theorem and an h0 bound. In every odd dimension, Serre duality and K=L^(-(n+1)) give the Hilbert-polynomial identity

    P(t)=chi(L^t)=-P(-t-n-1),  P(0)=1.

Hence P is odd in x=t+(n+1)/2. In dimension five this reads

    P(t)=a x^5+b x^3+c x,
    (243/32)a+(27/8)b+(3/2)c=1,
    P(1)=85a+10b+5/3,
    a=integral_X c1(L)^5/120.

These are exact constraints, but they provide neither the needed sign/vanishing control on intermediate cohomology nor a higher-dimensional upper bound on h0(L). The dimension-three contradiction h0(L)>=10>7 therefore has no established uniform-dimensional analogue here. Riemann–Roch is a comparison, not a second substitute target.

## E. Remaining full-scope operation

The proper dominating family, big contact line, simple connectivity, full local value–velocity variation, exact target of the trace map, and downstream jet-to-projectivity argument are accounted for. What has not been constructed uniformly for the objects in 00-scope is a global symmetric section B in L box L with diagonal symbol theta^2.

In the source-style curve route this requires, first, degree-two transversely very free curves (or a genuinely different controlled family; arbitrary high degree is ruled out by the explicit P3 fixed-end variation). It then requires a global boundary identity that handles every nonconstant zero- or negative-degree component and, for a trace substitute, EVERY sheet over the diagonal. Additive thickness c>=R for vector lifts, or sufficient scalar order plus the all-sheet congruence from 02.4, are precise interfaces. No such identity has been proved from rational connectedness, class C, b2=1, and contact nondegeneracy. This is an unfinished construction, not a nonexistence theorem, no-go theorem for all alternative routes, or a nominee with added hypotheses.
