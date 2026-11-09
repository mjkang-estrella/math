# Personal ordinary verification and shortest proof — 382297

This verifies the disclosed author mechanism, not independent invention. No formal execution or credit.

Exact statement: for every n>=0 and fixed u,v in T_n with arcs i->j iff i<j, give each horizontal arc in each layer an independent fair bit and each index ONE fair bidirectional vertical token. Under the uniform law on all 2^(n^2) outcomes, P(u0 reaches v0)>=P(u0 reaches v1). Reach includes the zero-length path.

## Shortest proof I can justify

Fix u<v and reveal successive prefixes starting at u. Let (A,B) count the reachable vertices in the two layers. Index monotonicity makes prefix reachability final for its vertices. Given any full revealed prefix with counts (a,b), the fresh incoming bits give independent X,Y with failure probabilities 2^-a,2^-b. With independent fair vertical bit Z, the new reach indicators are U=X or (ZY), V=Y or (ZX), and the counts become (a+U,b+V). This law depends only on counts: every earlier vertex is a predecessor of the new vertex, and horizontal tokens in different layers are distinct.

Write rho(a,b)=(b,a). The transition kernel is rho-equivariant and cannot jump from a>b to a<b or conversely, because the difference changes by at most one. Initially the law is half at (1,0), half at (1,1). For t above the diagonal, pair reflected predecessors to obtain

    (mu K)(t)-(mu K)(rho t)
      = sum_(s above) (mu(s)-mu(rho s)) K(s,t) >=0.

Diagonal predecessors cancel and the missing cross term is zero by no-crossing. Thus reflected mass dominance persists. Finally E(U-V|a,b)=(2^-b-2^-a)/2 is antisymmetric and nonnegative above the diagonal. Pairing reflected states proves E(U-V)>=0 at v, precisely the desired event-probability difference. If v<u both events are impossible; if v=u their probabilities are 1 and 1/2. n=0 is vacuous. Relabel a transitive tournament by its order. QED.

This is about 300 words plus one displayed identity, approximately half a page with dense typesetting or one page with the model defined. It is not a proof in two or three lines. The count sufficiency, no-crossing and endpoint identification cannot be omitted.

## Detailed independent checks of the author proof

All tokens with maximum touched index <=k form the revealed sigma-field. A path to <=k cannot visit a larger index; vertices <u never matter. Future and discarded bits are summed over, not forced absent. A path entering j>u first enters horizontally from a previously reachable copy; its only within-j closure is the shared vertical token. This proves U,V exactly, without the circular implication that reachability of one vertical partner alone constitutes an incoming path.

Put q=2^-a,r=2^-b. For increments (0,0),(1,0),(0,1),(1,1), the four probabilities are qr, (1-q)r/2, q(1-r)/2, 1-(q+r)/2. They sum to one. Independence is on each full-prefix fiber; all fibers with the same counts have the same law, so conditioning only on counts is valid. Even if the reachable sets overlap, incoming tokens differ by layer. Reflection swaps the two middle probabilities. Since a-b is integer, a single +-1 increment cannot cross from strict positive to strict negative. Diagonal departures cancel in the paired sum; they are not forbidden. This proves a signed distributional invariant, stronger than an expected-count comparison; it does not assert A>=B for every outcome. The payoff identity U-V=(1-Z)(X-Y) gives the displayed nonlinear antisymmetric payoff. All sums are finite.

The supplied Lean text defines HToken with i<j, Token=HToken sum Fin n, Out=Token->Bool, and a vertical Arc clause controlled by exactly omega(vtok i) for both directions. Reach is ReflTransGen. These definitions match the source under its conventional length-zero path interpretation. The code text is not a kernel certificate. Its reach_char is an equivalence involving partner reachability, not by itself a noncircular first-entry/least-closure proof; later formal work must prove the X,Y closure bridge. I found no semantic defect in the supplied definitions. No Lean was run.

## A genuinely broader consequence, with its limits

The same proof works conditional on ANY fixed post set T, with independent horizontal probabilities p_j in [0,1] shared by every incoming arc i->j and both layers. Then Z_j=1_(j in T), q_j=1-p_j, failure probabilities are q_j^a,q_j^b (q^0=1 including q=0), and g_j=(1-Z_j)(q_j^b-q_j^a). The kernel is time-inhomogeneous but remains equivariant and no-crossing. Initial counts are (1,1) or (1,0). An independent arbitrary random post set is therefore also allowed by conditioning. The E7 endpoint is the p_j=1/2, independent fair-post specialization of this reviewer-authored extension. No separate credit or established literature priority is asserted for it.

One can also set p_j=0 at selected columns, corresponding to vertices with no incoming edges, or take disjoint unions of ordered complete components. This does not prove the statement for arbitrary posets, interval orders, nested proper predecessor sets or general acyclic digraphs. A missing predecessor changes q^a into q^(number of reachable predecessors). Two prefixes with the same total a,b can then have different next laws. For a concrete obstruction to count sufficiency, take a later vertex whose only predecessor is x: a prefix reaching x0 but not y0 and one reaching y0 but not x0 have equal counts, yet different entry probabilities. Even a transitive poset with x<j and y incomparable with j exhibits this issue. Merely nesting predecessor sets does not repair the total-count recursion. Weighted counts for tail-dependent p_i have unequal increments and lose the no-crossing argument. I have no full replacement proof for those classes.
