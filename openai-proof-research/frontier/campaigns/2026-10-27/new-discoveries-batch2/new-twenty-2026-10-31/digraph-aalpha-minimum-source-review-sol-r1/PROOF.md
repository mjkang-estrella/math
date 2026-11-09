# Independent ordinary proof and exhaustive arc audit: 350767

Review only. Credit 0. No Lean, computation of mathematical cases, CAS or child agents. The mechanism was disclosed in the task; independence means verification, not independent invention. PRE-CANDIDATE.md records the scalar reconstruction and precise remaining structural gap before FULLCANDIDATE.md was opened. Its initially inverted chain propagation is immediately corrected there; the equations below use the corrected direction.

## Endpoint and matrix facts
For every n>=5 and 0<=alpha<1, use finite simple strongly connected digraphs, allowing opposite arcs. The first four distinct radii have unique isomorphism types C_n, theta(0,1,n-3), theta(1,1,n-4), theta(0,2,n-4). A=alpha D_out+(1-alpha)Adj, radius means maximum modulus of complex eigenvalues. This proves the cached conjecture and strengthens its phrasing by uniqueness.

Use standard Perron-Frobenius for finite nonnegative irreducible matrices: positive right and left Perron vectors; eigenvalue equals spectral radius; row-sum bounds with equality only if row sums constant; strict comparison against a distinct dominated nonnegative matrix, even if the latter is reducible. These are genuine ordinary background dependencies, not implemented formal facts. Strong connectivity makes A irreducible even when alpha=0, since 1-alpha>0. All outdegrees >=1. If every degree is 1, strong connectivity forces one spanning directed cycle. Otherwise radius>1: nonconstant row sums give strictness, and constant row sum d>=2 gives radius=d. The unconditional claim radius<maximum outdegree for all noncycles is false for regular digraphs; it is needed only for the nonregular degree-1/2 graphs below, where 1<lambda<2.

For a strongly connected proper subdigraph H of G, extend its matrix with zero rows/columns. It is entrywise <=A(G) and distinct: any missing arc changes an off-diagonal entry by 1-alpha>0; a missing vertex in a strongly connected larger graph also entails a missing incident arc. Thus rho(H)<rho(G), including alpha=0. No artificial diagonal alpha is placed at the padded vertices. For completeness, strict comparison follows by taking the nonnegative Perron vector y of the smaller matrix, spreading it with powers of I+A(G) to get a positive vector, and applying the positive left Perron vector; equality would force every propagated strict defect to vanish, contrary to irreducibility. This is the usual irreducible strict-monotonicity theorem; it does not require the padded matrix to be irreducible.

## Scalar equations and all root orders
Set d=1-alpha>0, r=alpha/d, t=(lambda-alpha)/d, s=t-r. A degree-one row gives t*x_v=x_successor. A degree-two row gives s*x_v=sum successor coordinates. Hence t>1, s>0, s<=t in these graphs. The return-path convention is two forward paths with a,b internal vertices and one opposite return with c internal vertices. Their lengths in arcs are a+1,b+1,c+1, respectively, n=a+b+c+2. Simplicity excludes a=b=0, and a<=b.

At the branch w of theta(a,b,c), propagation of the positive coordinates gives
s=t^(-(a+c+1))+t^(-(b+c+1))=(t^a+t^b)/t^(n-1).
For infinity(k,l), cycles have lengths k+1,l+1 and n=k+l+1, k,l>=1; the equation is
s=t^(-k)+t^(-l)=(t^k+t^l)/t^(n-1).
The residual t-r minus the displayed sum is strictly increasing for t>1 (all exponents on the right are strictly negative), and the Perron vector supplies a root. Thus there is exactly one root in this interval and a positive residual means the testing t exceeds that root. We never infer root order from the unnormalized polynomial alone.

On n>=5, the first three theta numerators are 1+t, 2t, 1+t^2. Their successive differences are t-1>0 and (t-1)^2>0. The only permissible pairs with b<=1 are (0,1),(1,1); otherwise b>=2 and t^a+t^b>=1+t^2, equality exactly (0,2). Their c values are forced by n, hence equality gives exactly the three stated isomorphism types. For infinity, if min(k,l)>=2, its numerator >=2t^2>1+t^2. Otherwise k=1,l>=3 (or swapped), and t+t^l>=t+t^3>1+t^2, since t^3-t^2+t-1=(t-1)(t^2+1)>0. This includes n=5.

At any order h>=3 the smallest bicyclic normalized right side is (1+t)/t^(h-1): infinity has numerator>=2t>1+t. If h<n, put it over denominator t^(n-1). Its numerator is >=t(1+t)>1+t^2. Therefore every bicyclic graph on fewer than n vertices already has radius greater than the proposed fourth graph. This pays h=3,4 directly and avoids invalid invocation of an n>=5 theorem at smaller orders.

Every strongly connected bicyclic graph is theta or infinity: with n+1 arcs and every outdegree and indegree positive, exactly one vertex has outdegree 2 and exactly one has indegree 2, all others 1. If these vertices coincide, tracing the outgoing arcs gives two internally disjoint cycles through that vertex (infinity); otherwise they give two internally disjoint directed paths to the indegree-2 vertex and a unique return path (theta). Strong connectivity forbids a separate cycle component. This is a classification of the actual directed graphs, not undirected bicyclic graphs.

## Reduction to two spanning exceptions
A shortest directed cycle C in a noncycle strongly connected simple graph is nonspanning: if it spanned, any extra arc plus the appropriate directed segment of C produces a shorter cycle, including the opposite-arc 2-cycle case. Strong connectivity supplies an excursion from C through an outside vertex and back. Take a shortest such excursion; its interior is outside C and has distinct vertices. The union with C is infinity if the endpoints coincide and theta otherwise, and has one more arc than vertices. This proves existence even when C has length 2. No assumption of oriented graphs is made.

If G is not itself bicyclic, this union is proper. A nonspanning bicyclic subgraph settles G by strict comparison and the preceding small-order bound. A spanning infinity or spanning theta other than the first two does likewise. It remains only to inspect all missing arcs of the first two spanning thetas. The following tables are a symbolic hand audit, not an enumeration program. For each theta entry, the direct added arc is the zero-internal forward path when a zero occurs; the alternate path follows the indicated original chain, and the remaining original segment is the return. These paths share just their endpoints. Tuples may require swapping the first two equal-direction parameters to enforce a<=b.

### First exception
Vertices w,u,v,z1,...,zm, m=n-3>=2. Original arcs: wv,wu,uv,vz1,z1z2,...,z_(m-1)zm,zmw.

|Extra arc|Witness theta(a,b,c)|Order / construction|
|--|--|--|
|v w|(0,m,0)|n-1; parallel v->w and v->z1->...->zm->w, return wv; omit u|
|v u|(0,m+1,0)|n; long v->chain->w->u, return uv|
|u w|(0,m+1,0)|n; long u->v->chain->w, return wu|
|u z_j, 2<=j<=m|(0,j,m-j+1)|n; alternate u->v->z1->...->zj; return through zm,w,u|
|z_i u, 1<=i<m|(0,m-i+1,i)|n; alternate zi->...->zm->w->u; return u->v->...->zi|
|w z_j, 1<=j<=m|(0,j,m-j)|n-1; alternate w->v->...->zj; omit u|
|z_i v, 1<=i<=m|(0,m-i+1,i-1)|n-1; alternate zi->...->zm->w->v; omit u|
|z_i w, 1<=i<m|(0,1,i)|i+3<n; retain original short branches and shortened return|
|v z_j, 2<=j<=m|(0,1,m-j+1)|m-j+4<n; shortened return|
|z_j z_i, 1<=i<j<=m|(0,m-j+i+1,j-i-1)|n-1; long path zj->...->zm->w->v->...->zi; omit u|
|z_i z_j, j>=i+2|(0,1,m+i-j+1)|m+i-j+4<n; shortened return|
|u z1 or zm u|single exception|treated below|

All spanning tuples here outside the exceptions have b>=2, since m>=2 and the relevant indices exclude the endpoints. Thus their radii are at least the fourth. Other rows have order<n. If both exceptional arcs occur, use u->z1 and u->v->z1 with return z1->...->zm->u; theta(0,1,m-1) of order n-1, omitting w.

Exhaustion by tails, for every m: w has only nonarcs to z_j; u has nonarcs w,z_j; v has nonarcs w,u,z_j(j>=2); each z_i has nonarcs u,v, w(i<m), all earlier z_j and all later z_j except its existing successor. Loops and the listed original arcs are excluded. These disjoint categories exhaust every ordered distinct pair.

At n=5,m=2, the full missing-arc lists are: w:{z1,z2}; u:{w,z1,z2}; v:{w,u,z2}; z1:{w,u,v}; z2:{u,v,z1}. Here uz1,z2u are exceptions; uz2 and z1u give (0,2,1); wz1,wz2,z1v,z2v give smaller-order tuples as in the table; z1w and vz2 shorten the return; z2z1 gives (0,2,0). There is no forward skip on the two-vertex chain. Both exceptions give theta(0,1,1) on four vertices. The vw,vu,uw rows remain as above. Thus no boundary pair is omitted.

The cached Xi-Wang p9 row(6) prints theta(0,n-l+k-1,l-k-1) for z_l z_k. That tuple would have order n, but its proposed path omits u and has order n-1. The correct first long internal count is n-l+k-2=m-l+k+1. This is an ancillary source typo, not a new result or reason to reject the actual path reduction. Li-Zhou p5(vi) has the latter count.

### Second exception
Vertices u,w,b,v,z1,...,zm, m=n-4>=1. Original arcs: uw,wv,ub,bv,vz1,z1z2,...,zmu.

|Extra arc|Witness theta|Order / construction|
|--|--|--|
|w u or v w|(0,m+1,0)|n-1, omit b; alternate path follows v,chain,u|
|b u or v b|(0,m+1,0)|n-1, omit w; symmetric|
|v u|(1,1,0)|4<n; original two short forward paths, direct return|
|u v|(0,1,m)|n-1; use uv and uwv, omit b|
|w z_j or b z_j|(0,j,m-j+1)|n-1; alternate via v,z1,...,zj; omit the other short-branch vertex|
|z_i w or z_i b|(0,m-i+1,i)|n-1; alternate via chain,u; omit the other short branch|
|v z_j, j>=2|(1,1,m-j+1)|m-j+5<n; shortened return|
|u z_j|(0,j+1,m-j)|n-1; alternate via w,v,z1,...,zj; omit b|
|z_i v|(0,m-i+2,i-1)|n-1; alternate via chain,u,w,v; omit b|
|z_i u, i<m|(1,1,i)|i+4<n; shortened return|
|z_j z_i, i<j|(0,m-j+i+2,j-i-1)|n-1; alternate via chain,u,w,v; omit b|
|z_i z_j, j>=i+2|(1,1,m+i-j+1)|m+i-j+5<n; shortened return|
|w b or b w|single exception|treated below|

If both wb,bw occur, use the direct w->b and w->v->chain->u->b, return bw: theta(0,m+2,0), order n, outside the first two types. All other rows already give order<n. Exhaustion by tails: u nonarcs v,z_j; w nonarcs u,b,z_j; b nonarcs u,w,z_j; v nonarcs u,w,b,z_j(j>=2); z_i nonarcs w,b,v,u(i<m), all earlier z_j and later nonsuccessors. This covers every ordered distinct pair.

At n=5,m=1 the full missing lists are u:{v,z}; w:{u,b,z}; b:{u,w,z}; v:{u,w,b}; z:{w,b,v}. The four reverse-short-branch arcs wu,vw,bu,vb give (0,2,0) on four vertices; vu gives (1,1,0); uv gives (0,1,1); wz,bz,zw,zb give (0,1,1); uz gives (0,2,0); zv gives (0,2,0). wb,bw are the only exceptions. All z_i u(i<m), forward-skip, backward-pair and vz_j(j>=2) ranges are empty. Both exceptions give (0,3,0) on five vertices. This is the exhaustive hand boundary audit.

### Isomorphisms, not reversal invariance
Let H be the first model plus uz1. The first model plus zmu is isomorphic to H by mapping H's ordered labels
(w_H,u_H,v_H,z1_H,...,zm_H) -> (zm,w,u,v,z1,...,z_(m-1)).
The H arcs wv,wu,uv,vz1,chain,zmw,uz1 go respectively to zm->u,zm->w,w->u,u->v, v->z1->...->z_(m-1),z_(m-1)->zm,w->v; all and only the other graph's arcs. This map works at m=2.

For the second model plus wb, map H labels to (u,w,b,v,z1,...,zm), where H has m+1 chain vertices. Then H's branch arcs map to ub,uw,wb; its chain starts bv and continues v->z1->...->zm->u; its extra arc maps to wv. This is exact. The bw case follows by the automorphism swapping w,b of the original second theta. It also works for m=1. Thus all four single additions are genuinely isomorphic. No assertion that A_alpha of a reversed digraph has the same radius is used; that assertion would be unjustified because the degree diagonal uses outdegrees.

## Comparison of H with the fourth graph
In H, let L be the Perron radius. Set t=(L-alpha)/d and s=(L-2alpha)/d. The degree-one chain gives x_v=x_w/t^(n-2), x_z1=x_w/t^(n-3). Rows u,w give s*x_u=x_v+x_z1 and s*x_w=x_v+x_u. Substitute the former into the latter, multiply by t^(n-2), and cancel x_w>0:
(E) s^2*t^(n-2)=s+t+1.
This also proves s>0 directly. At this t the fourth-theta polynomial residual is
q(t)=s*t^(n-1)-t^2-1
=t*(s+t+1)/s-t^2-1
=t*(t+1)/s-(t^2-t+1).
For 1<t<2, s<=t yields q>=2t-t^2>0. For t>=2, n-2>=3 and E yield s^2<1: indeed s^2<=(s+t+1)/t^3<=(2t+1)/t^3<1, as t^3>2t+1 on [2,infinity) (value difference3 at 2 and increasing derivative3t^2-2). Hence s<1 and q>2t-1>0. This includes t=2 and n=5 without an omitted endpoint.
Finally q/t^(n-1)=(t-r)-t^(-(n-3))-t^(-(n-1)) is strictly increasing for t>1. Its unique root is the actual fourth-theta Perron parameter, so q>0 proves L is strictly greater. All proper supergraphs are strictly greater still. Combining all cases gives the stated four radii and unique minimizers.

## Assessment of defects
No fatal ordinary gap remains. Corrections are the source's backward-arc tuple, the explicit single-addition isomorphisms replacing vague reversal language, smaller-order cases h=3,4, and the precise restriction on strict maximum-row-sum bounds. These are paid here. They receive no separate discovery credit.
