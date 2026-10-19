# Exact all-prime hyperstar interface (author research; no theorem nomination)

This note concerns the unchanged T197O scope. It supplies finite types and an algebraic implication. Root protection is UNPROVED. The original source197 graph theorem cannot be cited to fill it.

## H1. The finite object

Fix an odd prime p, q=p^4, v=q^2+q+1, and e=p^2+p+1. Let P,L be the points and lines of PG(2,q). Let E be the disjoint union of p−1 copies of PG(2,p)'s point set, so |E|=(p−1)e=p^3−1. Set T=P disjoint-union E. Thus |T|=q^2+q+p^3 is divisible by p.

Partition T into p-element classes. For specificity put each extra letter in a class with p−1 distinct ordinary letters, then partition the remaining ordinary letters into p-element classes. This is possible because v>(p−1)|E| and the remainder is divisible by p.

Let m tend to infinity through integers m=1 mod p^2. A has m outer vertices for each L-line; B has m−1 for each line. Ordinary outgoing sockets of an outer vertex are the q+1 points on its line. Choose root x_A and give it all E. In each copy E_c and for each of its e lines ell, give exactly

    a_m=((q+1)m−1)/p^2 vertices of A,
    b_m=(q+1)(m−1)/p^2 vertices of B

the extra set D_(c,ell)=E_c minus ell (size p^2). Every other vertex has no extra sockets. These assigned vertex sets are disjoint, with the root excluded. Distribute each assignment across the v ordinary line classes as evenly as possible. The demand per line is at most (p−1)e ceil(a_m/v)+1 (and analogously for B). Its leading ratio to m is

    (p−1)e(q+1)/(p^2 v) < 1,

since (p−1)e=p^3−1 and (p^3−1)(q+1)<p^2(q^2+q+1) for q=p^4. Hence all assignments exist for sufficiently large m. Fix any B root.

For every socket t, the number of A vertices with t is N_A=(q+1)m; the B count is N_B=(q+1)(m−1). Indeed each extra point belongs to exactly p^2 line complements, and the A root contributes the extra one. Thus all p sockets of every class have exactly equal counts on each side.

For each socket class j, create N_Y centres on side Y. Independently match the N_Y vertices carrying each socket t in j bijectively to these centres. Every centre has exactly one incident edge of each socket in j; every outer vertex has its prescribed sockets once each. This is a bipartite incidence graph Gamma_Y, with degree p at centres. Multiple edges between one centre and one outer vertex are allowed initially. We can require their absence as part of the root-protection problem, but the algebra below also works with incidence multiplicity.

Let F be the free-group rose on T (one oriented generator for each socket, not a signed involution). An edge with socket t is oriented outer-to-centre and labelled t. Attach an abstract cone on every connected component of Gamma_A and Gamma_B to F by these edge-label maps. Let G be the fundamental group. This is a finite presentation. For every graph vertex z in a root component define g_z or h_z by a root-to-z path; cone relations make it independent of that path.

## H2. The exact missing statement

For every odd p, for some sufficiently large admissible m and some choices of the finite matching bijections above, every path in Gamma_B from its chosen outer root to another outer vertex has nonidentity image in G.

This ONE root-protection statement suffices for T197O. Asphericity, torsion-freeness, protection of all centres, and protection of the A root are not required. A proof may change the matching choices or grouping of the sockets, but changes of the prescribed finite types must reverify H3. No such existence proof is supplied here. The source197 topology theorem concerns ordinary edge matchings with fixed-point-free inverse labels; its hypothesis is not H2.

## H3. Proven algebraic implication H2 => T197O

Write A',B' for outer vertices in the root components, with root path labels g_x,h_y. In F_p[G] set

    a=sum_(x in A') g_x, b=sum_(x in A') g_x^(-1),
    c=sum_(y in B') h_y^(-1).

For every two outer vertices in A, their socket intersection has size 1 mod p, except the root with itself, whose size is 0 mod p. The same intersection is 1 mod p for A versus B. Ordinary lines intersect in one point or q+1 points, both 1 mod p. Extra intersections are 0, p^2−p or p^2, all 0 mod p, apart from the unique root self-intersection |E|=p^3−1=−1 mod p. This proves the assertions.

For each pair of centres z,w of the same socket class j on the two chosen sides, and for each t in j, let x_t,y_t be the outer endpoints. Since the edges point towards the centres,

    g_(x_t) t=g_z, h_(y_t) t=h_w,
    g_(x_t) h_(y_t)^(-1)=g_z h_w^(-1).

Consequently the p corresponding pair-vertices contribute the same group element. They form one p-uniform hyperedge, counting multiplicities if endpoints repeat. At a pair-vertex (x,y), the number of incident hyperedge occurrences is exactly |S_x intersection S_y|: every common socket picks its unique two centres and socket position. Componentwise the total degree is p times the number of hyperedges, hence zero modulo p. Product labels are constant on each component.

For A' times A', every component not containing (x_A,x_A) therefore has cardinality 0 mod p. The component containing it has cardinality 1 mod p, since only this pair-vertex has degree 0 rather than 1. Its product label is identity. Thus ab=1. For A' times B', every component has cardinality 0 mod p, so ac=0. Under H2 only the B root has path label identity, making the identity coefficient of c equal to one. Hence c!=0 and ba!=1. This proves the implication, not H2.

## H4. Why the literal source word-decay proof fails

Read source197 random.tex, Lemma word-decay. Its required sum of squared word weights decays exponentially. In the present incidence graph, a centre has p−1 deterministic nonbacktracking exits; a peripheral turn between two distinct ordinary sockets has asymptotic weight 1/(q+1). Let O be the ordinary sockets in all-ordinary classes. Its size is

    |O|=v−(p−1)|E|=q^2+q+p−p^4+p^3=p^8+p^3+p.

On states O, one centre turn followed by one peripheral turn has nonnegative squared-weight matrix whose every row sum is

    R=(p−1)(|O|−1)/(q+1)^2 > 1.

There are p−1 choices of centre exit and |O|−1 peripheral successors. Multiple intermediate choices add in matrix multiplication. The strict inequality holds for p>=3 because the numerator exceeds 2p^8 while (p^4+1)^2<2p^8. Thus the squared mass of these restricted two-step words grows at least as R^k. This excludes the unchanged source contraction proof, even before the extra sockets are included. Small O(1/m) changes from type rounding cannot repair a strict limiting gap above one.

This is an obstruction to a proof mechanism, not a counterexample to H2 or T197O. A possible useful next task is root protection with p-fold correlations organized as whole hyperedges, using an estimate different from squared ordinary word weights. Any such argument must handle repeated centres and shared p-stars rather than declaring their edge occurrences independent.
