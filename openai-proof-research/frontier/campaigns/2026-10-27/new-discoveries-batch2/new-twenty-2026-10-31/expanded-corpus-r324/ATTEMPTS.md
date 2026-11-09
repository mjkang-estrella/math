# Ordinary research, zero credit

No computation, enumeration, CAS, solver, Lean, or execution handoff was used. These are handwritten arguments. None is represented as a new accepted solution. Source bodies are retained locally with URL/time/byte/hash receipts. Literature, journal/correction and all-citing-body qualification remains incomplete.

## 367681: exact endpoint, two identifications, and a complete counting route

Read Chen–Li–Yao 2503.19621 versions 1, 2 and 3 at the definitions and concluding conjecture (4.1 in v1/v2, 4.2 in v3), plus the Schubert-polytope discussion. The abstract history dates v1 25 March 2025, v2 31 March 2025, v3 9 October 2025. The same problematic identification persists in the latest version. Read McGinnis 2303.04113v2 introduction's explicit panhandle base polytope, Section 3 coefficient-extraction argument preceding Theorem 3.1, Theorem 3.1, and ensuing specialization. Only selected portions of the much longer coefficient proof were read; no all-companion audit is claimed.

Let N=a+b, n=N+2. The source defines SM(S) by bases T={t_1<...<t_k} with t_i<=s_i. For r(S)=(1,1,a,b), S={2,a+3,...,a+b+2}. The bases are exactly the (b+1)-subsets meeting {1,2}: the first bound requires this, and every subsequent bound follows from room for the remaining elements. Its polytope is

P={x in [0,1]^(N+2): sum x=b+1, x_1+x_2>=1}.

Here is an independent vertex justification so the box bounds need not be inferred from an incomplete rendered formula. Intersect the unit box with these two constraints. At a vertex where the pair inequality is inactive there can be at most one fractional coordinate, and the integral total forces it to be integral. When the pair inequality is active, each of the two blocks has an integral total. A block with two fractional coordinates admits a small opposite perturbation preserving all constraints; a block with exactly one fractional coordinate contradicts its integral total. Thus every vertex is a zero-one vector, precisely a stated basis. This proves the convex-hull bridge.

For an integer t>=0, set u=x_1+x_2-t for lattice points in tP. Then 0<=u<=t. For each such u there are t-u+1 ordered pairs (x_1,x_2) in [0,t]^2 with sum t+u. The other N coordinates have sum bt-u. Consequently the lattice count is

sum_{z in Z} (t+1-z_0), where Z={z in {0,...,t}^(N+1): sum z=bt}.

Write E=|Z|=i(U_{b,N+1},t). Permuting the N+1 coordinates is a bijection of Z. Therefore all coordinate sums S_j=sum_{z in Z}z_j are equal and (N+1)S_0=bt E. It follows exactly that

|tP intersect Z^(N+2)|=(1+(a+1)t/(a+b+1))i(U_{b,a+b+1},t).

This proves the second equality in the literal record, for every a,b>0 and every integral dilation, and hence the polynomial identity. It is not a proof of the entire literal chain.

Indeed the source also explicitly identifies Pan_{b+1,a+b,a+b+2} with r(S)=(a,b,1,1). McGinnis defines its polytope by sum x=b+1 and x_{N+1}+x_{N+2}<=1. At t=1, for a=1,b=2, bases either use no element of the last pair (one choice) or exactly one (2*3 choices), giving 7. By contrast P has all 3-subsets of five elements except {3,4,5}, giving 9. RHS=(1+2/4)*binom(4,2)=9. This is an exact literal discrepancy with the first equality, not a solution of an intended corrected problem.

The same full counting method also diagnoses the correction: merging the two last coordinates of the genuine Pan polytope gives Z'={z in {0,...,t}^(N+1): sum z=(b+1)t}, each with z_0+1 preimages. Coordinate symmetry gives i(Pan,t)=(1+(b+1)t/(N+1))i(U_{b+1,N+1},t). For r(S)=(1,1,a,b), complementary coordinates and reversal yield instead Pan_{a+1,N,N+2}; their Ehrhart polynomials agree because x -> 1-x is an integral affine bijection on dilates. This completes the identification/classical bridge rather than declaring ease alone an exclusion. The older companion's coefficient-extraction body already supplies the split-pair counting framework: each block total j is weighted by its number of weak compositions, j+1 for the size-two block. Applying coordinate symmetry to its all-unit merged hypersimplex yields the displayed factor directly. The literal refutation is a parameter/identification correction; the repaired formula is a complete classical/source bridge. Both earn zero discovery credit under the task. No CANDIDATE or Pi plan.

## 367511: lifting perfect divisibility across an anticomplete edge

Read the entire short source 2503.10206v1 body, including Definition 2.1, proofs of Theorems 2.1 and 2.2, corollaries, and Conjecture 3.2. Definition: D_1 is perfection; D_j for j>1 means every induced subgraph with an edge has a partition A,B with omega(A)<omega(total) and D_{j-1}(B). These are hereditary properties. Disjoint union with an isolated vertex preserves D_j (base case perfection; induct on j, assigning the isolate to B and using a partition of the nontrivial component; repeat in each induced graph). This validates the isolated-vertex step of the source proof.

Fix an arbitrary H and k>2 and assume all H-free graphs have D_{k-2}. Let G be (H disjoint-union K2)-free. For every edge uv, the common antineighborhood C consists of vertices other than u,v adjacent to neither. G[C] is H-free, since otherwise that copy together with uv is a forbidden induced disjoint union. Thus D_{k-2}(C). This is a full valid local implication, not the requested global conclusion.

First attempted extension of Theorem 2.2: choose u and use A=N(u), B=V\N(u). A has clique number <=omega(G)-1, so induction on clique number can handle A. To conclude D_k(G), however, one needs D_{k-1}(B). Inside B, choosing a vertex v nonadjacent to u does not give an H-free common antineighborhood: uv is not an edge and cannot certify the forbidden K2. Thus the edge hypothesis does not produce the needed one-vertex recursion.

Second route: choose an actual edge uv and divide vertices into N(u), N(v)\N(u), and C, assigning u,v consistently. Each neighborhood separately has clique number strictly below omega(G); C has D_{k-2}. One might combine the first two neighborhoods into A and put C plus endpoints into B. But omega(N(u) union N(v)) can equal omega(G). The four-vertex clique example already shows the issue: an edge uv has its two other vertices in both neighborhoods, and u and v occur in opposite neighborhoods, so their union is the entire K4. Keeping just N(u) as A leaves in B vertices adjacent to v but not u, whose maximum cliques need not lose one relative to B. Neither local bound supplies a D_{k-1} partition of every induced B.

Third route: take a vertex-minimal counterexample, so every proper induced subgraph has D_k. A witnessing failure then says every D_{k-1} induced set misses some maximum clique of G. The edge-antineighborhood lemma controls C only, and gives no reason that C can be extended by a clique transversal to a D_{k-1} set. One cannot replace this by the source's chromatic binomial bound: a coloring inequality supplies no recursive partition of the required hereditary kind. The precise missing lemma is a partition/extension theorem turning the H-free common antineighborhoods of edges into a D_{k-1} transversal of all maximum cliques, uniformly in every induced subgraph. No such theorem has been proved here. No witness contradicting the literal universal statement was found or claimed. Hold, zero credit. Version/journal/citing coverage remains incomplete.

## 368306: transitivity versus actual game strategies

Read v1 and v2 definitions, Conjecture 6, the strategy-stealing/Proposition 5 discussion, and the complete local proof of Proposition 5 and its clique consequence. Latest abstract history: v1 6 May 2025, v2 28 October 2025. The source defines the score as the difference a-b of the final red and blue clique numbers under optimal play; Proposition 1 proves its optimal value belongs to {0,1}. Alice wins if this value is 1; Bob wins if it is 0. A binary win predicate on arbitrary terminal positions must not replace this numerical score definition. Edges are alternately colored, Alice red and Bob blue.

First full subcase route: if G is triangle-free and has at least two edges, Alice cannot build a clique of order three. Bob gets an edge on his first move, so his blue clique has order at least two, and hence he wins regardless of subsequent moves. This completely covers edge-transitive triangle-free graphs with >=2 edges, but no graphs with triangles. A one-edge graph with extra isolated vertices would violate the literal exclusion of only K2, yet is simply the same K2 game with irrelevant isolated vertices: a domain correction, excluded from discovery credit. No such candidate is offered.

Second route: if G has an involutive automorphism tau acting without fixed edges, Bob can reply to Alice's edge e with tau(e). Before each Alice move the colored sets are interchanged by tau; uncolored edges occur in pairs, so the reply is legal. At termination tau carries red cliques bijectively to blue cliques, giving equal clique numbers. This is a complete pairing proof for graphs with that extra symmetry, but edge-transitivity alone does not assert such an involution. In particular one cannot choose an automorphism taking each fresh edge to some unused edge independently and preserve a single isomorphism of the accumulated colors. It is the accumulated state, not the initial edge orbit, that governs legality.

Third route: try strategy stealing after Alice's opening edge uv, transferring an optimal strategy on G-{u,v} and pairing ux with vx. The source's Proposition 5 proof explicitly works on a complete graph, with both ux and vx available for every remaining x and a controlled residual clique. General edge-transitivity does not imply adjacent endpoints have equal outside neighborhoods. In C5, an edge's endpoints each have an outside neighbor the other does not; although C5 is already covered by triangle-freeness, it rigorously invalidates that proposed general pairing rule. Thus the complete-graph proof cannot be used as a universal transitivity proof.

A disproof on the intended nondegenerate domain needs a graph with triangles and a full winning strategy against all Bob replies, plus an actual proof of edge transitivity. No finite game tree was computed and no stronger-statement refutation is substituted. A proof needs a replacement for the absent involution or a universal strategy theorem; even the contained family of complete graphs includes the source's unresolved Erdős conjecture. The precise gap is the general second-player strategy on edge-transitive graphs with triangles that lack a supplied fixed-edge-free involution. Park, zero credit, no Pi plan.

## Compact diagnostic routes outside the three sustained investigations

367336: m=0,n=2 gives the edgeless graph, necessarily extremal with beta_1=0, with no spanning K_{r,2-r} for 0<r<2. If empty bipartition parts are allowed, K_{0,2} makes the conclusion vacuous. This is a missing-domain/terminology correction, not a discovery. Source v1 Conjecture 3 and Example 33 caption/context read; no claim that this settles the intended dense extremal problem.

367709: the cached definition of T(n,m) compares an n by m matrix with its transpose using only row and column permutations, so for n!=m this cannot even preserve dimensions. Under that literal interpretation both sides are empty; when n=m they coincide. This tautological correction cannot settle the intended plethysm inequality. Source definition review incomplete; no solution claimed.

368034: the source introduction explicitly says Kim–Roush disproved the unrestricted conjecture, while its actual new theorem assumes Gelfand–Kirillov dimension three. The literal record omitted that restriction. No classical counterexample is re-credited, and no source announcement is represented as our proof.

367308: latest source Conjecture 7.3 has a footnote announcing Bonin's proof. This is a material public-resolution warning; the actual Bonin proof body has not been read and no complete public reduction or final resolution status is asserted here.
