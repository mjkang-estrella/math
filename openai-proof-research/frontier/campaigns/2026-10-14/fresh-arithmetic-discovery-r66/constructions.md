# Source161: removing four-cycles from the pattern

Status: substantive construction attempt, unresolved; no theorem nomination. The working question is whether there exist a connected finite simple bipartite C4-free graph F and a finite simple host G with p(G)>0 and t(F,G)<p(G)^|E(F)|. Here t counts all homomorphisms and p(G)=2|E(G)|/|V(G)|². No degree bound, asymptotic girth assertion, injective-only replacement, or prescribed host is imposed. This is a question selected during exploration, not a retrospectively asserted successful scope freeze. No unified positive proof is assembled.

The source supplies H, a 35-vertex, 66-edge incidence graph of 22 triples on 13 points, and an untyped nonnegative kernel witnessing its deficit. Its proof is accepted as true at its stated interface. Two explicit finite operations were attempted below. Neither transports the deficit.

## 1. Finite voltage cover: graph compatibility succeeds

Number the 66 edges of H from 0 to 65 and orient each from the point part to the face part. Give edge e voltage w_e=2^e in Z/pZ, where p is any prime greater than 2^67. Replace v by vertices (v,t), t in Z/pZ; replace the oriented edge i→j by (i,t)→(j,t+w_e) for every t. This is a finite simple bipartite covering graph.

A four-cycle in the cover would project to a nonbacktracking closed walk of length four in H: a covering map is locally injective, so consecutive different edges cannot project to an immediate reversal. In a simple graph such a walk of length four is a four-cycle with four distinct edges. Its voltage is the alternating sum of four distinct powers of two. It is a nonzero integer, because the largest power exceeds the sum of all the smaller selected powers. Its absolute value is less than 2^66, so it is nonzero modulo p. Such a walk cannot close in the cover. Hence the cover is C4-free. Every connected component covers H: lifting paths from a vertex reaches a preimage of every base vertex, and path lifting gives bijections between its fibers. Select any component if connectedness is required.

Every lifted face still has three neighbors, but now two distinct faces share at most one point. This makes the incidence triples linear.

## 2. Why the native rank-layer model loses the negative term

The source's rank-layer lemma is stated for its original complex, not for arbitrary covers. We do NOT infer that the actual lifted matrix integral converges to the following model. The exact algebraic observation is conditional: if one tries the same independent-pair parity model on a linear triple system, it is identically one.

For any active incidence set and any fixed incidence signs, its model is

E_eta product over faces j and active point pairs {i,k} in j of
(1+c0 eta_{ik} xi_{ij} xi_{kj}),

where eta_{ik} are independent uniform signs. Linearity means each eta occurs in at most one factor. Averaging that variable gives one, independently of every incidence sign. Thus the whole expression is one. This applies separately to every matrix coordinate, and averaging any activation law still gives one.

By contrast, in the source every point pair lies in two faces. Averaging its eta multiplies the two factors and retains a four-corner sign monomial. The overlapping labels U_e and U_f, their seven-coordinate union, and their six-coordinate symmetric difference yield the negative off-diagonal overlap moment. Those are exactly the terms eliminated in the linear lift. The source's o(1) does not supply a signed remainder for a changed pattern; an o(1) remainder of unspecified sign would not prove or disprove a finite deficit anyway.

Thus the finite cover solves the graph problem but not the correlation problem. Extending the singular-tail estimate alone would at best give this neutral leading model, not the source's fixed negative gap.

## 3. Vertex splitting with long copying wires

A different construction replaces each old vertex v by one clone per incident edge. The clones are joined by a tree whose edges are subdivided into long even paths, so all clones of v remain in its original bipartition. Original incidence edges connect their corresponding clones. All these trees are disjoint. Contracting them recovers H. Choosing every subdivided tree edge sufficiently long makes every cycle long: a cycle cannot consist only of original incidence edges, since these form a matching on the clones, and it cannot lie in one tree. Thus it uses at least one long tree path. The graph remains finite, connected, simple, and bipartite.

For a typed model with uniform payloads in [N], the normalized equality kernel D_N(x,y)=N·1{x=y} pays the desired contraction exactly. If T is a tree on s clone/intermediate vertices and f_a are arbitrary functions attached to its vertices, then

E_(x_a) [product_{ab in T} D_N(x_a,x_b) product_a f_a(x_a)]
= E_x product_a f_a(x).

Indeed only the N constant assignments survive, each with weight N^(s−1) and probability N^(−s). Applying this separately to each old vertex's tree recovers the old typed partition function, including all its incident factors.

This is an exact typed identity. It does not prove an untyped deficit. A single graphon averages over all type maps, including those that repeatedly use one copying type pair. Introducing source-style thinning replaces a copying interaction by 1+t(D_N−1), and now nonempty terms can be supported on a proper cycle rather than on every edge of the new pattern.

## 4. Exact unwanted cycle terms

Let P be the averaging operator on functions on uniform [N]. The centered equality kernel A_N=D_N−1 represents I−P. It is selfadjoint, has zero row and column means, and has eigenvalues 1 with multiplicity N−1 and 0 with multiplicity one. Consequently, for every integer l≥3,

t(C_l,A_N)=Tr((I−P)^l)=N−1.

Every proper nonempty edge subset of a cycle is a forest with a leaf. Integrating that leaf kills its product of A_N factors. Hence the exact identity

t(C_l,1+t A_N)=1+(N−1)t^l

holds. In particular every even cycle supplies a positive correction. The wire kernel is nonnegative for 0≤t≤1. These are finite identities, not asymptotic estimates.

A part-preserving type assignment may send the two sides of a cycle to a single copying type pair. In the perturbation expansion, selecting the edges of that cycle and taking baseline 1 elsewhere produces such a positive term multiplied by positive type-prior/thinning factors. This does not prove it dominates every possible negative term. It proves that the source's all-or-nothing support assertion is unavailable: these proper-support terms exist.

The source pinning lemma compares Q(f)=sum of vertex scores plus the sum of pair scores over ALL incidences. Its use in the source depends on every nonempty term having a thinning factor on every incidence. A proper cycle term receives only that cycle's pair-score factors. The unique maximizer of the full Q is not a bound on these different scores. No assertion that large pinning parameter suppresses these terms is justified without a new estimate.

## 5. Exact and approximate copying cannot have arbitrarily cheap cycle moments

The obstruction is not confined to a poorly normalized delta. Suppose a kernel K on uniform [N] satisfies

E_(x,y) f(x) K(x,y) g(y)=E_x f(x)g(x)

for every two functions f,g. Choosing singleton indicators shows K(x,y)=N·1{x=y} entry by entry. Therefore any endpoint gadget required to copy the entire payload exactly has precisely the equality kernel and precisely the preceding cycle moments. This is an elementary characterization, not a new substantial result.

There is also a quantitative finite-dimensional version. Let T be a selfadjoint operator on mean-zero functions on a finite probability space. Suppose a d-dimensional subspace V satisfies ||Tf||_2≥a||f||_2 for all f in V, with a≥0. Then T² has at least d eigenvalues at least a². To prove this, if the span of its eigenvectors of eigenvalue at least a² had dimension below d, V would intersect its orthogonal complement nontrivially, contradicting the displayed lower bound (when a=0 the conclusion below is immediate). Thus, for every k≥1,

Tr(T^(2k))≥d a^(2k).

For a symmetric row-mean-one wire kernel K, take T to be the operator of K−1. Retaining d independent mean-zero modes with loss at most epsilon forces t(C_2k,K−1)≥d(1−epsilon)^(2k). This statement requires the lower bound on an entire subspace, not merely on a list of basis vectors. It does not establish that reproducing the source's one particular partition function requires copying all N−1 modes.

Long paths do not evade exact copying: the endpoint operator must still be I if it reproduces every payload test. Approximate copying could use a much smaller specially chosen subspace, or fail the selfadjoint interface, but neither compatibility construction is supplied here.

## 6. Remaining full obligation

Produce a finite nonnegative untyped kernel for a connected C4-free pattern with a strictly negative normalized density gap. A source-based copying approach must retain its required multi-incidence rank-layer correlations while controlling EVERY proper-support cycle and EVERY repeated type map. Full-state equality gives the exact positive terms above. The current source activation/pinning identity controls only all-incidence terms. A specialized copying interaction with a proved global expansion and error bound, or a different correlation geometry, remains missing. Neither native lifts nor typed contractions close the full question. No supporting obstruction is offered as a replacement nominee.
