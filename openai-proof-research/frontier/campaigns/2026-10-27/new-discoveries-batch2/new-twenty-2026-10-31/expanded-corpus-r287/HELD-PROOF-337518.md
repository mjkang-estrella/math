# Held ordinary proof: graph evolution-algebra isomorphisms

Zero credit. Not source-qualified, not independently reviewed, not Lean checked. No execution authorized. This is a complete ordinary argument for the source's standing connected, simple, finite, real setting with at least two vertices. MathDB omits connectedness and the field; restoring these is a semantic gate, not a new discovery. The one-vertex random walk needs a separate explicit convention. Literature coverage is incomplete: the 2021 journal body, all current companion versions, and general natural-basis classification bodies have not all been read. A routine complete bridge to an existing classification would exclude this route. No CANDIDATE.md is nominated.

## Definitions and exact intended endpoint

For a connected simple graph G on a finite set V, |V| >= 2, let d_i > 0 be its degree and a_ij its symmetric adjacency matrix. On R^V define products
A: (xy)_k = sum_i a_ik x_i y_i;
B: (xy)_k = sum_i (a_ik/d_i) x_i y_i.
An algebra homomorphism is an R-linear, multiplicative map; associativity and a unit are not required. B is A_RW(G). Biregular means bipartite with constant degree on each side, as in the companion's lines 185–189; it does not merely mean having two degrees.

Claim: A and B are isomorphic iff G is regular or biregular. Every homomorphism in either direction is zero or invertible. Thus the source's second clause follows as well.

Source: arXiv:1710.10516v2, standing connectedness lines 107–112, real convention near the introduction, Conjecture 1 lines 635–637, sufficient construction Proposition 2.4 lines 642–653, monomial converse Proposition 2.5 lines 657–747, nonsingular Proposition 2.7 lines 854 onward. All line numbers refer to retained pdftotext -layout text, not original TeX. Literal chunk, line, and hashes are in literal-provenance.json. We accept no catalogue label as a proof.

## 1. Nonzero homomorphisms are invertible

For the target algebra define L(x)=sum_k x_k and <x,y>=L(xy). This is a positive definite real bilinear form: in A it is sum_i d_i x_i y_i, and in B it is sum_i x_i y_i. Write t_i=f(e_i). Since e_i e_j=0 for i != j, the vectors t_i are pairwise orthogonal for this form.

If t_i=0, applying f to e_i^2 gives sum_{j adjacent i} c_ij t_j=0, where each c_ij is positive (1 for A, 1/d_i for B). Taking the inner product with any t_j in this sum gives c_ij ||t_j||^2=0. Hence all neighbors also have zero image. Connectedness propagates this to all vertices. Thus a nonzero f has all t_i nonzero, so its |V| orthogonal rows are independent. Equal finite dimensions imply invertibility. The inverse is multiplicative by applying f to a product. This proves the full null-or-isomorphism statement without a nonsingularity assumption.

## 2. An isomorphism can mix only a twin class

Take f:A -> B invertible. In the standard coordinates of B its rows t_i are Euclidean orthogonal. Set r_i=||t_i||>0, R=diag(r_i), O=R^{-1}T. Then OO^t=O^tO=I. For each coordinate k put D_k=diag_i(a_ik/d_i). Orthogonality of products in the natural basis gives T D_k T^t diagonal, hence O D_k O^t=Lambda_k diagonal.

Multiply by O on the right to obtain O D_k=Lambda_k O. Thus if O_ij != 0, then a_jk/d_j=(Lambda_k)_ii for every k. Consequently any two indices in the support of a row have identical normalized adjacency rows. Their supports are the same nonempty neighbor set, so their degrees coincide and their adjacency rows coincide. They are twins. Each row t_i is supported on a single target twin class, denoted C(i). This is an explicit coordinate proof, with no invoked classification theorem.

## 3. Source and target twin classes correspond, with equal sizes

If C(i)=C(j)=C, then
f(e_i^2)=t_i^2=(r_i^2/d_C) 1_{N(C)},
f(e_j^2)=t_j^2=(r_j^2/d_C) 1_{N(C)}.
Invertibility gives e_i^2/r_i^2=e_j^2/r_j^2. These nonzero adjacency vectors have 0/1 entries. Thus their supports agree and r_i=r_j: i,j are source twins.

Conversely if i,j are source twins, then f(e_i^2)=f(e_j^2). The displayed positive multiples of nonzero neighbor indicators are equal. Hence N(C(i))=N(C(j)), so C(i)=C(j), and r_i=r_j. We obtain a bijection of source twin classes with target twin classes. The rows supported in a fixed target class are orthogonal and span its full coordinate subspace: all other rows are supported outside it and the total matrix is invertible. Their number therefore equals its size. Thus corresponding twin classes have equal cardinality. Write r_C for the common row norm in a source class C.

## 4. Quotient adjacency and degree are preserved

For source i in class C,
sum_{j adjacent i} t_j=(r_C^2/d_{C'}) 1_{N(C')}.
The projection of the left side onto a target class D' is zero if D is not adjacent to C; otherwise it is the sum of all rows indexed by D. This latter sum is nonzero, since those rows are independent (indeed orthogonal). The right side's projection is nonzero exactly when C' and D' are adjacent. Thus the bijection of classes preserves adjacency. Twin classes have no internal edges in a simple graph, and between distinct classes adjacency is all-or-nothing. Class sizes agree, so d_C=d_{C'}.

On an adjacent class D' the equation now reads
sum_{j in D} t_j=(r_C^2/d_C) 1_{D'}.
Square Euclidean norms on both sides. Orthogonality, constant row norm, and equal class sizes give
|D| r_D^2=|D'| (r_C^2/d_C)^2.
All constants are positive, so r_D=r_C^2/d_C. No assumption about the signs of individual entries of T is needed.

## 5. The graph is regular or biregular

All neighbors D of C have the same r_D. Also r_C=r_D^2/d_D for every such D, so they have the same degree d_D. Therefore any two vertices joined by an even walk have equal degree. In a connected bipartite graph each side is an even-walk class, yielding biregularity. If the graph has an odd cycle, insertion of that odd walk shows every two vertices are joined by an even walk, so the graph is regular.

Conversely if G is regular of degree d, f(e_i)=d e_i is an isomorphism A -> B. If the two bipartition degrees are d_1,d_2>0, take r_1=(d_1^2 d_2)^(1/3), r_2=(d_1 d_2^2)^(1/3), positive real cube roots. Then r_2=r_1^2/d_1 and r_1=r_2^2/d_2. The diagonal map f(e_i)=r_s e_i on side s is invertible and multiplicative on each basis pair, hence everywhere by bilinearity. This is the source's existing sufficient construction; no separate novelty is claimed for it.

## Failed shortcuts and substantive scope

Requiring every isomorphism to be monomial is unjustified for singular graphs: orthogonal changes inside twin blocks need not be permutation matrices. The proof uses support blocks instead. Inverting the adjacency matrix loses precisely the singular case. Squared coefficient positivity alone does not force individual off-diagonal coefficient products to vanish: signs can cancel. The row normalization and diagonal-intertwining identity resolve that issue.

For disconnected graphs the literal null-map assertion is false for a routine reason. On a disjoint union of non-isomorphic components one can project to a regular component and apply its scalar isomorphism, zeroing the others. For example K_3 disjoint union P_4 is neither regular nor bipartite, and f:A -> B equal to 2 times identity on K_3 and zero on P_4 is a nonzero homomorphism. No credit for repairing the corpus's missing connectedness premise.

## Dormant, bounded Pi plan, only if root later authorizes

No execution now. A first authorized task should formalize the finite matrix lemma in Sections 1–2 only, with a 2 CPU, 6 GiB address-space/RSS and CPU 120 s / wall 140 s envelope per job, and stop on the first failed semantic bridge. No solver/search is needed. Root must separately authorize any implementation and decide source fidelity and significance first.

Full Lean endpoint requires all of the following, none silently assumed:
1. A finite SimpleGraph V, connectedness, 2 <= Fintype.card V and degree positivity. Explicit R^V bilinear multiplications A and B; no associative Ring instance. Define multiplicative real linear equivalences and homomorphisms with the literal nonassociative meaning.
2. Basis expansion translating multiplicativity into every pairwise product equation, including i=j. Prove the coordinate-sum positive forms and row orthogonality; zero propagation along graph paths; invertibility and inverse multiplicativity.
3. Row normalization by strictly positive square roots; finite orthogonal-matrix transpose identities; diagonal-conjugation-to-intertwining lemma proved by matrix multiplication. Joint-support lemma must prove equality of all normalized adjacency rows, not use spectral proxies.
4. Twin Setoid, finite quotient, every row nonempty support, unique support class. Prove source/target class bijection and equal sizes via linear independence and spanning, then recover complete/empty interclass adjacency. Establish degree preservation as an exact finite-sum identity.
5. Project the basis-square equations to blocks, use orthogonality to compute squared norms of the row sums, and cancel the positive class cardinality to prove r_D=r_C^2/d_C.
6. Prove even-walk degree propagation, the bipartite/odd-cycle dichotomy, and equivalence to source biregularity; construct positive cube roots and the converse scaling maps.
7. The final theorem must quantify over all finite graphs satisfying the source standing hypotheses and both homomorphism directions, and separately state the nontriviality convention and mismatch with the bare MathDB wording. Audit the endpoint and every dependency with #print axioms; only propext, Classical.choice, Quot.sound. No sorry/admit/axiom/unsafe/native_decide.

Certificate size: a structural proof over arbitrary finite V, not a finite graph certificate. Tentatively 6–12 modest modules; this is a planning estimate, not a measured execution claim. Missing literature gates may terminate the route before implementation. No count increment.
