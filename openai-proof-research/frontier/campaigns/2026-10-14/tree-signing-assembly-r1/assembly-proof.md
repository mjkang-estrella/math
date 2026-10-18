# Conditional heavy-light assembly for Euclidean tree signing

Myeongjin Kang, no affiliation. Original prose CC BY4.0. Author-side conditional support for the structural r44 family097 investigation, not independent review, a separate result nomination, or an acceptance. The chain law below is an explicit hypothesis, not proved in this note.

## Hypothesis and conclusion

Fix constants A,B>=0. Assume that for every d>=1 and every finite sequence v_1,...,v_N in the Euclidean UNIT BALL of R^d there is ONE law on sign vectors epsilon in {−1,1}^N such that:

1. With probability1, simultaneously for all0<=j<=N, the prefix S_j=sum_(i<=j) epsilon_i v_i satisfies ||S_j||_2<=A sqrt(d).
2. For each fixed j and every u in R^d,

       E exp(<u,S_j>) <= exp(B^2 ||u||_2^2/2).                 (H)

The law may be taken centrally symmetric under epsilon -> −epsilon. The assembly only needs the centered marginal estimate(H); symmetry is useful for deriving that estimate from a symmetric tail or psi2 formulation. It does not require independent signs, or independent prefixes, INSIDE a chain. The constants are uniform in d,N and the input sequence. Separate distributions selected for separate prefixes do not suffice.

Let T be a nonempty finite rooted tree, with L leaves, and give each vertex v a vector x_v in the Euclidean unit ball of R^d. Paths include both the root label and the final vertex label. Under(H), one signing of the vertices satisfies, for L>=2 and d>=1,

    max_v ||sum_(u on [root,v]) epsilon_u x_u||_2
      <= A sqrt(d)
          +2B sqrt(2 floor(log_2 L)[d log5+log(2L)]).         (1)

For L=1 the bound is A sqrt(d). In particular(1) is

    O(A sqrt(d)+B sqrt(log(1+L)[d+log(1+L)])).               (2)

Only L starting states, not all vertices or all prefixes, enter the probabilistic union bound. Combining with the separately verified unary-chain argument below yields

    O((A+B) sqrt(d log(1+L)))                              (3)

for all finite rooted trees, provided the same chain-law hypothesis holds. The alternate argument itself requires only deterministic O(sqrt(d)) sequence signing, which is already supplied by the pinned family097 theorem.

## Conversion from the primary two-sided tail convention

Suppose instead the chain-law construction supplies, for each fixed prefix and unit theta,

    P(|<theta,S_j>|>=t)<=2 exp(-t^2/(2s^2)),    t>=0.

First symmetrize the WHOLE signing law by multiplying all its signs by one independent uniform sign. Its hard-good support is preserved, as are all absolute-value tail bounds; every prefix marginal becomes symmetric and centered. This uses one symmetrization for the whole chain, not unrelated signs for its prefixes.

For the resulting symmetric scalar X=<theta,S_j> and k>=1, integrating the tail gives

    E X^(2k)<=2(2s^2)^k k!.

Since (2k)!>=2^k(k!)^2, monotone convergence in the cosh series implies

    E exp(lambda X)=E cosh(lambda X)
       <=1+2 sum_(k>=1) (s^2 lambda^2)^k/k!
       =2 exp(s^2 lambda^2)-1
       <=exp(2s^2 lambda^2).

Thus(H) holds with B=2s, after scaling theta to an arbitrary u. Any larger absolute choice, such as B=sqrt(8)s used by the structural author's note, is also sufficient. This conversion does not condition on the hard-good event: the SAME law must already have hard-good support and the stated tails. Conditioning a different subgaussian law without a quantitative argument would not establish the hypothesis.

## Heavy chains and exact counting

For each vertex v let ell(v) be the number of descendant leaves, counting v when v is a leaf. At every nonleaf select a child of maximum ell as the heavy child, with a fixed deterministic tie-breaking rule. All other child edges are light. The maximal connected paths of heavy edges partition the vertices into chains. Each chain starts either at the root or at a light child, and terminates at a leaf: a nonleaf always has one heavy outgoing edge. Thus sending a chain to its last vertex is a bijection from chains to leaves. There are exactly L chains.

If w is a light child of v, another child has at least ell(w) leaves. Hence ell(w)<=ell(v)/2. Along all other descendant steps leaf count does not increase. Therefore a root path has at most floor(log_2 L) light edges. In particular a chain head has at most this many ancestor chains before its own chain.

For each maximal heavy chain, in root-to-leaf order, sample a signing from the law in the hypothesis. Make these finitely many chain samples mutually independent. This defines one joint law on all vertex signs; independence between different chain samples does not assert independence within a sample.

## Starting states use internal prefixes

For a chain C with head h, define Z_C as the signed sum over the strict ancestors of h. If h is the root, Z_C=0. Otherwise list the preceding heavy chains met on the root-to-h path as C_1,...,C_k. The path exits C_a at the parent of the next light child. Its intersection with C_a is a fixed initial segment, and that segment can end strictly BEFORE C_a's last vertex. Denote its signed sum by Y_a. The tree, labels and deterministic heavy choices fix this prefix independently of all random signs. We have exactly

    Z_C=Y_1+...+Y_k,    k<=K:=floor(log_2 L).                (4)

Each Y_a satisfies(H), and these random vectors are independent because their chains are distinct. Multiplying their moment-generating functions gives

    E exp(<u,Z_C>) <= exp(k B^2 ||u||_2^2/2)
                       <= exp(K B^2 ||u||_2^2/2).          (5)

Different starting states Z_C generally share chain samples and need NOT be independent. A union bound below needs no such independence. Replacing an internal Y_a by its terminal-chain sum would be an incorrect identity; nothing here makes that replacement.

## The finite net estimate and a positive-probability event

For d>=1 choose a Euclidean1/2-net N of the unit sphere with cardinality<=5^d. A maximal1/2-separated set has this cardinality by disjoint radius1/4 balls inside the radius5/4 ball, and maximality makes it a net. For every z in R^d,

    ||z||_2 <=2 max_(u in N) <u,z>.

Indeed approximate z/||z|| by a net point and use the triangle inequality; z=0 is immediate. For B>0,K>0, Chernoff's bound applied to(5) gives

    P(<u,Z_C> > a) <=exp(-a^2/(2KB^2))

for any unit u. Set

    a=B sqrt(2K[d log5+log(2L)]).

A union bound over at most L*5^d pairs(C,u) shows

    P(max_C ||Z_C||_2>2a)<=1/2.                            (6)

The simultaneous hard prefix bounds on every chain hold on an event of probability1: the tree has finitely many chains, and each law has that property. Intersecting with(6) gives positive probability that both requirements hold. For any realization in this intersection and any v in chain C,

    sum_(u on [root,v]) epsilon_u x_u
       = Z_C + (the prefix of C ending at v).

The triangle inequality gives(1), simultaneously for ALL vertices, regardless of the lengths of the heavy chains. If B=0, (H) forces every one-dimensional marginal, and hence every fixed prefix, to be zero almost surely; then all starting states are zero and only the hard bound is needed. If K=0, L=1 and the unique chain already covers the entire tree. These cases do not divide by B or K.

## The verified alternate: unary-chain compression

This argument uses a DIFFERENT chain partition. A unary chain starts at the root or at a child of a branching vertex, follows the unique child while there is exactly one, and stops at the first leaf or branching vertex. Every branching vertex belongs to the END of its incoming chain. If b is the number of vertices having at least two children, this partition has

    m=L+b<=2L−1                                            (7)

chains. For example, each chain corresponds to exactly one leaf or branching endpoint. The elementary identity sum_(branch vertices)(outdegree−1)=L−1 gives b<=L−1.

Choose on each unary chain a deterministic signing whose every prefix has norm<=A sqrt(d); one can choose any signing in the probability-one set of the hypothesis. Alternatively use the pinned source097 deterministic signed-prefix theorem with its absolute constant A_0. Let e_C be the terminal signed sum of chain C. Its norm is at most A sqrt(d).

Contract each unary chain to a node. The resulting rooted tree has m vertices labeled by w_C=e_C/(A sqrt(d)), of norm<=1. Assume for this normalization A>0,d>=1; if all endpoint vectors vanish choose any flips, and the zero-dimensional case is handled below. A=0 in the universal hypothesis for d>=1 is impossible when one uses a single nonzero unit vector; nevertheless any particular all-zero instance is trivial.

The primary input is Lemma4.1 of Bansal–Jiang–Meka–Singla–Sinha, Prefix Discrepancy, Smoothed Analysis, and Combinatorial Vector Balancing, arXiv2111.07049v1. Its symmetric-convex-body form says that if a centrally symmetric convex body K in R^d has standard Gaussian measure at least1−1/(2m), unit-ball labels on an m-node rooted tree can be signed so all root paths lie in C_0 K, for an absolute C_0. The proof in the read version gives C_0=5 for the symmetric bodies used here; only an absolute constant is needed.

For clarity, its operative mechanism is bottom-up intersection of K with symmetrized child bodies, losing at most1/(2m) Gaussian measure per node. Definition2.4 preserves symmetry; Lemma2.5 does not decrease measure under symmetrization by vectors of norm<=1/5 while the current body has measure>=1/2. Each recursive body is symmetric convex. A symmetric convex body of Gaussian measure>=1/2 contains (1/5)B_2^d: otherwise a separating supporting slab of half-width<1/5 would have Gaussian measure at most(2/5)/sqrt(2pi)<1/2. Thus the scaled root vector lies in its body, and signs can be chosen down the tree. This supplies the root step, including a zero root vector. We only use Euclidean balls, so no nonsymmetric-body assertion is required.

Let

    r_m=2 sqrt(2[d log5+log(2m)]).

The same1/2-net argument for a standard Gaussian g gives

    P(||g||_2>r_m)<=5^d exp(-r_m^2/8)=1/(2m).

Use K=r_m B_2^d in the lemma. For d>=2 it produces chain flips tau_C in {−1,1} such that every compressed root path has signed endpoint sum of norm<=5r_m A sqrt(d). For an original vertex v in unary chain C, its sum is the sum of COMPLETE endpoints of the strict ancestor chains, plus tau_C times one internal prefix of C. Those strict ancestors form a compressed root path (or the empty path). Hence

    max_v ||original signed path sum||_2
        <= A sqrt(d)(1+5r_m)
        = O(A[d+sqrt(d log(1+L))]).                         (8)

Flipping an entire chain preserves all of its internal prefix bounds. This is why the unary partition, whose exits are endpoints, is appropriate for(8). Heavy-chain exits are not endpoints and cannot be used in this deterministic compression argument without an extra justification.

The primary text states its tree lemma for d>=2. For d=1, a direct greedy signing on the ORIGINAL tree gives every path sum in[-1,1]: if the sum at a parent is s with |s|<=1 and the child's scalar label is x with |x|<=1, choose its sign so |s±x|=||s|-|x||<=1. Root initialization is immediate. Thus neither dimensional padding nor an unstated d=1 case of the primary lemma is needed.

## Combining the two signings, without a common-realization assumption

Put ell=log(1+L), so ell>=log2. If ell<=d, then K<=ell/log2 and d log5+log(2L)<=c(d+ell)<=c' d. Formula(1) gives O((A+B)sqrt(d ell)); the hard A sqrt(d) term is absorbed because ell is bounded below by log2. If ell>=d, (8) gives O(A sqrt(d ell)) because d<=sqrt(d ell). Choose the signing from the relevant regime. The two constructions need not produce the same signing or be coupled: the conclusion is existential and the case split depends only on d,L. This proves(3).

## Degenerate and normalization cases

- A nonempty finite rooted tree has L>=1. The root itself is a leaf when it is the sole vertex. The empty tree, if allowed, has no path constraints and any empty signing works; the formulas involving log L are not invoked.
- For d=0 every vector is zero and every path sum is zero. Choose all signs+1; no sphere net or chain law is used.
- Zero vectors are allowed by the UNIT-BALL formulation. Their signs may be arbitrary and their contributions vanish. The hard law and fixed-prefix estimate still concern the same sequence, including such indices.
- If a chain law were supplied only for vectors of norm exactly1, it would require a stated reduction. One may lift x to (x,sqrt(1−||x||^2)) in R^(d+1), apply the law there and project back. For d>=1 this changes A by at most sqrt2 and leaves the projected subgaussian parameter B unchanged. It preserves global sign symmetry. This reduction covers all unit-ball vectors, including zero vectors, but should not be silently omitted.
- L=1 uses one chain and no random starting-state estimate. Its O(A sqrt(d)) conclusion has no dependence on the number of vertices. Root labels are included once, in the first chain.

## Exact outstanding obligation and attribution

The whole-tree conclusion(3) is conditional on the single joint chain law(H) with the simultaneous hard prefix support bound. The pinned deterministic source alone does not supply uniform subgaussian marginals of a law supported on its hard-good signings. Establishing that joint law is the structural author's separate task. This note does not review or certify that task.

The parent specified the heavy-light mechanism and requested the internal-prefix and edge-case checks. The structural author identified the precise chain-law contract and the unary-compression primary reference. This note supplies the assembly details, explicit bounds, source-operation check for the alternate, and the case split. These are author-side contributions to one candidate, not independent gates or separately counted theorems.
