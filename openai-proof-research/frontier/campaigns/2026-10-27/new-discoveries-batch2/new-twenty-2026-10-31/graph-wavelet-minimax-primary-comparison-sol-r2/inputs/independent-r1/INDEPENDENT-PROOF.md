# Independent ordinary proof for MathDB 332073

Personal mathematical derivation, no mathematical execution. This establishes an ordinary refutation of the copied literal and original Conjecture 1. It does not establish novelty, final-source equivalence, acceptance, or credit.

## Endpoint and conventions

For a finite simple undirected unweighted graph G, let Delta have one row per unordered edge {i,j}, i<j, with -1 at i, +1 at j. For a real vector z, ||z||_0 is the number of nonzero coordinates. Put P={x in R^8: ||Delta x||_0<=1}. For every full orthonormal basis matrix Q let M(Q)=max_{x in P} ||Q^T x||_0. These maxima exist: P is nonempty, and the possible support sizes form a nonempty subset of the finite set {0,...,8}. The conjectural minimizer condition entails M(W)<=M(Q) for every such Q. It is enough to exhibit a legal even W and an orthonormal F with M(W)>M(F). No uniqueness interpretation of the source's informal equality to argmin is needed.

## Graph and the entire admissible class

Let A={1,2,3}, B={4,5,6,7,8}. The edges are all pairs within A, all pairs within B, and the single bridge {3,4}; there are no other edges, loops, multiplicities, directions or weights. The graph is connected: each clique is connected and the bridge joins them. It is simple and unweighted with symmetric adjacency and nonnegative weights. K=1 belongs to {0,...,N-1} for N=8 as required by Definition 9.

If x is not constant on one of these cliques, there are distinct u,v with x_u!=x_v. Each clique has at least three vertices, so choose w different from u,v in the same clique. The edge uv is inconsistent. If both uw and vw were consistent, equality through w would imply x_u=x_v. Thus at least one additional, distinct clique edge is inconsistent. Hence x cannot belong to P. Every x in P is therefore constant on both cliques. Conversely x=a 1_A+b 1_B has zero differences on all clique edges and only the bridge can have a nonzero difference. Its bridge difference is b-a. Thus

P={a 1_A+b 1_B: a,b in R},

with support of Delta exactly zero for a=b and exactly one otherwise. This includes zero, every global constant, a=0, b=0, arbitrary negative and arbitrary real values. No lower signal-support or nonzero-value restriction has been imposed. The source's optional suggestion to exclude sparse signals is not a standing premise of Definition 9 or Conjecture 1. Individual singleton indicators are not admissible here: each vertex has at least two neighbors; this also follows from the nonconstant-clique argument. Singleton local sets used below remain connected and are not claims about singleton-signal admissibility.

## A full competitor, including the constant column

For a clique with ordered vertices v_1,...,v_m, define the m-1 Helmert contrasts

h_j=(e_{v_1}+...+e_{v_j}-j e_{v_{j+1}})/sqrt(j(j+1)), 1<=j<m.

Each has sum zero and norm squared (j+j^2)/(j(j+1))=1. If j<k, h_k is constant on the entire support of h_j; their inner product is that constant times the zero coordinate sum of h_j, hence zero. The contrasts on different cliques have disjoint supports. Each is orthogonal to each clique indicator. There are two contrasts for A and four for B.

The two normalized indicators 1_A/sqrt3 and 1_B/sqrt5 are mutually orthogonal unit vectors. Together with the six contrasts they form eight orthonormal vectors, hence a basis of R^8: taking inner products proves linear independence, and eight independent vectors in dimension eight span. In this basis x=a1_A+b1_B has only coordinates sqrt3 a and sqrt5 b. Its worst support is exactly two (for example a=b=1).

To avoid even a hypothetical objection requiring a common global constant vector, use instead the following competitor F, which also lies in the literal unrestricted class:

m=1_V/sqrt8,
h=(5 1_A-3 1_B)/sqrt120,
and the same six Helmert contrasts.

The squared norm of h is (3*25+5*9)/120=1; its sum is 15-15=0, so h is orthogonal to m. Both are orthogonal to all six contrasts, and m has norm one. Thus F is a complete orthonormal basis with the constant column mandatory if desired. For every admissible x its only potentially nonzero coordinates are

<m,x>=(3a+5b)/sqrt8,
<h,x>=15(a-b)/sqrt120.

For a=1,b=0 both are nonzero, so M(F)=2. For a=b nonzero only the mean survives, and for a=b=0 all coefficients vanish. Cancellation 3a+5b=0 causes no difficulty for the upper bound. This proves the claimed worst case for all real signals, not just positive coefficients or test signals.

Indeed the global minimax value equals two. For any full basis Q, support at most one means x lies in one of its eight coordinate lines. The affine family x_t=1_A+t1_B cannot meet any fixed line in more than one point: two different members are linearly independent, since their A coefficients are both one and their B coefficients differ. There are only finitely many lines but infinitely many real t, so some admissible x_t has support at least two. Hence M(Q)>=2 for every Q. The explicit F attains this lower bound. This argument uses no enumeration or computational test.

## Source-legal even hierarchy and its exact W

Use root children L={1,2,3,4}, R={5,6,7,8}; L children {1,2},{3,4}; R children {5,6},{7,8}; each pair then splits into its two singletons. Each split is disjoint, covers its parent, has equal positive cardinalities, and has connected children. L is connected via the K3 and bridge 3--4, R is a clique, {3,4} is precisely the bridge edge, and all other pairs are clique edges. Singletons are connected by the usual length-zero path convention. No empty child or division by zero is used. A stack schedule can process only nonsingletons while any remain, as required to reach these terminal leaves.

Algorithm 1 generates m and, at a split S=S1 disjoint-union S2, the contrast

sqrt(|S1||S2|/(|S1|+|S2|)) (1_{S1}/|S1|-1_{S2}/|S2|).

Consequently W has the following eight columns, in this chosen order:

m;
r=(1,1,1,1,-1,-1,-1,-1)/sqrt8;
l=(1,1,-1,-1,0,0,0,0)/2;
t=(0,0,0,0,1,1,-1,-1)/2;
p12=(e1-e2)/sqrt2;
p34=(e3-e4)/sqrt2;
p56=(e5-e6)/sqrt2;
p78=(e7-e8)/sqrt2.

Every contrast sums to zero. The norms are one: r has eight entries of square 1/8, l and t have four of square 1/4, and pairs have two of square 1/2. Two contrasts with disjoint support are orthogonal. If supports are nested, the larger contrast is constant on the support of the smaller, whose sum is zero, so they are orthogonal. They are all orthogonal to m. Thus these eight vectors form a full orthonormal basis independently of reliance on Theorem 8. Column order or sign changes do not affect support.

Definition 10, p15, requires connected local sets. Algorithm 1, p17, specifies a partition into two disjoint connected sets, not minimization of an edge-cut objective. Page16 introduces equation (7) as an ideal normalized-cut objective, explicitly replaces it by relaxed methods, and explicitly allows other graph partition algorithms. Corollary 2 and Conjecture 1 stipulate even partitions. This hierarchy satisfies those actual conditions. It is not claimed to minimize (7), or to be the deterministic output of a particular spectral eigensolver. Such an additional requirement is absent from the conjecture. Moreover the next paragraph below proves failure for every perfectly even hierarchy, so an unspecified even-partition tie-break cannot repair it.

## Exact support comparison

For x=a1_A+b1_B the W coordinates, in the displayed order, are

((3a+5b)/sqrt8, 3(a-b)/sqrt8, (a-b)/2, 0, 0, (a-b)/sqrt2, 0, 0).

These follow by summing the listed entries against the three A values and five B values. In particular x=1_A has exactly the four nonzero coefficients 3/sqrt8,3/sqrt8,1/2,1/sqrt2. All square-root denominators are positive, so none vanishes. The coefficient Euclidean norm squared is 9/8+9/8+1/4+1/2=3=||1_A||_2^2. For general x the squared norm is

((3a+5b)^2+9(a-b)^2)/8+(a-b)^2/4+(a-b)^2/2=3a^2+5b^2,

consistent with orthonormality. The formula proves M(W)<=4 for every admissible real vector and the witness proves equality. Therefore

M(W)=4>2=M(F)=min_Q M(Q).

In particular there exists an orthonormal F with strictly smaller worst-case support, so W is not in the argmin. This is a strict actual comparison, not comparison of two upper bounds. It negates the universal minimax claim on a connected simple unweighted graph with allowed K.

## Robustness to all perfectly even choices

For any perfectly even hierarchy on these eight vertices, consider x=1_A. Its global mean coefficient is 3/sqrt8, nonzero. At the 4|4 root, if q of the three A vertices lie on one side, the contrast coefficient is (2q-3)/sqrt8; an integer q cannot make it zero. At least one root child is mixed between A and B, since a homogeneous 4-set cannot contain all three A vertices and root children cover them. The restriction of x to this mixed child is nonconstant. The descendant contrasts in that child, together with its normalized indicator, form its full orthonormal coordinate space by the same nested-support proof. If all descendant coefficients vanished, the restriction would be constant, contradiction. At least one additional contrast coefficient is nonzero. Thus every perfectly even W has M(W)>=3>2. No computational root-split enumeration or optimizer assumption is involved.

## Mean-zero and source-bound objections

The literal source uses full N-column bases on R^N, with the mean explicitly initialized; it does not optimize only over N-1 zero-mean columns or impose x perpendicular to constants. Those would be different statements. Even under that alternative problem this mechanism survives: in P intersect 1_V-perp, choose a=5,b=-3. The admissible subspace is the line spanned by h, so F's zero-mean part has worst support one. The three nonconstant W coefficients displayed above are all nonzero, with mean zero, so its zero-mean part has worst support three. This is supporting robustness, not another credited outcome.

Theorem 9 and Corollary 2 are not proof inputs. Their literal full-basis bounds already fail on any nonzero global constant, since Delta x=0 while the mean coefficient is nonzero. Their printed activation argument cannot pay that missing mean term. Our explicit coefficient proof neither assumes their truth nor uses this bound defect as the minimax refutation. Theorem 8's statement and entire proof were independently read; its orthonormality mechanism is reproved above, avoiding printed normalization typographical issues.
