# Leaf-sensitive Euclidean signing of finite rooted trees

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

**Author-side complete candidate, pending independent proof and contribution
review. No acceptance or campaign count is claimed.** All uses of pinned097
are stipulated source inputs; no upstream truth audit is performed.

## The full theorem

There is an absolute C<infinity such that for every d>=1, every finite
nonempty rooted tree T with L leaves, and every vertex labeling v_t in R^d
with ||v_t||_2<=1, one can choose signs epsilon_t in {-1,1} with

  max_{u in V(T)} ||sum_{t on [root,u]} epsilon_t v_t||_2
      <= C sqrt(d log(1+L)).                                (T)

Each path includes its root and endpoint. C is independent of all depths,
degrees, unary-chain lengths, dimension and number of vertices. Zeros and
repetitions are allowed. For d=0 or an empty tree the sums are zero. The claim
is existential and offline, with no efficient sampling/algorithmic or optimality
assertion. original-scope.txt fixes these exact quantifiers before the full
proof was assembled, after exploratory local-law calculations and the parent's
assembly suggestion. Its external SHA256 is
08338d40a730c126691accaaa60db530116b5df44393ca22d2c1663cc9099821.

The crucial ingredient is a law whose support satisfies a hard bound for ALL
prefixes, while EACH fixed prefix has dimension-free subgaussian marginals.
Existing online prefix-subgaussian laws alone do not give this support property.
We first prove that ingredient in full, then assemble the tree estimate.

## 1. Exact statement and source contract

There are absolute A,s<infinity with the following property. For every d>=1,
n>=0 and sequence v_1,...,v_n in the Euclidean unit ball of R^d, there is a
centrally symmetric probability law on {-1,1}^n such that

(a) every signing in its support satisfies max_t ||sum_{i<=t}epsilon_i v_i||<=A sqrt(d);
(b) for every FIXED t and every unit theta, the scalar theta dot
sum_{i<=t}epsilon_i v_i has tails at most 2 exp(-u^2/(2s^2)), u>=0.

The same law works for all t. This is not a claim of independence between
prefixes or of a conditional law after exposing earlier signs. No efficient
sampling algorithm is asserted. n=0 is the point mass on the empty signing.

Use the pinned097 assembly.tex propositions prop:adaptive and prop:filtered,
lemma lem:slab-energy, and brownian.tex lem:brownian-rate and
lem:gaussian-path-correlation as stipulated true. They are stronger inputs than
the final deterministic prefix theorem. Kappa=1/100 and delta=1/4 are fixed.
The source adaptive theorem selects one point by assigning distinct coordinates
q_i+epsilon_i, where q_i is any [-delta,delta]-valued function of prior assigned
coordinates, provided lambda_Q(K)<=kappa^2 tr Q for every positive diagonal Q.
The filtered body D has coordinate bounds B_0 and state bounds A_0 sqrt(d),
with lambda_Q(D)<=H_0 tr Q uniformly over length and every such Q.

## 2. Two elementary energy supplements

**Intersection.** For bounded open centrally symmetric convex D,E in the same
Euclidean space,

  lambda_Q(D intersection E) <= lambda_Q(D)+lambda_Q(E).

Indeed, for 0<a<1, impose Brownian path membership in the two CLOSED sets
closure(aD), closure(aE). They are contained in D,E respectively. Gaussian
path correlation bounds the simultaneous probability below by the product of
the closed-event probabilities, each at least its corresponding open-event
probability for aD,aE. Take the negative logarithmic survival rate, using the
source lemma only for OPEN sets D intersection E, aD, aE. This gives the bound
with right side a^{-2}(lambda_Q(D)+lambda_Q(E)); let a increase to1. All domains
contain0 and are bounded, open, convex. No equality of closed and open survival
rates is assumed.

**Gaussian body.** There is absolute H_G such that every bounded CLOSED
symmetric convex K with standard Gaussian measure >=1/3 satisfies

  lambda_Q(3 int K) <= H_G tr Q.

Set a=Phi^{-1}(2/3)>0. Every unit-direction support width of K is at least a:
otherwise K lies in a centered slab of Gaussian measure <1/3. The support
halfspace representation therefore gives a B_2 contained in K. Put
phi(x)=max(0,1-dist(x,K)/a) and g=phi sqrt(rho), where rho is standard Gaussian
density. The support lies in K+aB_2, contained in2K, which is compactly
contained in3 int K. Thus g belongs to H^1_0(3 int K), by compact-support
Lipschitz/Sobolev approximation. Its squared norm is at least1/3. Almost
everywhere |partial_j phi|<=1/a, and

  integral |partial_j g|^2
  <= 2 integral rho |partial_j phi|^2 + (1/2) integral rho x_j^2 phi^2
  <= 2/a^2+1/2.

Consequently H_G=6/a^2+3/2 suffices, uniformly in dimension and diagonal Q.
For an arbitrary possibly unbounded symmetric convex body of Gaussian measure
>=1/2, intersect its closure with a sufficiently large closed Euclidean ball
to obtain such a bounded K of measure >=1/3. A point in cK lies in c times the
original closed body. If the original body is open, first take an interior
homothetic shrink with measure >1/3, then truncate; the same absolute constants
apply. This handles the convex-body conventions in the cited minimax theorem.

## 3. A fixed finite set of good corrected coefficients

Choose absolute D_* large and 0<sigma<1/2 small enough that

  H_0/D_*^2 + pi^2 delta^{-2} sigma^2 <= kappa^2/2.

As in the source, b_i=sigma v_i,
eta_i=(1+sqrt(1-||b_i||^2))^{-1}, C_i=I-eta_i b_i b_i^T.
Let m=d+n, R_0 read the initial d coordinates, and
R_i x=C_i R_{i-1}x+b_i x_{d+i}. These maps satisfy R_i R_i^T=I_d.
Let x^0 zero the initial block, and m_i x=eta_i b_i^T R_{i-1}x^0.
The source telescoping identity gives ||M e_j||^2<=sigma^2 for every column
of the row matrix M. Hence

  K_0=(2D_* D) intersection { |m_i x|<delta for every i }

has lambda_Q(K_0)<=kappa^2 tr Q/2. Its state bound is
||R_i x||<2D_* A_0 sqrt(d). All these choices are fixed by the input sequence,
independent of the auxiliary Gaussian body below.

For each epsilon in {-1,1}^n, solve the triangular recursion with zero initial
block

  z_i=epsilon_i + eta_i b_i^T R_{i-1}(0,z).

The solution x(epsilon)=(0,z) is unique. Define the FINITE set
A_good={x(epsilon): x(epsilon) in K_0}. It is centrally symmetric, since the
recursion is linear in epsilon and K_0 is symmetric. It will be nonempty by
the following argument. Its definition is independent of all auxiliary bodies.

For any symmetric Gaussian-half body B in R^m, choose K contained in B as in
Section2, with Gaussian measure>=1/3. Choose absolute D_G with
H_G/D_G^2<=kappa^2/2 and set E=3D_G int K. The intersection lemma gives

  lambda_Q(K_0 intersection E)<=kappa^2 tr Q

for every positive diagonal Q. Apply source prop:adaptive to this intersection
with assigned coordinates d+1,...,d+n and prescribed shifts
clip_delta(m_i x_previous). The rows use only earlier assigned noise
coordinates. At the final x in K_0 intersection E, |m_i x|<delta, so clipping
was inactive at every step. Thus x=x(epsilon) belongs to A_good and also to
3D_G B. The exact cancellation is

  R_i x=(I-eta_i b_i b_i^T)R_{i-1}x
         +b_i(epsilon_i+eta_i b_i^T R_{i-1}x)
       =R_{i-1}x+epsilon_i b_i.

Since R_0x=0, R_i x=sigma sum_{j<=i}epsilon_j v_j.
We have proved that A_good meets cB for EVERY Gaussian-half symmetric convex
body B, with one absolute c=3D_G, in dimension m=d+n.

## 4. The primary minimax operation and the prefix law

Dadush–Garg–Lovett–Nikolov, Theory of Computing15(15),2019, Theorem1.2
(detailed as Theorem3.4 and its Section3 proof), states for every finite
T subset R^m that meeting a fixed dilation of every symmetric Gaussian-half
convex body is equivalent, up to an absolute constant, to supporting a
subgaussian law. The exact finite-set theorem and the complete operative
minimax direction were read in the primary PDF, extracted lines238–298 and
953–1075. The authors convexify normalized cosh tests, use compactness of the
finite probability simplex, and associate each test mixture to a Gaussian-half
convex level set. That distributional duality is credited to them, not claimed
as new here.

Apply it to A_good. Obtain a c_0-subgaussian X supported on A_good, c_0
absolute. Symmetrize its law under X->-X. This keeps its support and all
absolute scalar tail bounds and makes it centrally symmetric. The map
x(epsilon)->epsilon is one-to-one by the triangular recursion, so it induces
a centrally symmetric law on signings. Its entire support has the deterministic
prefix bound A=2D_* A_0/sigma. For each fixed i,

  sum_{j<=i}epsilon_j v_j = sigma^{-1} R_i X.

Since R_iR_i^T=I, ||R_i^T theta||=1 for unit theta. Thus each fixed prefix is
s=c_0/sigma-subgaussian. This proves the stated law without a factor depending
on d or n. Importantly the law gives ALL fixed-prefix marginals, not only the
terminal sum. It does not give one subgaussian bound for the maximum over n.

For use in sums of independently sampled chains, symmetry and the tail bound
imply the scalar moment generating function estimate

  E exp(lambda Z) <= exp(4 s^2 lambda^2).

Indeed E Z^{2k}<=2(2s^2)^k k! follows by tail integration; then (2k)!>=(k!)^2
bounds E cosh(lambda Z) by 2 exp(2s^2 lambda^2)-1, which is at most
exp(4s^2 lambda^2). Symmetry identifies the cosh expectation with the exponential
expectation. Independent fixed-prefix contributions therefore add variances.


## 5. Heavy-light assembly

Write A,s for the absolute local constants above and B=sqrt(8)s, so every
fixed chain prefix S satisfies E exp(<u,S>)<=exp(B^2||u||^2/2). The local law
is one law per entire chain; different prefix-specific laws would not suffice.

For each vertex t let ell(t) be its descendant leaf count. At every nonleaf
choose a child of maximum leaf count as heavy, breaking ties deterministically.
Maximal heavy paths partition the vertices into chains. Each chain ends at
one leaf and every leaf ends one chain, so there are exactly L chains. A light
child has at most half its parent's leaf count. Every root path therefore uses
at most K=floor(log_2 L) light edges.

Sample the local laws independently for these finitely many heavy chains.
For a chain C with head h let Z_C be the sum at the strict ancestors of h.
The root chain has Z_C=0. Otherwise the root-to-h path intersects each preceding
heavy chain in a FIXED INTERNAL PREFIX, which may end before that chain's
terminal vertex. The prefix is fixed by the tree, independently of signs.
There are at most K such ancestor chains. Their contributions Y_a are independent
across chains, and each has the local MGF bound. Hence

  E exp(<u,Z_C>)<=exp(K B^2||u||^2/2).                     (5.1)

Different Z_C need not be independent. A union bound does not require that.
For d>=1 a1/2-net N of the unit sphere has size<=5^d, by disjoint radius1/4
balls inside the radius5/4 ball. It satisfies ||z||<=2 max_{u in N}<u,z>.
Chernoff applied to(5.1), followed by a union bound over L*5^d pairs(C,u), gives
with probability at least1/2

  max_C ||Z_C|| <= 2B sqrt(2K[d log5+log(2L)]).             (5.2)

Each chain's simultaneous hard prefix bound holds almost surely. Thus some
sample satisfies both(5.2) and all hard bounds. For any original vertex v in
chain C, its root-path sum is Z_C plus the prefix of C ending at v. Therefore

  max_v ||path sum|| <= A sqrt(d)
      +2B sqrt(2K[d log5+log(2L)])
    =O(sqrt(d log(1+L))+log(1+L)).                         (5.3)

For L=1 use the sole chain directly; no union estimate dividing by K is used.
This argument never assumes conditional shift control given an inherited sum.
It uses only fixed-prefix marginals on independent whole-chain samples.

## 6. The complementary regime from unary-chain compression

Use a different partition: a unary chain starts at the root or at a child of
a branching vertex, follows unique children, and stops at a leaf or branching
vertex. Each branching vertex is included at the END of its incoming chain.
If b is the number of branching vertices then there are m=L+b<=2L-1 chains,
since sum_{branch vertices}(outdegree-1)=L-1. The chains are disjoint and their
contraction is a rooted m-vertex tree. All exits from these chains are endpoints.

The source097 deterministic signing theorem supplies a signing on each chain
whose every prefix has norm<=A_0' sqrt(d), with A_0' absolute. Let e_C be each
chain's terminal sum. Normalize by A_0' sqrt(d). The normalized e_C label the
compressed tree by unit-ball vectors.

Bansal–Jiang–Meka–Singla–Sinha, arXiv2111.07049v1 Lemma4.1 (ITCS2022 Lemma21)
supplies an absolute C_0: if a symmetric convex K in R^d has Gaussian measure
>=1-1/(2m), these m node labels have one signing with all root-path sums in
C_0 K. We use d>=2 here. Its actual proof constructs child target bodies
backwards by intersection and symmetrization; their measure loss is charged
once per node. This is a paid primary operation. Symmetry ensures the root
step: every symmetric convex Gaussian-half body contains a fixed Euclidean
ball, so the sufficiently scaled root vector is admissible.

The same sphere-net argument applied to a standard Gaussian shows that the
Euclidean ball of radius r=2 sqrt(2[d log5+log(2m)]) has measure>=1-1/(2m).
Thus there are chain flips tau_C with every compressed root sum of norm at most
C_0 r A_0' sqrt(d). Multiply ALL original signs in each unary chain by its
flip. This keeps its hard internal-prefix bound. The root-to-v sum in the
original tree is a compressed path of COMPLETE STRICT ANCESTOR endpoints,
plus one internal prefix. Consequently

  max_v ||path sum|| <= A_0' sqrt(d)(1+C_0 r)
       =O(d+sqrt(d log(1+L))).                            (6.1)

For d=1 a greedy choice on the original tree gives norm<=1 everywhere: for
parent sum |a|<=1 and child label |x|<=1 choose the sign with
|a+epsilon x|=||a|-|x||<=1. This handles the primary lemma's stated d>=2
convention. A zero vector creates no difficulty in either construction.

## 7. Completion at the exact frozen scope

Let q=log(1+L)>=log2. If q<=d, (5.3) is O(sqrt(dq)), including the A sqrt(d)
term because q is bounded below. If q>=d, (6.1) is O(sqrt(dq)), since
d<=sqrt(dq). Choose the signing from the appropriate regime. The two signings
need not agree; the theorem is existential and the regime depends only on d,L.
This proves(T). Empty trees and dimension zero are handled by zero sums.

## 8. Dependencies, contribution limits, and verification boundary

The following operations are prior inputs: source097 filtered-body energy,
adaptive shifted signs, predictor-column cancellation and deterministic
one-chain control; Gaussian Brownian correlation/survival; DGLN finite-set
Gaussian-body/subgaussian minimax; the primary Bansal etal tree-body theorem;
heavy-light decomposition, independent MGF summation, sphere nets and unary
compression. The candidate deduction is the joint HARD-supported prefix law
via energy-preserving arbitrary Gaussian-body intersection, and its use to
replace all-vertex tests by L chain-head tests without a unary-length loss.
The regime comparison is elementary, not a separately claimed contribution.

Kulkarni–Reis–Rothvoss2308.01406v1 Thm19 already gives a tree-signing law with
O(1)-subgaussian root-path marginals, via cloning and a Gaussian empirical-law
body. Its all-prefix high-probability norm estimates retain log(length).
Aden-Ali2607.04388v1 gives coupled Gaussian prefix representations efficiently.
Neither cited statement asserts deterministic length-independent hard support;
we do not condition either law on such an event. Russo–Wei2610.16715v1 uses
independent local subgaussian signers to control boundary paths in online
ordering. That path-summation architecture is prior; it does not state the
hard all-prefix chain law used here. Dutta–Jha–Jiang2604.13355v1 supplies an
algorithmic one-order bound O(sqrt(d)+d^(1/4)log^(7/4)n), attaining sqrt(d)
when d>=log^7 n. It is a different algorithmic contract, not an algorithmic
consequence claimed for(T).

All these comparisons are bounded and operation-specific; no worldwide
priority claim is made. The prior r4 two-order target remains unresolved and
is not restricted or relabeled. Parent author assistance and the complementary
analytic worker's conditional assembly note are recorded in author-assistance.json.
Their checks are not independent reviews. Exact finite diagnostics validate
interpretations and algebra on stated samples, not this universal theorem.
No Lean proof of the analytic or full combinatorial result is claimed. A
feasible scoped formalization would encode finite-tree chain decompositions,
path identities and the final numerical regime comparison, conditional on the
explicit analytic input theorems. Acceptance requires the campaign's independent
proof, substantial-contribution and scoped-formal gates.
