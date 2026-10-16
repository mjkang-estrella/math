# Stable cut operators for all-edge FK barriers: research candidate r9

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT.
Private third-party inputs retain their original rights.

**Disposition: proposed complete proof of the full frozen target G, pending
independent proof and contribution gates. No PASS, substantiality verdict,
acceptance, count change, manuscript, formalization or release is claimed.**
The campaign remains 4/10. This is a new target outside F. The proof-reviewed
technical theorem F and both reviews, with all parent corrections, remain
unchanged. No universal largest-cut bound is used.

## 1. Exact target, normalization and probability mode

Fix any real q>4 and any alpha in (1/2,1). For each integer n>=1 sample a
rooted spherical map and edge subset (M_n,A_n), with n edges, with weight
proportional to q^{k_M(A)+(|A|-|V(M)|)/2}. Keep loops and parallel edges.
Independently assign **every** edge an iid R with P(R>r)=r^{-alpha}, r>=1.
Let m(v)=deg_M(v), counting two loop darts, M=2n, N=M+1, b_N=N^{1/(2alpha)}.
The energy and generator are

 E_n(f)=sum_{nonloop e=vw} R_e^{-1}(f(v)-f(w))²,
 L_n f(v)=m(v)^{-1}sum_{nonloop e=vw} R_e^{-1}(f(w)-f(v)).

Edges in sums are unoriented and counted with multiplicity. On degree-mean-
zero functions let K_n=(-L_n)^{-1}; take K_n=0 on a one-vertex map. Its norm
is tau_n=sup Var_m(f)/E_n(f), with unnormalized degree variance.

Use the source's exact corner tree T_N. Its nonroot nodes in preorder,
numbered 1,...,M, correspond to M original darts. Put the pole of node j on
the cell [(j-1)/M,j/M) of [0,1]. The resulting pullback U_n is an isometry
from L²(m/M) into L²[0,1]. Its adjoint averages over cells belonging to each
vertex. Put H0={g in L²[0,1]: integral g=0}, and extend U_n K_n U_n* by zero
on the orthogonal complement of the image. This extended operator preserves
H0 and has the same nonzero eigenvalues, norm and trace as K_n.

Write p_k for the **exact** offspring law in source `block:offspring`, and
sigma²=Var(xi). Thus p_{2j}=b_j v^j/Phi(v), p_{2j+1}=0, E xi=1,
0<sigma²<infinity, p_0p_2>0. Constants below use this sigma, not the map
metric comparison constant beta.

Let e be a standard normalized Brownian excursion, using exactly the source
metric d_e(s,t)=e(s)+e(t)-2min_[s,t] e. Let (T_e,d_e,mu_e) be its rooted CRT,
ell its skeleton length. For ell-a.e. x the component above x away from the
root is coded by one open interval I_x=(a_x,b_x); set s_x=b_x-a_x and
u_x=1_{I_x}-s_x in H0. Branch points and endpoints have zero ell measure.
Conditional on e, let P be a Poisson measure on (x,r), r>0, of intensity

 c_q ell(dx) alpha r^{-alpha-1}dr,       c_q=p_2/sigma.              (1.1)

The proposed limiting operator, with tensor in the Lebesgue inner product,
is

 K=sum_{(x,r) in P} r (nu_x tensor nu_x).                           (1.2)

The proof below establishes its construction, not merely names a resistance
form. It is positive trace class, nonzero and injective on H0 almost surely.
If h_N(t)=sigma H_{Nt}/(2sqrt N) is the linearly interpolated preorder height
with terminal value zero, the assertion is joint convergence in law

 (h_N, (M b_N)^{-1}U_n K_n U_n*) => (e,K)                          (G)

in C[0,1] times the trace norm topology of self-adjoint trace-class operators
on H0. Both limit coordinates use the same excursion. The probability is
annealed over the finite map and its resistances; (1.1) specifies the exact
conditional law in the limit. No path-process or resistance-metric compactness
claim is added.

In particular, through all integer n,

 n^{-[1+1/(2alpha)]}tau_n => 2^{1+1/(2alpha)}||K||.                 (1.3)

The limit is finite, strictly positive and nonconstant. The self-adjoint
inverse A=K^{-1} on H0 has domain Ran K; its closed quadratic form has domain
Ran K^{1/2}, as detailed in Section 8. No larger offspring moment, bounded
blocks, tree-only model, bridge-only disorder, restricted q, subsequence,
changed clock or reduced alpha range is present. Nothing here treats the
endpoint alpha=1/2.

## 2. Stipulated source interfaces and predecessor boundary

The immutable source is openai/math at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, accepted true. For the FK-above-four
manuscript the prefix is

https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Brownian-continuum-random-tree-limits-of-finite-Fortuin-Kasteleyn-maps-above-four-September-24-2026/build/

Actual statements used:

* `main.tex`, `eq:finite-law`, `eq:degree-measure`: exactly the finite law
  and degree clock above, including loop conventions.
* `sections/blocks.tex`, `block:decomposition`, `block:finite-law`: exact
  independently marked GW representation conditioned on N=2n+1, all odd N
  attainable. A block with k/2 edges has k children, its ordered corners.
* Same file, `block:offspring`, `block:moments`, `block:one-edge`: the even
  critical finite-variance law above. Given k=2 the mark is a link or loop
  with probability 1/2 each. Thus a link at a node has probability p_2/2.
* `sections/trees.tex`, `tree:excursion`, `tree:conditioning`: h_N=>e,
  pi_s=P(|T|=s)=a_s(-1)/s, and the span-two local limit estimate. Here
  a_j(z)=P(sum_{i<=j}(xi_i-1)=z), a_0(0)=1.
* Same file, `tree:paths` and `tree:spine-law`: for any fixed 0<=b<=k,
  uniform ancestral sums equal their spine mean times depth plus o_P(sqrt N).
  The spine mass of a given (k,i) is p_k, for 1<=i<=k.
* `sections/metric.tex`, `metric:measure`: uniform nonroot-node measure is
  exactly original degree divided by M. A child subtree of S nodes accounts
  for S darts: S-1 inserted darts plus its parent corner dart.

The proof uses the source bounded-label path theorem only for a 0-1 link
label. It never applies it to an unbounded resistance. The geometric CRT
metric theorem by itself does not assert (G).

The exact grounded inverse-block decomposition and elementary two-path
moment estimate already appeared in F. They are credited and re-proved here
for clarity; they are not nominated as new lemmas. F's microscopic fringe
LLN, Frechet law and separation of bounded-mass traps are **not** used in this
regime. Fill–Janson and Abraham–Delmas–Nassif already identify the global
subtree-power scale and important additive-measure operations; our argument
must additionally establish a trace-class barrier operator limit with every
cyclic block included. Section 10 compares operations and states reading limits.

## 3. Two conditioned-tree estimates

Constants in this section depend on the fixed offspring law and indicated
exponent. The source local limit, together with Fourier inversion, gives

 a_j(z)<=C(j+1)^{-1/2},     a_N(-1)>=c N^{-1/2}                     (3.1)

for all j,z and all attainable N, after absorbing finitely many small sizes.
At incompatible lattice sites the probability is zero. Only odd tree sizes
occur. Consequently pi_s<=C s^{-3/2}. No positive exponential moment or
third offspring moment is needed.

### 3.1 Fringe powers and small subtrees

For any nonnegative fringe toll f, cyclic rotation of the iid offspring
list conditioned to sum to -1 gives the exact identity

 E sum_{u in T_N} f((T_N)_u)
 =N sum_{s<=N} E[f(T);|T|=s] a_{N-s}(0)/a_N(-1).                  (3.2)

Indeed a length-s tree window has sum -1, leaving sum zero; exactly one
rotation of a total-sum -1 list is a tree word. Marks can be carried along.
The full window s=N is the root, with exactly the same formula. This is the
classical cyclic-fringe identity, credited to Janson.

For any a>1/2, (3.1), pi_s<=Cs^{-3/2} and the elementary beta-sum estimate
imply

 E sum_u |(T_N)_u|^a <= C_a N^{a+1/2}.                           (3.3)

In detail the right side of (3.2) is bounded by
C N^{3/2}sum_{s<=N}s^{a-3/2}(N-s+1)^{-1/2}. The sum is O(N^{a-1});
the endpoint s=N contributes only O(N^a) to (3.2). These bounds also hold
for all small N after changing C_a. If 0<delta<=1/2, then

 E sum_{u: |(T_N)_u|<=delta N}|(T_N)_u|^a
       <= C_a delta^{a-1/2}N^{a+1/2}.                            (3.4)

Here the conditioning ratio is bounded on s<=N/2, and
sum_{s<=delta N}s^{a-3/2}<=C_a(delta N)^{a-1/2}; if delta N<1 the sum is
empty. These are expectation bounds, not independent fringe assumptions.

### 3.2 Exact selected-child identity and the second-moment tail

For every nonnegative g on offspring numbers and F on positive integers,

 E sum_{v in T_N}g(k_v)sum_{w child of v}F(|(T_N)_w|)
 = N/a_N(-1) sum_{s=1}^{N-1}F(s)pi_s
                  sum_{k>=1} k p_k g(k)a_{N-1-s}(1-k).           (3.5)

Here is a derivation including the near-N boundary. Apply (3.2) to the
root toll. Conditional on root offspring k, exchangeability lets us select
the first child and multiply by k. If this child has size s, the remaining
k-1 children form a GW forest of total size t. Its term is

 N/a_N(-1) k p_k g(k) F(s)pi_s
                sum_t P(F_{k-1}=t)a_{N-1-s-t}(0).

The increments xi-1 are at least -1. A walk of length m ending at -(k-1)
must first hit that level at some t<=m. The first passage is the exploration
of k-1 independent GW trees; after t, an independent remainder must sum to
zero. Thus the convolution equals a_m(1-k), m=N-1-s, exactly. For k=1
use the empty forest concentrated at t=0; k=0 contributes nothing. This
proves (3.5), including zero-length remainders. It uses neither a forest
asymptotic nor a size cutoff.

For a>1/2 insert F(s)=s^a and use (3.1). Summing over k first gives

 E sum_v g(k_v)sum_{w child}|(T_N)_w|^a
       <= C_a N^{a+1/2} E[xi g(xi)].                            (3.6)

Indeed the remaining sum is
C N^{3/2}sum_{s<N}s^{a-3/2}(N-s)^{-1/2}, of the same order as above.
Most importantly g(k)=k 1_{k>K} costs **E[xi²;xi>K]**, which tends to zero.
No k³ moment is introduced. The exact checker verifies (3.5) and its
first-passage convolution on small nonbinary even-offspring trees; that is
finite support, not proof of (3.6).

## 4. Convergence of the marked cut measure

For each nonroot node w let I_w be its interval of preorder cells after the
root cell is deleted, and s_w=|I_w|=|(T_N)_w|/M. Let b_w be one exactly when
its parent block is a link and w is the corner at the endpoint opposite the
parent pole. This selects one child of a link, not both. A link is a map
bridge, and its far-side original-degree mass is M s_w. There is a bijection
between selected w and map bridges.

By the source spine law the label b has mean

 theta=sum_{k,i}p_k E[b(k,i,B)]=p_2/2.                            (4.1)

It is bounded. Source `tree:paths` therefore gives

 D_N:=max_v |sum_{w on root-to-v path}b_w-theta H(v)|
                  =o_P(sqrt N).                               (4.2)

For a Lipschitz function phi(a,b) on the closed interval triangle that is
zero when b-a<=delta, delta>0, define

 Lambda_N(phi)=N^{-1/2}sum_{w!=root} b_w phi(I_w).

The following convergence is joint with h_N=>e:

 Lambda_N(phi) => (2theta/sigma)int_{T_e}phi(I_x)ell(dx)
                =c_q int phi(I_x)ell(dx).                      (4.3)

We give details because this supplies the mark **locations**, rather than
only their count or their branch masses.

Integrate over all M nonroot cells. Since a cell belongs to I_w exactly
when its node is a descendant of w,

 sum_w b_w phi(I_w)
 =int_0^1 dt sum_{w ancestor-or-self of v(t), w!=root}
                         b_w phi(I_w)/s_w.                     (4.4)

This is an exact finite identity. Along a root-to-node path the left
endpoints of these intervals increase and the right endpoints decrease.
The function F(a,b)=phi(a,b)/(b-a), set to zero near the diagonal, is
Lipschitz. Hence the sequence F(I_w) has total variation and supremum
bounded by a deterministic C_phi independent of the path or N. Summation
by parts and (4.2) show that replacing b_w by theta in (4.4) makes an error
at most C_phi D_N=o_P(sqrt N). The self-edge convention changes the
unmarked path sum by at most one bounded term; excluding the root has the
same harmless effect. For the centered marked sums all partial paths are
covered by D_N, including the self-edge when the endpoint is w.

It remains to identify the unmarked path integral. We describe the elementary
coding continuity used here. For a continuous excursion h and t with h(t)>z,
let I_h(t,z) be the component of {h>z} containing t. Along a fixed t its two
endpoints are monotone in z. At every continuity level z of both endpoints,
uniform convergence h_j->h and the sandwich at z-epsilon,z+epsilon force
I_{h_j}(t,z_j)->I_h(t,z) whenever z_j->z. Monotone endpoints have at most
countably many discontinuities. The argument also applies to discrete
ancestor intervals: the subtree at integer depth j, with its root omitted,
is the component above level j of the linearly interpolated preorder height,
up to at most one cell at either endpoint. If the chosen cell meets a descent,
its height differs from its node height by at most the maximum height jump;
this divided by sqrt N tends to zero by continuous-path tightness.
Deleting the root changes time coordinates by at most 1/N. Thus for a.e.
(t,z), the ancestor interval at depth asymptotic to 2sqrt N z/sigma tends
to I_e(t,z).

More explicitly, extend the ancestor weight as a step function of the
rescaled depth, with steps Delta z=sigma/(2sqrt N). For a.e. (t,z) below
e(t), the endpoint sandwich just proved gives convergence of this step
function to F(I_e(t,z)); above e(t) it is eventually zero, except in an
interval whose length tends to zero. Its absolute value is <=||F||_infinity,
and the heights are uniformly bounded along any uniform coding coupling.
Dominated convergence therefore yields

 N^{-1/2}int dt sum_{w ancestor of v(t)}F(I_w)
       -> (2/sigma)int_0^1 dt int_0^{e(t)} F(I_e(t,z))dz.        (4.5)

This can be applied along every subsequence via a further Skorokhod coupling
of h_N and D_N/sqrt N; (4.2) makes the latter converge to zero. Consequently
the claimed convergence holds in law jointly with h_N on the original
sequence.

On a real tree, integrating first over leaves above x gives the coarea
identity

 int_0^1 dt int_0^{e(t)} F(I_e(t,z))dz
       =int_{T_e}s_x F(I_x)ell(dx)=int phi(I_x)ell(dx).          (4.6)

For justification, first prove the identity on finitely many arcs of a
finite reduced subtree: length is ordinary dz on each arc and the set of
times above x has Lebesgue measure s_x. A countable increasing union of
root-to-dense-point arcs exhausts the skeleton, so Tonelli proves the
nonnegative case; bounded signed tests follow by splitting signs. This
also defines the sigma-finite length pushforward on interval space.
Equations (4.2)--(4.6) prove (4.3).

The measure on intervals with s>=delta is finite, since
int 1_{s>=delta}ell<=delta^{-1}int s ell
=delta^{-1}int e(t)dt. Its discrete counterpart is tight by (3.3) at a=1
(or directly by maximum height tightness). Lipschitz tests supported away
from the diagonal determine weak convergence of these locally finite
measures. Using a countable determining class gives (4.3) as joint random-
measure convergence. Mass cutoffs may be chosen along a deterministic
sequence delta down to zero for which the limit assigns zero mass to
s=delta almost surely; such a sequence exists by finiteness away from the
diagonal and Fubini. No new branching-process limit theorem is assumed.

## 5. Construction, integrability and compactness of the limit

The same unmarked argument gives

 (sigma/(2sqrt N))sum_{w!=root}delta_{I_w}
                   => (x->I_x)_*ell                            (5.1)

locally away from zero interval mass. By (3.3), for every alpha>1/2,

 sup_N E[(sigma/(2sqrt N))sum_w s_w^alpha]<infinity.

Apply convergence to bounded continuous nonnegative tests below s^alpha
supported away from s=0, then use the expectation lower passage and
monotone convergence. This proves

 E int_{T_e}s_x^alpha ell(dx)<infinity.                          (5.2)

This finiteness is also a known part of the global additive-functional
results of Fill–Janson and Abraham–Delmas–Nassif; the argument above proves
exactly the needed implication directly from the source. It is not a novelty
claim for the threshold. Put t_x=s_x(1-s_x) and J_e=int t_x^alpha ell(dx).
Then J_e<infinity a.s. It is strictly positive: the Brownian CRT has two
branches of positive length and positive mu mass, and an interior portion
of either branch has 0<s_x<1, by full support of mu. The integrand is positive
on a positive-length arc.

The Poisson measure (1.1) exists on a sigma-finite space: the skeleton is a
countable union of finite arcs, and the r-axis can be partitioned into
intervals bounded away from zero and infinity. Since ||nu_x||²=t_x,

 int ell(dx)int_0^infinity (1 wedge r t_x)alpha r^{-alpha-1}dr
                =J_e/(1-alpha)<infinity.                       (5.3)

It follows directly that sum_(x,r) r t_x is finite almost surely:
the terms exceeding one are finitely many, each finite, and the sum of
terms at most one has finite conditional expectation. Thus (1.2) converges
absolutely in trace norm, independently of its enumeration, and defines a
positive trace-class, hence compact, operator on **all** H0. In particular,

 Tr K=sum_(x,r)r t_x,
 E[exp(-z Tr K)|e]
   =exp[-c_q Gamma(1-alpha)z^alpha J_e],   z>=0.                 (5.4)

The scalar integral follows by integration by parts from
int(1-exp(-zr t))alpha r^{-alpha-1}dr=Gamma(1-alpha)(zt)^alpha.
This is a conditional trace law; it is not a Frechet law for ||K||.

## 6. Bridge operator convergence, including both trace tails

The exact inverse decomposition, proved in Section 7, makes the normalized
bridge contribution on H0 exactly

 B_N=sum_{w:b_w=1}(R_w/b_N)(nu_{I_w} tensor nu_{I_w}),
       nu_I=1_I-|I|.                                          (6.1)

Conditional on the marked map tree, the R_w here are independent Pareto
variables, independent of the tree. Their nonloop edge identities are
distinct; cyclic edges have not been discarded from the model.

For delta>0 and 0<epsilon<L<infinity, retain only s_w>delta and
R_w/b_N in (epsilon,L). Let B_N^{delta,epsilon,L} be the resulting finite
sum. Conditional Laplace functionals show joint convergence of its marked
point measure with h_N to the restriction of P in (1.1). Indeed for a
nonnegative continuous test f supported on those intervals and r values,

 E[exp(-sum_w b_w f(I_w,R_w/b_N))|tree]
 =prod_{w:b_w=1}(1-N^{-1/2}int(1-exp(-f(I_w,r)))
                                      alpha r^{-alpha-1}dr).    (6.2)

The formula is exact once b_N epsilon>=1. The sum of subtracted terms
converges by (4.3), and their squares are at most their maximum O(N^{-1/2})
times their tight sum. Taking logarithms proves the Poisson functional
with intensity c_q ell(dx)alpha r^{-alpha-1}dr. Bounded continuous tests of
h_N may be multiplied into (6.2), proving joint convergence. The finite
intensity restrictions imply tightness; a countable separating family of
tests identifies the point-measure law. Choose the above generic delta;
r-boundaries have zero limit intensity. Since
||1_I-1_J||²=|I symmetric-difference J|, the map
(I,r)->r nu_I tensor nu_I is trace-norm continuous for s>=delta and
bounded r. Thus finite sums converge in trace norm:

 (h_N,B_N^{delta,epsilon,L}) => (e,K^{delta,epsilon,L}).           (6.3)

Here are the required uniform remainders. They control positive **sums**,
not only the largest rank-one term.

**Small interval mass, with arbitrarily large resistance.** For a Pareto R
and z>=0,

 E(1-exp(-zR))<=C_alpha z^alpha.                                 (6.4)

For 0<z<=1 this follows from
z int_0^infinity exp(-zt)P(R>t)dt and the Pareto tail; for z>=1 enlarge C.
Also P(Y>eta)<=E(1-exp(-Y/eta))/(1-exp(-1)) for Y>=0. By
1-exp(-sum y_i)<=sum(1-exp(-y_i)), these imply, conditionally on the tree,

 P(sum_{w:s_w<=delta}b_w (R_w/b_N)t_w>eta |tree)
       <= C_alpha eta^{-alpha}N^{-1/2}sum_{s_w<=delta}s_w^alpha,
       t_w=s_w(1-s_w).                                        (6.5)

No independence is needed for this upper bound. By (3.4), with M=N-1,
its expectation is at most C_alpha eta^{-alpha}delta^{alpha-1/2}, uniformly
in sufficiently large N (replace delta by 2delta; root omitted). This tends
to zero for the **entire** open alpha range. The operator norm and trace norm
of this positive remainder both equal or are bounded by its trace.

**Small resistance mark, with all interval masses.** Direct Pareto integration
gives

 E[(R/b_N)1_{R/b_N<=epsilon}]
       <=[alpha/(1-alpha)]epsilon^{1-alpha}N^{-1/2}.             (6.6)

Consequently the expected trace of all these terms is <=
C_alpha epsilon^{1-alpha}N^{-1/2}E sum_w s_w
<=C_alpha epsilon^{1-alpha}, by (3.3) with a=1. This is an unconditional
truncated expectation, not conditioning on the absence of a large mark.

**Very large resistance on retained masses.** By a union bound,

 P(exists w: s_w>delta, b_w=1, R_w/b_N>L)
       <=L^{-alpha}N^{-1/2}E #{w:s_w>delta}
       <=C L^{-alpha}/delta,                                  (6.7)

using #{s>delta}<=delta^{-1}sum s and again (3.3). This suffices even though
large-mark traces need not have a finite expectation.

The corresponding limits obey the same vanishing remainders: (5.2) and
monotone convergence make int_{s<=delta}t_x^alpha ell(dx) tend to zero;
(6.4) in its Poisson version bounds the probability of their trace exceeding
eta. Small-r expected trace is c_q alpha/(1-alpha)epsilon^{1-alpha}int t_x ell,
whose mean is finite by (5.2), or by (5.1),(3.3) at a=1. The probability of
r>L at s>delta is <=c_q L^{-alpha}int_{s>delta}ell, with finite expectation
bounded by C/delta. Equivalently, all follow by Poisson integration.

To finish, first make the small-mass error small by choosing delta, then
the small-r error by choosing epsilon, then the large-r error by choosing L
at this delta. Keep these cutoffs fixed in (6.3). The triangle inequality
for bounded Lipschitz tests on C[0,1] times trace class, followed by the three
remainder bounds, proves

 (h_N,B_N)=>(e,K) in C[0,1] times trace norm.                     (6.8)

This also proves that neither an invisible microscopic mode nor an omitted
collection of small marks has been assumed away. Interactions between
nested or disjoint macroscopic cuts remain in K.

## 7. Every cyclic block is negligible with the actual moment assumption

We first recall the exact finite electrical decomposition, to specify both
the clock and the comparison being used. Work on degree-mean-zero vertex
functions with inner product <f,g>_m=sum_v m(v)f(v)g(v). For each nonloop
block B ground its local potentials at the pole o_B, with local energy inner
product. Extend a local potential constantly into each exterior component,
using its attachment-vertex value, and subtract its global m-mean. Call this
map J_B. Different block extensions have disjoint energy: every other
extension is constant across every edge of B. Conversely, successive
block differences reconstruct every global potential modulo constants.
Thus the direct sum extension J is an energy isometry and

 K_n=JJ*=sum_B J_BJ_B*,                 K_B:=J_BJ_B*>=0.          (7.1)

The adjoint is from the m inner product to local energy. Indeed
E(JJ*g,f)=<g,f>_m, which characterizes the inverse. Single loops have zero
potential dimension and give zero terms, while retaining all their darts
in m. For an energy-orthonormal local basis (g_j),
sum_j g_j(x)²=R_B(o_B,x), the squared norm of evaluation. Centering decreases
m norm. Assigning exact corner masses then gives

 Tr K_B <=sum_{i=1}^k S_i R_B(o_B,x_i),                          (7.2)

where S_i is the i-th child size, x_i its corner vertex. Extra exterior
root-side mass is at the pole and has resistance price zero. Several corners
at one vertex add their distinct dart allocations; none is counted twice.

For a link with far-side set A and degree mass Ms, its local extension is
sqrt R times (1_A-s). Consequently

 K_B=R(1_A-s) tensor_m (1_A-s).

After U_n pullback and division by M b_N this is exactly
(R/b_N)nu_I tensor nu_I, proving (6.1). The factor M is essential: tensor_m
is M times the tensor for probability mass m/M. This verifies the
normalization of (G).

For every other nonloop block and every x, there exist two edge-disjoint
pole-to-x paths, chosen from the block shape before exposing resistances.
Indeed a bridge in a loopless connected block without a separating vertex
would force it to be the one-link block. The edge form of Menger, or the
elementary unit-capacity augmenting-path argument, supplies the two paths.
If their lengths are l_1,l_2, then l_1+l_2<=k/2. Their resistance sums U_1,U_2
are independent, and Thomson's principle gives R_B(o,x)<=min(U_1,U_2).
For a sum U of l Pareto resistances,

 P(U>t)<=lP(R>t)+t^{-1}lE[R;R<=t]<=C_alpha l t^{-alpha}, t>=1.

Thus the minimum has tail <=min(1,C_alpha²l_1l_2t^{-2alpha}). Integrating
alpha t^{alpha-1} times this bound proves

 E[R_B(o,x)^alpha |B]<=C_alpha sqrt(l_1l_2)<=C_alpha k.            (7.3)

This includes two parallel edges. At x=o the value is zero. Only the alpha
moment is used; no first moment uniformly in k is assumed.

Set Z_{v,i}=R_{B_v}(o,x_i) on cyclic nonloop blocks, zero on links, loops and
leaves. These marks are independent of the child tree sizes given offspring
and block shape. For every fixed K there are finitely many rooted block
shapes of offspring at most K. Since (7.3) is finite,

 d_{K,L}:=max_{k<=K,B,i}E[Z_{v,i}^alpha;Z_{v,i}>L |B] ->0
                  as L->infinity.                             (7.4)

For k>K, (7.3) bounds the same tail by C_alpha k without any truncation.
Split (7.2) into corner prices Z<=L and Z>L. The total bounded-price trace
is at most

 L sum_{v,i}S_{v,i}=L sum_{w!=root}|(T_N)_w|
                 <=L N max_v H(v)=O_P(L N^{3/2}).               (7.5)

Dividing by M b_N makes this tend to zero for every fixed L, since alpha<1.
For the tail, concavity of x^alpha and then (3.6), averaging block and
resistance marks first, give

 E[( (M b_N)^{-1}sum_{v,i}S_{v,i}Z_{v,i}1_{Z_{v,i}>L})^alpha]
 <=(M b_N)^{-alpha}E sum_{v,i}S_{v,i}^alpha
           [d_{K,L}1_{k_v<=K}+C_alpha k_v1_{k_v>K}]
 <=C_alpha[d_{K,L}E(xi;xi<=K)+E(xi²;xi>K)].                    (7.6)

We used (M b_N)^alpha=M^alpha sqrt N, comparable to N^{alpha+1/2}; no
conditioning ratio was bounded without its near-N factor. Markov's
inequality, (7.5),(7.6), first N->infinity at fixed K,L, then L->infinity
at fixed K, and finally K->infinity prove

 (M b_N)^{-1}sum_{cyclic blocks}Tr K_B ->0 in probability.        (7.7)

This positive remainder's trace norm equals its trace and is unchanged by
the isometric pullback. It pays **all** cyclic-edge disorder with only
E xi²<infinity. No universal tree-gap comparison, diameter bound for the
random-resistance metric, third offspring moment or bounded-block event
is used. Equations (6.8),(7.1),(7.7) prove the full operator convergence (G).

## 8. Injectivity, inverse domain and a nondegenerate inverse gap

We supply the remaining analytic properties of (1.2). Conditional on e,
Poisson marks project densely onto every nonempty open subarc of the
skeleton, almost surely. To see this, take a countable collection of arc
bases exhausting the skeleton. Each has positive finite ell measure and
infinite mark intensity as r decreases to zero; the chance of no mark is
zero. A countable intersection gives the assertion, and mark locations
avoid the countable CRT branch points and leaves.

On any arc, at a nonbranch interior point x, the cut indicator nu_y tends
to nu_x in L²(mu_e) as y approaches x along that arc. Indeed the symmetric
difference of the nested clades decreases to the singleton x when the
point is not a branch point; mu_e has no atoms and charges no skeleton.
Therefore the closed span of marked cut indicators contains the indicators
of all nonbranch cuts on a countable dense family of arcs. It also contains
all nonbranch cuts elsewhere by exhaustion of the skeleton by root-to-dense-
leaf arcs. At every such point one may choose an arc containing an open
neighborhood of it along its unique line of descent, so the density argument
applies on that arc.

These clades generate the Borel sigma-field on the leaf support. For two
distinct leaves choose a regular interior point on the path above their
last common ancestor toward one leaf; its clade separates them. One can
choose a countable separating family from dense arcs and regular points.
The family is laminar: clade intersections are one of the two clades or
empty. Its linear span together with constants is therefore an algebra,
and the measurable monotone-class theorem makes it dense in L²(mu_e).
For completeness, a countable separating family on this compact metrizable
tree generates its Borel sigma-field: the induced injective measurable map
into {0,1}^N is a Borel isomorphism onto its image. Equivalently finite
separating cut partitions distinguish the points of a countable dense
support and refine to the full leaf sigma-field. Thus centered regular cut
indicators have dense span in mean-zero L²(mu_e).

The coding map identifies L²(mu_e) with L²[0,1] up to null sets,
rather than only a proper subspace. Here no extra path-limit theorem is
needed. Aldous, CRT III, Section 2.3 (definition (a)–(c)) and Corollary 22,
gives the binary CRT with nonatomic mass supported on leaves, in his 2e
normalization; scaling the metric by 1/2 gives the source normalization e
and the same mass measure. Full support also follows directly: the quotient
map is continuous and onto, so the preimage of any nonempty open ball is
a nonempty relatively open time set and has positive Lebesgue measure.
To prove almost-everywhere injectivity, suppose t<u code the same point x.
Then e(t)=e(u)=min_[t,u]e=:h. If e(v)>h at any intervening time v, x is a
strict ancestor of [v], and hence is not a leaf. Otherwise e is constant
on [t,u], so mu_e has an atom of mass at least u-t at x. Neither alternative
can occur for a point in the nonatomic leaf support. Thus every leaf has
at most one coding time (apart from a possible zero-mass root exception),
and the coding map is injective on a full Lebesgue-measure set. Its Borel
inverse on that set identifies the two L² spaces. The dense-span conclusion
therefore transfers to H0.

If <g,Kg>=0, positivity and the trace-norm series imply
sum_(x,r)r|<g,nu_x>|²=0. Every term is zero. The dense span just proved forces
g=0. Thus K is injective. This is an almost-sure statement about the span
of the random collection, so it applies simultaneously to all g, including
g depending on the marks; it is not an uncountable intersection of
fixed-g zero-probability statements.

By the compact positive spectral theorem K has an orthonormal eigenbasis
(f_j) of H0, with eigenvalues kappa_j>0 tending to zero and
sum_j kappa_j<infinity. Its inverse is the self-adjoint positive operator

 D(A)={f:sum_j |<f,f_j>|²/kappa_j²<infinity}=Ran K,
 Af=sum_j kappa_j^{-1}<f,f_j>f_j.

Its closed quadratic form is

 D(Q)={f:sum_j |<f,f_j>|²/kappa_j<infinity}=Ran K^{1/2},
 Q(f)=sum_j kappa_j^{-1}|<f,f_j>|².

On the full L² space one may adjoin constants with eigenvalue zero for A.
This spectral domain description is the claim in G; no pathwise resistance-
form/process construction is being asserted without additional work.

Finally J_e>0 and c_q>0. A mark with r t_x>R gives ||K||>R except possibly
at equality, a null mark boundary. Conditional on e its existence has
probability 1-exp(-c_q R^{-alpha}J_e)>0 for every R>0. Also K is finite and
nonzero a.s. by (5.3) and the dense span (or by infinitely many positive
marks on an arc). Therefore ||K|| is finite, strictly positive and has
unbounded support; in particular it is not a constant. Trace norm convergence
implies norm convergence in law by continuity. Since

 M b_N/n^{1+1/(2alpha)}
       =2 (2+1/n)^{1/(2alpha)} ->2^{1+1/(2alpha)},

(G) proves (1.3) with its exact constant and all-integer-n quantifier.

## 9. Scope stress tests and computational limitations

The limiting operator is not replaced by its largest individual term.
For nested intervals I=(0,3/4), J=(0,1/2), take r_I=16/3 and r_J=4. Both
individual trace/norm weights equal one, but the squared inner product of
their normalized cut vectors is 1/3. The sum has characteristic polynomial
lambda²-2lambda+2/3, and top eigenvalue 1+1/sqrt(3)>1. Such interactions are
retained by (1.2); the small-trace remainders do not erase them.

The parent's unit-path counterexample is preserved. On an n-edge path with
unit resistance and original-degree masses, f(i)=i gives inverse-gap lower
bound (n²+2)/6 whereas every individual cut weight is <=n/2. Their ratio
diverges. This rules out the rejected universal comparison; no step above
uses it or a mislabeled tree Hardy theorem.

For alpha=1/2 the power delta^{alpha-1/2} in (3.4),(6.5) does not decrease.
Fill–Janson's endpoint expected subtree toll is n log n. The endpoint is
outside G, and neither the proof nor the scale is claimed there. For alpha
approaching either endpoint no uniform estimates are asserted.

`checks.py` uses exact rational arithmetic, with critical offspring supported
on {0,2,4}; it enumerates small conditioned plane trees, checks (3.5), its
first-passage convolution, and the preorder interval integral identity. It
also checks the nested-cut interaction polynomial, exact path counterexample,
and one-child link spine mean. These checks cannot establish any weak limit,
CRT integrability, injectivity, asymptotic trace tail or contribution verdict.
The arguments in Sections 3–8, not the finite receipt, constitute the proposed
proof. No simulation is used as proof, no solver incumbent is a bound, and
there is no formalization claim.

## 10. Bounded predecessor comparison and gate request

Actual reading extents and pinned source URLs are recorded in
`source-contracts.md`; `literature-screen.md` records the bounded search and
operation comparison. The main credited antecedents are:

* Janson's cyclic-fringe identity and finite-variance local-limit method.
  The selected-child identity (3.5) is an explicit first-passage convolution
  using those classical ingredients. It is not a claimed new general
  branching theorem. Its role here is to retain E[xi²;xi>K] in (7.6).
* Fill–Janson, arXiv:2104.02715v1, Theorems 1.7(iii),(iv), 1.10(i), 1.12:
  subtree-power scaling above 1/2, the distinct endpoint, and related moment
  convergence. Abraham–Delmas–Nassif, arXiv:2009.08185v1, Theorem 1.1 and
  the measure definitions (1.6)–(1.8), already provide the global additive
  CRT measure framework. Our cut-measure proof retains **preorder interval
  location** and the link/opposite-child thinning needed for the operator;
  the coarea principle and mass-power threshold are credited, not nominated.
* Croydon, arXiv:1609.05666v1, Assumption 1.1/Theorem 1.2, requires convergence
  of the actual measured resistance spaces. It does not supply that convergence
  from the undisturbed CRT, or by itself prove this trace-class statement.
  Croydon–Hambly–Kumagai, arXiv:1609.02120v1, Section 6.1, instead homogenizes
  finite-mean **resistances** with heavy **conductances** bounded below,
  while the conductance-degree clock has a FIN speed-measure limit. Our
  Pareto resistances have infinite mean and the clock is original degree.
* Andriopoulos, arXiv:1812.10197v1, treats random Gaussian tree potentials and
  assumes convergence of the resulting measured resistance trees. Archer,
  arXiv:2011.07266v1, treats decorated infinite stable-offspring trees and
  walk/spectral dimension exponents with stated decoration growth bounds.
  The inspected statements do not supply G.
* F's cut-vertex inverse decomposition, two-path alpha moment, and positivity
  estimates are reused and credited as classical/elementary. Flegel and
  heavy-tailed random matrix analogies are context only, not an implication
  of G. Faggionato's segment random-barrier theorem is an important one-
  dimensional antecedent, with a generalized differential operator limit;
  it does not include the conditioned branching geometry and cyclic payment.

The three pinned walk/spectral companion theorem statements concern ordinary
conductances on FK–Ising or spanning-tree surface models, not this q>4
all-edge barrier operator. Their model/theorem introductions were inspected;
their entire proof bodies were not read and are not used as premises.

The proposed full bridge consists of the interval-location stable cut limit,
its trace-class construction and spectral tails, and all-edge cyclic-block
negligibility at the same scale with only finite second offspring moment.
This report supplies a proof rather than assumes those operations. Whether
that package is a substantial contribution, or another technical assembly
from stronger general prior work, remains for an independent contribution
gate. **No worldwide novelty, priority or SUBSTANTIAL verdict is claimed.**
An independent reviewer should audit, in particular, the interval-coding
continuity/summation-by-parts step in Section 4, the exact (3.5) near-N
convolution, the second-moment tail in (7.6), the two trace-tail passages in
Section 6, and the dense-span/injectivity proof in Section 8.

## 11. Authentication, rights and handoff

`inputs/private/frozen-r7/` is a complete preserved authenticated copy of F's
package. Its externally supplied seal SHA256 is
80f72efab2af1c25bb440a49fcaacd5410601d328b83c0f59055be65958ae7bc.
It was hash-only checked before any stored code execution; none of its code
was executed here. Separate proof and contribution reports and parent
corrections are retained under `inputs/private/history/`. All 13 copied
upstream blobs were independently matched with their exact Git-blob SHA1s
in the full nontruncated preprints tree. New primary-literature PDFs and
text extractions have private paths, retrieval provenance, sizes and hashes.

The SHA256/size input and output inventories are frozen. `seal.json` binds
them; its hash is detached in the terminal handoff. `verify.py` authenticates
that external anchor, both inventories, every payload byte, exact file
membership, all pinned blobs and the preserved F seal before replaying only
the r9 checker with Python -B. It compares the checker stdout with the frozen
receipt and writes no receipt, manifest, bytecode or cache, even on failure.
Mutation diagnostics use only disposable copies inside r9. Authentication and
replay are not independent mathematical reviews. The parent alone integrates
or commissions gates; no child acceptance is authorized.
