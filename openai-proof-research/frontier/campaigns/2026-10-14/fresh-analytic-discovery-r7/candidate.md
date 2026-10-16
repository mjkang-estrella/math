# Heavy resistance traps on finite FK maps above four

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT.
Private third-party inputs retain their original rights.

**Disposition: full proposed proof of the fixed target F, awaiting separate
independent proof and contribution review. Not accepted, counted, formalized,
published or submitted.** The initial scope and its chronology are in
`original-scope.md`. No narrower theorem replaces F. The contribution
assessment below is a researcher's bounded comparison, not a gate result.

## 1. Exact statement

Fix **any** real q>4 and **any** alpha in (0,1/2). For each integer n>=1
sample the rooted spherical n-edge map and edge subset (M_n,A_n) with
probability proportional to

    q^{k_M(A)+(|A|-|V(M)|)/2}.

Loops and parallel edges are retained. Independently, assign every edge an
independent resistance R with

    P(R>r)=r^{-alpha},  r>=1.

Write m(v)=deg_M(v), including two darts for a loop, and M=sum_v m(v)=2n.
On real vertex functions define

    E(f)=sum_{nonloop e=uv} R_e^{-1}(f(u)-f(v))^2,
    Var_m(f)=sum_v m(v)(f(v)-M^{-1}sum_w m(w)f(w))^2,
    tau_n=sup_{E(f)>0} Var_m(f)/E(f).

Set tau_n=0 on a one-vertex map. Equivalently, tau_n is the inverse first
positive eigenvalue of -L, where

    Lf(v)=m(v)^{-1}sum_{nonloop e=vw}R_e^{-1}(f(w)-f(v)).

The speed measure is the **original degree**, not the sum of conductances.
This distinction is part of the fixed model.

Use the exact offspring law p_k of `block:offspring` in the pinned source:

    p_{2j}=b_j v^j/Phi(v),   p_{2j+1}=0,
    E xi=1,   0<Var xi<infinity,   p_0 p_2>0.

Let T be the unconditioned Galton--Watson tree with this law. Then the
proposed theorem is, for every x>0, through **all positive integer n**,

    P(n^{-1/alpha}tau_n <= x)
        -> exp(-K(q,alpha)x^{-alpha}),
    K(q,alpha)=p_2 E|T|^alpha in (0,infinity).             (F)

No offspring third moment, bounded block size, tree-only restriction,
bridge-only disorder, or changed clock is assumed. Nothing is asserted
at alpha=1/2, for q approaching four uniformly, or for a conductance-degree
speed measure. Those were never part of F.

## 2. Exact stipulated source interfaces

All OpenAI premises are accepted true at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The source is
*Brownian continuum random tree limits of finite Fortuin--Kasteleyn maps
above four*, September 24, 2026. Its prefix is

https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Brownian-continuum-random-tree-limits-of-finite-Fortuin-Kasteleyn-maps-above-four-September-24-2026/build/

The proof uses stronger interfaces than the source's metric-limit abstract:

* `main.tex`, `eq:finite-law`: exactly the finite model above.
* `sections/blocks.tex`, `block:decomposition`, `block:finite-law`:
  the map is exactly the corner-substitution of independently marked
  Galton--Watson T_N, conditioned on N=2n+1 nodes. A block with j edges has
  2j ordered children. Given offspring 2j its block law is a(B)/b_j,
  independent of child subtrees before conditioning.
* The same file, `block:offspring`, `block:moments`: the stated even
  critical law has finite positive variance. The two one-edge blocks
  are a link and a loop, with equal weight 1+sqrt(q). Thus a node has a
  **link** mark with probability theta=p_2/2.
* `sections/metric.tex`, `metric:measure`, and the corner construction:
  each child subtree with S nodes accounts for S original-degree units
  at its parent's corner: one parent-block dart and S-1 inserted darts.
  Degree mass is exact; no metric approximation enters this calculation.
* `sections/trees.tex`, `tree:conditioning`: writing
  Y=xi-1 and S_j=sum_{i<=j}Y_i,
  P(|T|=s)=P(S_s=-1)/s is O(s^{-3/2}) and asymptotic to a positive
  multiple of s^{-3/2} through odd s. Consequently E|T|^alpha<infinity
  precisely for alpha<1/2 among positive alpha.

The source's arbitrary-label path law `tree:paths` is **not** an
estimate for the unbounded resistance labels here. The source metric
CRT theorem does not imply F. Private raw retrievals were independently
matched against the pinned Git blob SHA1 entries; SHA256 and sizes are
also recorded. `source-contracts.md` gives read extents and companion checks.

## 3. Conditioned fringe estimates, with no third moment

We give the needed conditioning argument explicitly. The cyclic-fringe
identity and its truncation method are classical; compare Janson,
arXiv:1312.1211v1, Theorem 1.3, Lemmas 5.1--5.2 and Remark 5.3.
The specific dominating toll in Lemma 3.2 is proved below.

### Lemma 3.1 (a useful integrable-toll criterion)

Let T have the offspring law above, with independent node marks whose law
depends only on offspring. Let f>=0 be a measurable marked-fringe toll.
Suppose

    E f(T)<infinity,
    h_s:=E[f(T); |T|=s]=o(1/s).                          (3.1)

Then, for T_N conditioned on odd size N,

    N^{-1} E sum_{u in T_N} f((T_N)_u) -> E f(T),
    N^{-1} sum_{u in T_N} f((T_N)_u) -> E f(T)
        in probability.                                (3.2)

Moreover the normalized sums have uniformly negligible expected toll
tails, in the following precise iterated sense:

    lim_{H->infinity} limsup_{N->infinity}
       N^{-1}E sum_u f((T_N)_u)1_{f((T_N)_u)>H}=0.       (3.3)

Proof. Set a_j(z)=P(S_j=z), with a_0(0)=1. The cyclic lemma for a
list of offspring increments totaling -1, with marks carried along,
gives exactly

    N^{-1}E sum_u f((T_N)_u)
      =sum_{s<=N} h_s a_{N-s}(0)/a_N(-1).               (3.4)

Only odd s occur. One way to see this is to start with the iid list
conditioned on total -1. A length-s consecutive window codes a fringe
tree exactly when its increments form a tree word. Its total is -1;
the independent remaining increments must total zero. Sum over its N
possible starting positions and rotate to the unique tree word.
The same reasoning includes s=N and yields the root contribution
without any exceptional convention.

The lattice local limit estimate gives, for all compatible indices,

    a_{N-s}(0)/a_N(-1) <= C sqrt(N/(N-s+1)),             (3.5)

and this ratio tends to one for each fixed odd s. Its ingredients are
sup_z a_j(z)<=C/sqrt(j+1) and a_N(-1)>=c/sqrt N. Fourier
inversion on a lattice fundamental interval proves the former: near
zero the modulus is <=exp(-ct^2); off zero it is bounded below one.
The source supplies the latter local limit asymptotic.

For s<=N/2, dominated convergence applies in (3.4), since sum_s h_s
is finite. For s>N/2 put epsilon_N=sup_{s>N/2}s h_s ->0. That part
of (3.4) is bounded by

    C epsilon_N N^{-1}sqrt N
                    sum_{0<=j<N/2}(j+1)^{-1/2}
       <=C'epsilon_N.

This proves the expected-value limit. The same argument applies to
f 1_{f>H}, dominated by f, and gives (3.3).

For completeness, the bounded-toll probability statement can also be
seen from the cyclic representation. First restrict to fringes of
size at most L. Two bounded such tolls use disjoint iid windows unless
their starting positions are within 2L on the circle; there are O(NL)
exceptional pairs. For fixed disjoint window sizes a,b their joint
conditioning factor is a_{N-a-b}(1)/a_N(-1), which tends to one by
the same lattice local limit estimate. Thus their average's variance
tends to zero. Marks on disjoint windows are independent given the
offspring, including arbitrary continuous resistance marks. Remove
the size cutoff using the expected-value argument for the bounded
tail toll. For unbounded f, apply this to min(f,H) and use (3.3) and
Markov's inequality. This proves (3.2). All limits use attainable odd
sizes. QED.

### Lemma 3.2 (the weighted-child toll)

For alpha in (0,1/2), write k for the root offspring and T_i for its
child subtrees, and put

    h(T)=k sum_{i=1}^k |T_i|^alpha,  h=0 if k=0.

Then E h(T)<infinity and E[h(T); |T|=s]=o(1/s).
The same conclusions, hence Lemma 3.1, hold for any nonnegative toll
whose conditional expectation given the entire unmarked tree is at
most C h(T).

Proof. Independence gives

    E h(T)=E xi^2 E|T|^alpha<infinity.                  (3.6)

We require a uniform forest bound. For a forest of j independent
copies of T with total size t, the elementary forest cycle formula is

    P(|T_1|+...+|T_j|=t)=(j/t)P(S_t=-j),  t>=j>=1.

It follows alternatively by applying the formal coefficient identity
[z^t]F(z)^j=(j/t)[u^{t-j}]phi(u)^t to F=z phi(F).
There are constants C,c>0 such that

    P(S_t=-j)<=C t^{-1/2}exp(-c j^2/t),  1<=j<=t,
    P(sum_{i<=j}|T_i|=t)
         <=C j t^{-3/2}exp(-c j^2/t).                  (3.7)

Here is why no positive exponential offspring moment is hidden.
Y>=-1 and E Y=0, E Y^2<infinity give
E exp(-rY)<=exp(C_0r^2) for small positive r. Chernoff
therefore bounds P(S_l<=-a) by exp(-c_0a^2/l) for 0<=a<=l.
To retain the local prefactor in (3.7), split the t summands into two
halves. In S_t=-j at least one half is <=-j/2. Bound that half by
Chernoff and the other half's point probabilities by C/sqrt t.
Adjust constants for t<=3. This proves (3.7).

Let pi_l=P(|T|=l). For large s, exchangeability of the children gives

    E[h(T);|T|=s]
      =sum_{k>=2} k^2 p_k sum_l l^alpha pi_l
           P(sum_{i=1}^{k-1}|T_i|=s-1-l).              (3.8)

There is no k=1 term since offspring are even. If l<=s/2, the residual
size is between s/3 and s for s>=6. By (3.7) this contribution is at
most

    C s^{-3/2} E|T|^alpha
           sum_k k^3 p_k exp(-c'(k-1)^2/s)=o(1/s).     (3.9)

Indeed divide the sum by sqrt s; its k-th term is k^2 p_k times
(k/sqrt s)exp(-c'(k-1)^2/s), which tends to zero for each k and is
bounded by a fixed multiple of k^2 p_k. Use E xi^2<infinity.
For l>s/2, l^alpha pi_l<=C s^{alpha-3/2}. For fixed k the sum
over residual sizes of the forest probabilities is at most one.
This part of (3.8) is at most

    C E xi^2 s^{alpha-3/2}=o(1/s).                     (3.10)

The conditional-expectation extension follows by averaging the marks
first. QED.

An important use of (3.1), rather than unqualified integrability, is
the near-N part of (3.4). Arbitrary integrable fringe tolls can have
spikes at conditioning sizes. We have not assumed those spikes away.

## 4. An exact electrical decomposition

Work temporarily with any fixed connected map, positive resistances,
and positive vertex masses m. Let H be the mean-zero vertex functions
with inner product <f,g>_m=sum_v m(v)f(v)g(v). Let A be the positive
energy operator, so <f,Af>_m=E(f), and K=A^{-1} on H. In the
zero-dimensional one-vertex case put K=0.

For each nonloop block B, fix its pole o_B. Let F_B be its potential
space with potential zero at o_B and with block energy inner product.
Extend a potential h on B to the whole map by making it constant on
each component attached to B, using its value at that attachment
vertex, and then subtract its global m-mean. Denote this linear map
by J_B. All of this is finite-dimensional.

Every global potential modulo constants uniquely decomposes as a sum
of such extended block potentials. To verify this, assign to each B
the differences f(x)-f(o_B) on its vertices. Summing along the
successive articulation blocks reconstructs f-f(o_root). Conversely
an extension from another block is constant across every edge of B.
Thus energies from different blocks are orthogonal and add exactly.
Single loops have zero-dimensional potential space and contribute
nothing. The total extension J from the orthogonal direct sum of the
F_B is an energy isometry onto global potentials modulo constants.
Taking adjoints with respect to energy and the m-inner product gives

    K=sum_B K_B,      K_B=J_B J_B^* >=0.                (4.1)

For example, E(JJ^*g,f)=<g,f>_m for every f, which verifies that
JJ^*=A^{-1}; this avoids any identification of adjoints with an
unweighted transpose. If g_1,...,g_d are an energy-orthonormal basis
on B, its uncentered evaluation variance at x is

    sum_j g_j(x)^2=R_B(o_B,x).                         (4.2)

This is the usual variational definition of effective resistance:
the squared norm of the evaluation functional h->h(x)-h(o_B).
Subtracting a mean contracts the m-norm. Therefore

    Tr K_B <= sum_v m(v)R_B(o_B,projection_B(v)).       (4.3)

In the source's exact corner tree let child sizes at a k-corner block
be S_1,...,S_k, and let x_i be the vertex of corner i. The mass on
the nonpole components equals sum of S_i over their corners. The
outside component is attached at the pole, where the resistance in
(4.3) is zero. Hence

    Tr K_B <= Z_B:=sum_{i=1}^k S_i R_B(o_B,x_i).        (4.4)

For a bridge e, its block is a one-link block. Let A_e be its component
away from the root pole, with original-degree mass s_e. Its opposite-
pole corner has exactly one child subtree, and

    s_e=|T_{i(e)}|.                                    (4.5)

Put u_e=1_{A_e}-s_e/M and t_e=||u_e||_m^2=s_e(1-s_e/M).
The bridge term in (4.1) is **exactly**

    K_e=R_e u_e tensor_m u_e,    ||K_e||=R_e t_e.        (4.6)

The far component has s_e original-degree units, including its one
bridge dart. For a leaf this mass is one. This is why replacing m by
conductance degree would change the theorem.

## 5. Cyclic blocks are negligible on the extreme scale

### Lemma 5.1 (shape-uniform two-path gain)

For any nonlink, nonloop source block B with m edges, and any vertex x,
independent alpha-Pareto resistances give

    E R_B(o_B,x)^alpha <= C_alpha m.                    (5.1)

Proof. Such a block is bridgeless: a bridge in a connected loopless
block with no separating vertex would force it to be the one-link
block. Consequently two edge-disjoint paths connect o_B to x when
x!=o_B. This elementary edge form of Menger's theorem also follows
by augmenting a unit-capacity path: absence of an augmentation yields
a one-edge cut. Let the two path lengths be l_1,l_2; their sum is at
most m. By sending all current down either path,

    R_B(o_B,x)<=min(U_1,U_2),

where U_j is the resistance sum on that path and U_1,U_2 are independent.
For a sum of l Pareto resistances and t>=1, union bound and truncation
give

    P(U>t)<=l P(R>t)+t^{-1}l E[R 1_{R<=t}]
             <=C_alpha l t^{-alpha}.                  (5.2)

Thus P(min(U_1,U_2)>t)<=min(1,C_alpha^2 l_1 l_2 t^{-2alpha}).
Integration of alpha t^{alpha-1} times this bound gives
E min(U_1,U_2)^alpha<=C'_alpha sqrt(l_1 l_2)<=C'_alpha m.
The case x=o_B is zero. QED.

Use concavity for alpha<1 in (4.4) and then (5.1). Given the entire
unmarked tree and block shape,

    E[Z_B^alpha | tree, B]
         <=sum_i S_i^alpha E R_B(o_B,x_i)^alpha
         <=C_alpha k sum_i S_i^alpha.                  (5.3)

Define the marked fringe toll f=Z_B^alpha on nonlink/nonloop blocks,
zero otherwise. Lemma 3.2 applies; in particular (3.3) holds. It follows
that, for a_n=n^{1/alpha},

    sum_{nonbridge blocks B} Z_B/a_n ->0
        in probability.                               (5.4)

Here is the truncation argument, including the dependence issue.
For delta>0 the probability that any Z_B>delta a_n is at most

    (delta^alpha n)^{-1}
       E sum_B Z_B^alpha 1_{Z_B^alpha>delta^alpha n},

which tends to zero by (3.3). On the complement, the expected sum
of Z_B/a_n is at most

    delta^{1-alpha} n^{-1}E sum_B Z_B^alpha
         <=C delta^{1-alpha}.

Markov followed by delta down to zero proves (5.4). No independence
between different fringe sizes or Z_B is used. From (4.1),(4.4),
the entire nonbridge contribution has operator norm o_P(a_n).

## 6. Exact bridge extreme law

Let the source link-mark probability be theta=p_2/2 and
A_alpha=E|T|^alpha. The marked fringe toll

    f(T)=1_{root block is a link}|T_{opposite child}|^alpha

is dominated by h(T), is integrable, and has expectation theta A_alpha.
Lemma 3.1, N/n->2, and (4.5) give

    n^{-1}sum_{bridges e}s_e^alpha ->2 theta A_alpha=K.  (6.1)

For every fixed L the same statement holds with 1_{s_e>L}, and its
limiting expectation tends to zero as L increases. It follows also that

    n^{-1}sum_e t_e^alpha ->K,                          (6.2)

since for s_e<=L the factor (1-s_e/M)^alpha tends uniformly to one,
and the remaining normalized s_e^alpha sum has negligible expected
mass after L increases. Notice that no root-side orientation estimate
is needed for a large branch; its alpha-weight is already controlled.

Let W_n=max_{bridges e}R_e t_e, with maximum zero if none. Conditional
on the map the bridge resistances are independent, so for x>0

    P(W_n<=a_n x | map)
          =product_e(1-t_e^alpha/(n x^alpha))           (6.3)

for all sufficiently large n. Indeed t_e<=M/4=n/2, whereas a_n
grows faster than n. The largest factor's subtracted term is at most
C_x n^{alpha-1}->0, deterministically. The sum of these terms tends
to Kx^{-alpha} by (6.2), and their squares sum to zero in probability.
Taking logarithms proves that (6.3) tends in probability to
exp(-Kx^{-alpha}). Boundedness removes the conditioning. In particular
W_n/a_n is tight.

## 7. Why the inverse gap equals the largest bridge trap asymptotically

We prove the genuinely spectral step, rather than identify an extreme
cut Rayleigh quotient with an eigenvalue without an upper bound.
For epsilon>0 call e large when w_e:=R_e t_e>epsilon a_n.
For every L, using conditional union bound and the original larger
weight s_e in place of t_e,

    P(exists large e with s_e>L)
      <=epsilon^{-alpha} n^{-1}
              E sum_e s_e^alpha 1_{s_e>L}.              (7.1)

Its limit superior tends to zero as L increases. The number J of
large edges is tight at each fixed epsilon, by the same bound without
the indicator.

Fix epsilon,L. Rooted far-side bridge components are either nested
or disjoint. A component of degree mass at most L contains at most L
vertices and at most L internal bridges. Hence, conditionally on the
map, there are at most nL unordered pairs of overlapping distinct
bridge components both having mass at most L. For both edges to be
large requires two independent resistances exceeding epsilon a_n/L.
The probability of any such pair is at most

    nL (L^alpha/(epsilon^alpha n))^2=O_{epsilon,L}(1/n).
                                                               (7.2)

Thus their components are disjoint with probability tending to one.
For disjoint components put b_e=u_e/sqrt(t_e). Their Gram matrix
in the m-inner product has diagonal one and, for e!=f,

    <b_e,b_f>_m
       =-sqrt(s_es_f)/(M sqrt((1-s_e/M)(1-s_f/M))),
    |<b_e,b_f>_m|<=L/(M-L).                            (7.3)

The nonzero spectrum of sum_large w_e b_e tensor_m b_e is that
of D^{1/2}G D^{1/2}, D=diag(w_e), G this Gram matrix. Its distance
in operator norm from D is at most

    max_e w_e J L/(M-L).                               (7.4)

After division by a_n this tends to zero, since J and max w_e/a_n
are tight. Thus, outside the exceptional events in (7.1),(7.2), the
large-bridge operator norm differs from the largest large w_e by
o_P(a_n).

Small bridge weights have a vanishing trace after epsilon decreases.
The exact Pareto integral, or direct integration of its density, gives

    E[w_e 1_{w_e<=epsilon a_n} |map]
       <=alpha/(1-alpha) (epsilon a_n)^{1-alpha}t_e^alpha.

Consequently

    limsup_n E[a_n^{-1}sum_{w_e<=epsilon a_n}w_e]
          <=C epsilon^{1-alpha},                      (7.5)

by the expected-value version of (6.1). Its operator norm is at most
its trace. The whole inverse K is the positive sum (4.1), so
||K||>=W_n. Combine (5.4),(7.1)--(7.5), take n to infinity,
then L to infinity at fixed epsilon, and finally epsilon down to zero.
This proves

    (tau_n-W_n)/a_n ->0 in probability.                 (7.6)

For explicit error bookkeeping, the probability of an error greater
than eta is bounded in limit superior by the right side of (7.1)
plus C eta^{-1}epsilon^{1-alpha}; all other errors vanish for fixed
epsilon,L. This validates the order of limits. Equations (6.3),(7.6)
give F at every x>0, completing the proposed proof with its original
quantifiers.

## 8. Contribution comparison and limitations

The initial ordinary-walk lane was screened out as technical: its
bounded resistance labels fall within the source's `tree:paths`, with
a standard resistance-process theorem left to assemble. F instead
concerns unbounded all-edge disorder and a localized lowest mode.
Metric CRT convergence alone gives neither (5.4) nor (7.6).

The source's block representation, finite variance, corner masses and
classical cyclic conditioning are credited. Janson's Remark 5.3
already supplies the general expectation/quenched truncation principle
behind Lemma 3.1. Our explicit proof is not a novelty claim for that
principle. The task-specific estimate is Lemma 3.2 and its use with
the arbitrary-block two-path gain (5.1): it pays nonbridge operator
tails with only the actual second offspring moment. Replacing that
moment by a third or an exponential moment would not prove F.

Flegel's [principal localization paper](https://arxiv.org/abs/1608.02415),
Theorem 1.8 and Corollaries 1.10--1.11, proves localization and a
Weibull minimum law on lattice boxes with Dirichlet boundary. Her
[higher-mode paper](https://arxiv.org/abs/1801.05684), main theorem
and Corollary 2.3, extends it to the first k modes. Spectral extremes
and separation of exceptional traps are established ideas. Their
lattice objects are minima of incident-conductance sums at sites;
here bridge traps carry an unbounded random branch mass. The exact
moment E|T|^alpha in K includes every finite branch size, not only
leaves. Our positive inverse-block decomposition and fringe-tail
payment replace lattice percolation/Poincare and local-speed-field
estimates. No operation-level reduction from those lattice statements
to F has been supplied by this bounded screen.

The pinned q=2 FK spectral and walk companions and the spanning-tree
walk companion have unit conductances and a surface diffusion limit;
their exact model statements do not assert F. Feng's infinite-volume
q>4 geometry is credited separately. A geometric CRT limit is not
claimed new here. Primary-literature reading limits and the precise
search strings are in `literature-screen.md`. The screen is bounded:
**no worldwide novelty or SUBSTANTIAL review verdict is claimed**.

The theorem is proposed for independent mathematical and contribution
review as one package. The current author believes the weighted-fringe
and cyclic-block spectral bridge is a substantive candidate, but a
review may judge an older general theorem to pay it. No supporting
lemma or corollary is separately nominated. No claim of a path limit,
all-eigenvalue point process, aging, critical alpha law, or uniform-q
estimate is added.

## 9. Supporting checks and handoff

`checks.py` uses exact rational linear algebra and finite ordered
trees. It checks inverse-block decompositions (including loops,
parallel edges, nested attachments and nonuniform masses), bridge
normalization, the PSD trace bound, the corner mass S=2e+1, the cyclic
fringe expectation identity, the two-window conditioning factor, the
forest coefficient identity, and the disjoint-cut Gram identity.
Deliberate wrong normalizations and adjacency choices are detected.
The stored receipt is not a proof of the asymptotic estimates or F.

`verify.py` authenticates the externally supplied detached seal hash,
the two SHA256/size inventories, every inventoried byte and exact
membership **before** executing any stored checker. It also verifies
all pinned source blobs against the copied tree entries. Replaying
uses Python -B and compares stdout byte for byte with the frozen
receipt. It writes no inventories, receipts, caches or other files,
including on failure. Mutation tests run only in disposable copies
inside this directory and remove those copies before the freeze.

Source truth is stipulated; new deductions are mathematical arguments
above. Computations are self-checks, not independent proof review.
Parent integration, separate proof and contribution gates, and any
later manuscript/formalization decisions remain outstanding.
