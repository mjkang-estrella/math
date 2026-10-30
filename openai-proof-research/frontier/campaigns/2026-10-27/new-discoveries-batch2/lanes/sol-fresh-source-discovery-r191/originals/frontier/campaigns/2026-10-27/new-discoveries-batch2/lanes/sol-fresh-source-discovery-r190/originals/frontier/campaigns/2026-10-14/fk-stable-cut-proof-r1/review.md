# Independent mathematical proof audit r1 — full stable CRT cut operator theorem G

Reviewer role: independent proof sub-agent. Date: 2026-10-16.
Author of the candidate: Myeongjin Kang; no affiliation.
Original review prose: CC BY 4.0. Original diagnostic code: MIT.
Private third-party material retains its existing rights.

## Verdict and scope

**PROOF PASS for the entire original G. No blocking gap or counterexample was found.**

This verdict concerns the frozen `fresh-analytic-discovery-r9/candidate.md`,
38,644 bytes, SHA256
`5c339f83efac52d43965a400ac6b693bb52100475e8ccddcd8ad490897567144`,
against the full frozen `original-scope.md`, SHA256
`d8686a39d756a2aee505382600106c0aa6f821f5a9496016767752038ab634a6`.
Candidate line references below refer to that exact file, numbered 1–737.
The review reconstructs the important arguments rather than accepting the
author's conclusion or a finite checker receipt.

The passed scope is: every fixed real q>4; every fixed alpha in (1/2,1);
all integer map sizes n tending to infinity; the exact spherical FK law
proportional to q^{k_M(A)+(|A|-|V(M)|)/2}; loops and parallel edges retained;
independent alpha-Pareto resistances on every edge; original degree speed
measure, including both darts of every loop; and only the actual finite
second offspring moment. Constants need not be uniform in q or alpha.

Put M=2n, N=M+1, b_N=N^{1/(2alpha)}, and let U_n use the nonroot preorder
cells specified in the frozen scope. The passed assertion is the joint limit

    (sigma H_{Nt}/(2 sqrt N), (M b_N)^(-1) U_n K_n U_n*)
        => (e, K)

in C[0,1] times the trace norm on self-adjoint trace-class operators on
H0=L²_0[0,1]. Conditional on the same excursion e, the operator is

    K = sum_(x,r) r (u_x tensor u_x),
    u_x = 1_(I_x) - |I_x|,

with Poisson intensity

    (p_2/sigma) ell(dx) alpha r^(-alpha-1) dr.

The a.s. construction, positivity, trace class, nonzero property, injectivity
on all H0, inverse and form domains, and finite positive nonconstant top
eigenvalue are included in the PASS. So is the exact inverse-gap consequence

    n^(-1-1/(2alpha)) tau_n => 2^(1+1/(2alpha)) ||K||.

No endpoint, subsequence, extra moment, bounded-block condition, changed
clock, tree-only or bridge-only model, largest-cut proxy, or scalar-only
replacement was used. No resistance-metric or process convergence was needed.

**Contribution is unassessed by this review.** Proof success supplies no
SUBSTANTIAL, novelty, priority, acceptance, or count verdict. The campaign
count remains 4/10 for purposes of this work. Historical F remains proof
PASS / contribution TECHNICAL, with its prior-work credit and parent
corrections intact. In particular, the false universal tree-gap comparison
and unqualified transfer to arbitrary decorated families are not premises.

## Authentication and source contracts

The working/output directory is exclusively `fk-stable-cut-proof-r1/`.
The candidate directory and all other inputs were read only. Before any
stored diagnostic execution, an independently written inline hash-only
bootstrap authenticated the external candidate seal

    13658895e2242a0eb3ecbed3f1910345666d10afc83de4d32befe9a9647585c4.

It checked both bound manifests, sizes and SHA256 of all 111 inputs and
19 outputs, exact 134-file package membership including its four inventory/
seal files, the detached seal text, and the separately supplied candidate
hash. All 13 copied upstream files were independently matched by Git-blob
SHA1 to entries of the full, nontruncated `preprints-tree.json`. The preserved
F seal also matches
`80f72efab2af1c25bb440a49fcaacd5410601d328b83c0f59055be65958ae7bc`.
See `authentication.json` for the exact blob paths, sizes, SHA256 and SHA1.

No candidate `checks.py`, `verify.py`, or mutation-test code was executed.
The only stored code executed was this review's newly authored
`diagnostics.py`, after authentication. Its finite receipt is not proof of
any limit. The frozen source's truth was stipulated; its upstream proofs
were not subjected to a truth audit.

The immutable OpenAI revision is
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. For the principal source define
the pinned prefix

    https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Brownian-continuum-random-tree-limits-of-finite-Fortuin-Kasteleyn-maps-above-four-September-24-2026/build/

The following actual contracts were inspected, not inferred from an abstract:

| Source and lines | Accepted contract and use |
|---|---|
| `main.tex` 70–98 | Exact finite law, degree probability measure, two loop darts, and excursion metric d_e. |
| `sections/blocks.tex` 19–89, 186–231 | Blocks are a singleton loop or loopless connected nonseparable maps, including a link; exact ordered corner substitution; p_{2m}=b_m v^m/Phi(v); E xi=1 and 0<sigma²<infinity; independent block marks given offspring; conditioned size N=2n+1; all odd sizes attainable. |
| `sections/trees.tex` 15–52, 103–138 | Exact even-offspring assumptions, preorder heights with H_N=0, joint coding limit with height coefficient sigma/2, Otter–Dwass and span-two uniform local limit. |
| Same file 143–203, 232–280 | Spine law P_sp(k,i,B)=p_k L_k(B), and the uniform bounded/offspring-bounded path theorem. Only a bounded 0–1 label is used here. |
| `sections/metric.tex` 92–115 | Uniform nonroot-node mass pushes exactly to degree/(2n), including loop and multiple-corner contributions. |

The source's block mark is a map marginal, which is sufficient because the
operator depends only on the map and added independent resistances, not A.
For a one-edge link the two FK subset weights sum to q+sqrt(q); the same is
true for a one-edge loop. Thus their conditional probabilities at k=2 are
exactly 1/2 each. A link has exactly one corner opposite its pole. This also
checks the thinning directly from the original finite law.

The source's ordinary metric constant beta is not substituted for sigma.
No source bounded-path theorem is applied to an unbounded resistance.

## Section 3: independent conditioning and tail reconstruction

Candidate lines 121–197, equations (3.1)–(3.6), pass.

Let Y=xi-1, S_m=sum_{j<=m}Y_j, a_m(z)=P(S_m=z), a_0(0)=1, and
pi_s=P(|T|=s). The accepted uniform lattice local limit, with finitely many
small indices absorbed, implies

    sup_z a_m(z) <= C/sqrt(m+1),
    a_N(-1) >= c/sqrt N,    pi_s <= C s^(-3/2).

Incompatible parities give zero probabilities, not new constants. Since
p_0p_2>0, every odd N is attainable, so these estimates cover every n.

For a nonnegative marked fringe toll f, circular-window counting in an iid
offspring list conditioned on total increment -1 gives exactly

    E sum_v f((T_N)_v)
      = (N/a_N(-1)) sum_{s<=N} E[f(T); |T|=s] a_{N-s}(0).

A length-s tree word has increment -1; its independent complement must have
increment zero. Circular rotation selects the unique full tree word. At
s=N there is one root window in the valid tree rotation; its contribution
is E[f(T_N)] as required. There is no lost or artificially independent root
term. Offspring-dependent node marks can be carried with their entries.
This agrees with Janson's actual cyclic representation and Lemma 5.1.

For f(T)=|T|^a, a>1/2, the resulting upper bound is

    C N^(3/2) sum_{s<=N} s^(a-3/2)(N-s+1)^(-1/2)
       <= C_a N^(a+1/2).

To check both endpoints independently, split at N/2. On the first half,
the second factor is O(N^(-1/2)) and the sum of the first factors is
O(N^(a-1/2)). On the second half the first factor is O(N^(a-3/2))
and the remaining sum is O(sqrt N). The single root contribution itself
is N^a. If s<=delta N<=N/2, the conditioning ratio is bounded and the
same calculation gives the sharper bound

    E sum_{|T_v|<=delta N}|T_v|^a
       <= C_a delta^(a-1/2) N^(a+1/2).

For the selected-child identity, let F_j be the total size of j independent
unconditioned trees, with F_0=0. Because Y>=-1, any path ending at -j
must first hit -j. Exploration of a forest of j trees is exactly that
first-passage segment. The strong Markov property therefore gives, for all
m,j>=0,

    sum_{t=0}^m P(F_j=t) a_{m-t}(0) = a_m(-j).

For j=0 this is the empty-forest identity. This formula is exact even when
m=0. It needs no forest asymptotic, exponential moment, or near-N cutoff.

Apply the cyclic formula to the toll g(k)sum_i F(|T_i|). Select the first
child, multiply by k by exchangeability, and fix its size s. The root and
other children consume 1+t nodes. The remaining factors are

    (N/a_N(-1)) F(s) pi_s k p_k g(k)
       times sum_t P(F_{k-1}=t) a_{N-1-s-t}(0).

The convolution just established proves exactly candidate (3.5):

    E sum_v g(k_v)sum_{w child}F(|T_w|)
      = (N/a_N(-1)) sum_{s<N}F(s)pi_s
                       sum_{k>=1}k p_k g(k)a_{N-1-s}(1-k).

When m=N-1-s=0, only k=1 could contribute; the source has p_1=0.
For the actual largest possible child size N-2, m=1 and the k=2 residual
term is a_1(-1)=p_0. Thus the boundary is retained rather than bounded by
an unjustified constant asymptotic.

For F(s)=s^a, the uniform bound with m+1=N-s gives

    E sum_v g(k_v)sum_{w child}|T_w|^a
      <= C N^(3/2) E[xi g(xi)]
                    sum_{s<N}s^(a-3/2)(N-s)^(-1/2)
      <= C_a N^(a+1/2) E[xi g(xi)].

The beta sum is paid by the same two-half calculation above. In particular
g(k)=k 1_{k>K} costs E[xi²;xi>K], which vanishes under finite second
moment. No k³ moment is hidden. All rearrangements use nonnegative terms;
the tail application averages resistance marks before using this identity.
No independence between nested fringes is asserted or needed.

## Section 4: interval locations, finite boundaries, and tightness

Candidate lines 199–303, equations (4.1)–(4.6), pass with the explicit
boundary interpretation given here. This is convergence of interval
locations, not just convergence of subtree masses.

For a nonroot node w of preorder index l, write r=l+|T_w| and d=H(w).
Its complete subtree occupies indices [l,r). If w is nonleaf, then

    H_l=d, H_(l+1)=d+1,
    H_j>d for l<j<r, and H_r<=d,

where the terminal value H_N=0 is appended. Consequently the component of
the linearly interpolated {H>d} containing any proper descendant starts
at l/N and ends inside [(r-1)/N,r/N]. The full subtree-cell interval differs
by at most an endpoint cell. Omitting w adds at most one cell at the left.
Leaves have no proper-descendant component; a leaf on a sampled ancestral
path can only be its final self term. Removing that term changes a bounded
path sum by at most its supremum.

In particular this proof does not identify preorder with a contour walk:
descents may have arbitrarily many integer height units. The largest
rescaled height jump tends to zero by continuous-path tightness of h_N.
Replacing all N preorder cells by the M nonroot cells moves time coordinates
by at most 1/N. The sampled cell's corresponding source time also tends to
the same t. These facts justify using the limiting excursion rather than
assuming an exact continuous coding by the finite preorder interpolation.

For a continuous excursion h and h(t)>z, denote by I_h(t,z) its component
of {h>z}. Its left endpoint is nondecreasing and right endpoint
nonincreasing as z increases. For fixed t both have only countably many
discontinuities. If h_j converges uniformly to h, z_j tends to z, and
t_j tends to t, then at a continuity level the component containing t_j
is squeezed between the components at z-epsilon and z+epsilon. Indeed a
small neighborhood of t remains strictly above the relevant levels, so
the component choice is stable under the moving sampling time. Letting
epsilon decrease proves convergence of both endpoints. The finite boundary
calculation above transfers this statement to discrete ancestors with
depth times sigma/(2 sqrt N) tending to z. Fubini removes the countably
many exceptional levels for a.e. t. The boundaries z=0 and z=e(t) are
also null for this two-dimensional integration.

The cut label b_w is the incoming-edge label determined by the parent
link and the opposite-pole corner. Under the accepted spine law,

    theta = sum_{k,i}p_k E[b(k,i,B)] = p_2/2.

The factor 1/2 is not doubled by the two children: only one opposite
corner is selected. The source's bounded path theorem gives the maximum
absolute centered partial path sum D_N=o_P(sqrt N), simultaneously for
every node and hence every prefix of every ancestral path.

Let phi be Lipschitz and zero on s<=delta, and F(a,b)=phi(a,b)/(b-a),
extended by zero near the diagonal. This is globally Lipschitz on the
interval triangle. The exact descendant-counting identity is

    sum_w b_w phi(I_w)
       = integral_0^1 sum_(w ancestor-or-self of v(t)) b_w F(I_w) dt.

Along a path, left endpoints increase and right endpoints decrease; total
endpoint variation is at most two. Thus F has uniformly bounded variation
on every path. If C_j=sum_{i<=j}(b_i-theta), Abel summation bounds the
weighted centered sum by

    max_j |C_j| ( ||F||_infinity + Var_path F ) <= C_phi D_N.

The incoming-edge/self conventions are compatible with D_N; replacing the
last self or root term in an unmarked path sum costs one bounded term.
This pays the thinning without independent assumptions about nested cuts.

Now use depth mesh Delta z=sigma/(2 sqrt N). The endpoint result makes
the bounded ancestor step function converge for a.e. (t,z) to
F(I_e(t,z)) below e(t). Under a uniform coding coupling the maximum
rescaled height is bounded. Dominated convergence, not a finite check,
gives the path integral limit with coefficient 2/sigma. Coarea on the
tree then gives

    integral dt integral_0^{e(t)}F(I_e(t,z)) dz
       = integral s_x F(I_x) ell(dx)
       = integral phi(I_x) ell(dx).

One can verify coarea on finite reduced subtrees arc by arc. An increasing
union of root paths to a countable dense set covers the skeleton; Tonelli
extends it, with signed tests handled by positive and negative parts.
This yields precisely c_q=(2/sigma)(p_2/2)=p_2/sigma.

For every delta>0, length on s>=delta is at most
delta^(-1) integral s_x ell(dx)=delta^(-1) integral e(t)dt. Discretely,
the number of intervals of mass at least delta divided by sqrt N is
bounded by delta^(-1) N^(-1/2) sum_w s_w, with bounded expectation by
(3.3) at a=1. Interval space away from its diagonal is compact. This pays
tightness of the locally finite measures. A countable determining class
of cut-away Lipschitz tests gives random-measure convergence, jointly with
h_N. A subsequence coupling of (h_N,D_N/sqrt N) has limit (e,0), and the
same deterministic argument applies on every such coupling; this proves
the full sequence result rather than choosing a preferred subsequence.
The endpoint maps are measurable hitting-time maps of a continuous coding
function, so the coarea construction also provides a measurable random
intensity kernel. Generic deterministic mass cutoffs decreasing to zero
can be chosen to avoid limiting boundary atoms a.s.

## Sections 5–6: Poisson construction and trace-norm convergence

Candidate lines 305–449, equations (5.1)–(6.8), pass. The two infinite
trace tails and the large-mark remainder are all paid.

First remove the link label in the preceding argument. The normalized
unmarked interval measure with coefficient sigma/(2 sqrt N) converges
locally to skeleton length pushed to intervals. Equations (3.3) and M=N-1
give a uniform expectation bound on its s^alpha integral. Apply local
convergence to continuous cutoffs below s^alpha. The nonnegative expectation
lower bound under weak convergence, followed by monotone convergence,
proves

    E integral s_x^alpha ell(dx) < infinity.

This implication is independently sufficient; it does not assume stronger
moment convergence from a literature theorem. In particular for
t_x=s_x(1-s_x), J_e=integral t_x^alpha ell(dx) is finite a.s. It is positive:
choose two distinct leaves, and a positive-length arc toward one
above their last common ancestor. At regular points its cuts have positive clade
mass and positive complementary mass by full support. Branch points and
endpoints have zero length measure.

The skeleton is a countable union of finite root arcs. Together with
r-intervals bounded away from zero and infinity, this makes the proposed
Poisson intensity sigma-finite. The required integrability test is exactly

    integral ell(dx) integral_0^infinity
        (1 wedge r t_x) alpha r^(-alpha-1) dr = J_e/(1-alpha).

After multiplication by c_q, the intensity of terms with r t_x>1 is finite,
and the expected sum of terms with r t_x<=1 is finite. Therefore the sum
of all r t_x is finite a.s. Each positive rank-one has trace norm r t_x,
so the series converges absolutely in trace norm and defines a positive
trace-class operator on the entire H0. This construction does not infer
operator existence from a scalar limiting distribution. The conditional
trace Laplace exponent is correctly

    c_q Gamma(1-alpha) z^alpha J_e.

For finite restrictions s>delta and epsilon<r<L, condition on the marked
map tree before revealing bridge resistances. These resistances are
independent variables attached to distinct original bridge edges. Their
scaled density is exactly N^(-1/2) alpha r^(-alpha-1) dr on the restriction
once b_N epsilon>=1. Hence the conditional product in (6.2) is exact.
The sum of its subtracted terms converges by the joint interval-measure
limit. Their maximum is O(N^(-1/2)); thus the total logarithm error is at
most this maximum times a tight sum, tending to zero in probability.
Multiplying by bounded continuous excursion tests identifies the Cox limit
conditional on the same e. Local count tightness and a determining class
of Laplace tests give joint marked point-measure convergence.

No independence of cut locations, selected-child labels, or nested fringes
is used. Independence enters this Poisson product only for the newly added
Pareto resistances conditional on the whole map tree.

The map from a bounded mark and interval to its rank-one operator is
trace-norm continuous. Indeed

    ||u_I-u_J||_2 <= |I symmetric-difference J|^(1/2),
    ||u tensor u - v tensor v||_1
         <= (||u||_2+||v||_2)||u-v||_2.

The first inequality follows because centering is an orthogonal projection.
On each finite restriction the count is finite and its boundary has zero
limiting mass. Finite sums therefore converge in trace norm. This verifies
(6.3) as an operator assertion, rather than merely a claim about individual
Rayleigh quotients.

Here is an independent accounting of the complete remainder:

1. **All resistances on small subtrees.** For Pareto R,
   E[1-exp(-zR)]<=C_alpha z^alpha. The inequality
   1-exp(-sum y_i)<=sum_i(1-exp(-y_i)), followed by the exponential
   Markov bound, gives

       P( sum_(s_w<=delta) b_w (R_w/b_N)t_w > eta )
          <= C_alpha eta^(-alpha) N^(-1/2)
                                      E sum_(s_w<=delta)s_w^alpha
          <= C_alpha eta^(-alpha) delta^(alpha-1/2).

   The M-to-N conversion is bounded uniformly for n>=1. The last estimate
   is (3.4) at a=alpha. It controls the trace of the sum, including arbitrary
   large resistance marks on these subtrees. The positive exponent is
   exactly where the strict lower endpoint alpha>1/2 is used.

2. **All subtree masses with small marks.** Direct integration gives

       E[(R/b_N)1_{R/b_N<=epsilon}]
           <= alpha/(1-alpha) epsilon^(1-alpha) N^(-1/2).

   Since t_w<=s_w and N^(-1/2)E sum_w s_w is bounded, the total truncated
   trace has expectation O(epsilon^(1-alpha)). This is an unconditional
   truncated expectation; no conditioning on absence of large marks occurs.

3. **Very large marks on retained masses.** A union bound gives

       P(exists s_w>delta, b_w=1, R_w/b_N>L)
          <= C L^(-alpha)/delta.

   This probability suffices. No finite first moment of those large-mark
   traces is asserted.

For the limiting Poisson operator, the corresponding small-mass bound is
controlled by integral_{s<=delta}t_x^alpha ell(dx), whose expectation
tends to zero by (5.2) and dominated convergence. Small-r expected trace is
c_q alpha/(1-alpha) epsilon^(1-alpha) integral t_x ell(dx), of finite
mean. The retained large-r probability is bounded by c_q L^(-alpha)
times the finite length on s>delta, with mean O(1/delta).

Choose delta, then epsilon, then L with delta fixed, and only then pass to
the finite-restriction limit. The probability/expectation errors vanish in
that order for every fixed eta. The converging-together argument in the
separable trace-class Banach space, with the common excursion coordinate,
proves (6.8). Tightness is supplied by these finite approximations and
trace tails; bounded total traces alone would not have sufficed. Interactions
between all retained nested cuts remain present.

## Section 7: exact Hilbert normalization and all cyclic blocks

Candidate lines 451–543, equations (7.1)–(7.7), pass. This argument was
checked independently, including the finite-second-moment payment.

Ground each block potential at its pole and extend it constantly into all
exterior components. For another block's potential, both ends of any edge
of the first block have the same value. Energies are therefore orthogonal
across blocks. Conversely the successive articulation-block differences
reconstruct every global potential modulo constants. If J denotes the
direct-sum extension, its adjoint from the degree inner product into energy
satisfies

    E(JJ* g, f)=<g,f>_m.

This proves K_n=JJ*=sum_B K_B with K_B>=0; it does not use an unweighted
matrix transpose. A singleton loop has no potential degree of freedom,
but all its darts remain in m. Finite-dimensional traces are independent
of multiplying the entire vertex inner product by the constant 1/M.

For an energy-orthonormal basis in a grounded block, squared evaluation
norm at x is its effective resistance from the pole. Subtracting the global
mean contracts the degree norm, so

    Tr K_B <= sum_i S_i R_B(o_B,x_i).

To verify the mass allocation, each corner contributes its one parent-block
dart plus S_i-1 darts of its inserted map. Distinct corners allocate distinct
darts even if they share a physical vertex. Mass outside the block's
descendant inserts projects to its pole, where the grounded evaluation is
zero. There is neither lost pole mass nor double-counted nonpole mass.

For a bridge, its opposite corner has exactly one child subtree. The far
component's unnormalized degree mass is exactly S=M s, including the far
bridge dart. A unit-energy basis is sqrt(R) times its uncentered far-side
indicator. Thus

    K_B = R (1_A-s) tensor_m (1_A-s).

The tensor for <.,.>_m is M times the tensor for probability measure m/M.
U_n is an isometry for the latter measure, and U_n(1_A-s)=u_(I_w).
Division by M b_N therefore gives exactly (R/b_N)u_(I_w) tensor u_(I_w).
This proves the factor M in (G); using tensor_m without this conversion
would produce the wrong limit. On H0 the adjoint U_n* has degree mean
zero, so the extension by zero introduces no unresolved constant mode.

Every cyclic nonloop source block is bridgeless: a bridge in a loopless
nonseparable connected graph forces it to be the singleton link. Choose
two edge-disjoint pole-to-x paths from the shape before exposing their
resistances. If their lengths are l_1,l_2, then l_1+l_2<=k/2. Their
resistance sums are independent, even if the paths meet at some vertices.
Thomson gives R_B(o,x)<=min(U_1,U_2). Union and truncated first-moment
bounds give P(U_j>t)<=C_alpha l_j t^(-alpha), t>=1. Therefore

    P(min(U_1,U_2)>t)
       <= min(1, C_alpha² l_1 l_2 t^(-2alpha)),
    E[R_B(o,x)^alpha | B] <= C_alpha sqrt(l_1 l_2) <= C_alpha k.

Integrating alpha t^(alpha-1) establishes the last inequality, including
the t<1 part. Parallel-edge blocks are covered; at x=o the resistance is
zero. No uniform first effective-resistance moment is used.

Let Z_{v,i} be this corner resistance on cyclic blocks and zero otherwise.
Condition on the whole unmarked tree and block shape, then average the
resistances. Their laws are independent of every child subtree size; this
is valid under total-size conditioning because the added resistances and
conditional block marks do not determine offspring counts. The several
Z's within a block need not be independent, and neither do nested tolls.
For fixed offspring cutoff K, finitely many rooted block shapes give

    d_(K,L)=max_(k<=K,B,i)E[Z_(v,i)^alpha;Z_(v,i)>L | B] -> 0.

For k>K the same expectation is bounded by C_alpha k. Bounded prices
contribute at most

    L sum_(v,i) S_(v,i)
       = L sum_(w nonroot)|T_w|
       = L sum_v H(v) <= L N max_v H(v) = O_P(L N^(3/2)).

After division by M b_N this vanishes for fixed L, because
1/2-1/(2alpha)<0 when alpha<1.

For the unbounded-price part, subadditivity of x^alpha, averaging marks
first, and the selected-child estimate proved above give

    E[( (M b_N)^(-1) sum_(v,i) S_(v,i)Z_(v,i)1_{Z_(v,i)>L})^alpha]
      <= (M b_N)^(-alpha)
          E sum_(v,i)S_(v,i)^alpha
                [d_(K,L)1_{k_v<=K}+C_alpha k_v1_{k_v>K}]
      <= C_alpha[d_(K,L)E(xi;xi<=K)+E(xi²;xi>K)].

Here (M b_N)^alpha=M^alpha sqrt N is comparable to N^(alpha+1/2).
The first use of the selected-child identity takes g(k)=1_{k<=K};
the second takes g(k)=k1_{k>K}. This independently reconstructs (7.6).
In particular, one does not bound each forest factor separately in a way
that introduces an extra k. Markov, first N at fixed K,L, then L at fixed
K, then K, proves full cyclic trace negligibility. Positivity makes that
trace exactly its trace norm. All original cyclic-edge resistances have
been paid; none were removed from the finite model.

Together with the bridge limit this proves full trace-norm convergence of
the normalized original inverse generator. No deterministic tree-gap bound
or largest-bridge equivalence enters this argument.

## Section 8: simultaneous injectivity, domains, and inverse-gap law

Candidate lines 545–632 pass. In particular the Hilbert space is all H0,
not an unnoticed proper pullback subspace, and injectivity holds on one
probability-one event simultaneously for all g.

Fix a realization of the CRT with the standard binary, nonatomic
leaf-mass properties. Its length measure ignores leaves and the countable
branch-point set. Choose countably many dense leaves; their root paths
cover the skeleton. Indeed any strict ancestor has a descendant open ball,
which contains a point of the chosen dense set. On each such root path use
countably many rational arc subintervals. Every nonempty such subinterval
has positive finite length. Conditional on e, its Poisson intensity over
all r>0 is infinite at r=0. The probability of no mark is zero, as follows
also by restricting to r>epsilon and decreasing epsilon. A countable
intersection ensures marks in all these intervals, while all marks avoid
branch points. This is the single event used below.

At a nonbranch interior point x of an arc, the clades of nearby points on
the arc differ only by sets whose mass tends to zero. Approaching from
below leaves in the intersection at most x and branches exactly at x;
approaching from above gives the analogous union. The latter branches are
absent at a regular point, and mu({x})=0. Thus u_y tends to u_x in L²(mu).
The marked span consequently contains every regular cut on these root
paths, and hence all regular skeleton cuts. This uses density of the actual
random mark set, not a fixed-g probability calculation.

Choose a countable dense set of regular cuts on each path. They separate
every pair of distinct leaves: use a regular point above their last common
ancestor toward one of them, and then a nearby cut from the countable
family. Clades are Borel and laminar, so their indicator span with constants
is an algebra. A countable separating Borel family generates the standard
Borel leaf space, for example by its injective membership map into
{0,1}^N and the Borel isomorphism theorem. The leaf set is Borel; it is the
complement of a countable union of half-open root arcs covering the
skeleton. The monotone-class/density theorem therefore gives all L²(mu).
After centering, regular cuts have dense span in L²_0(mu). This conclusion
separates the entire leaf support, not merely a countable dense subset.

The source excursion quotient has a.e. injective time coding. To check it
directly, suppose t<u code the same point x, so e(t)=e(u)=min_[t,u]e=h.
If e rises above h between them, x has a strict descendant and is not a
leaf. If it does not, the whole interval codes x and mu has an atom of
mass at least u-t. Neither alternative is possible for the nonatomic
leaf-supported mass, as given by Aldous CRT III Section 2.3 and Corollary
22, rescaled from 2e to e. The time set coding leaves has full Lebesgue
measure, is Borel, and its continuous coding map has a Borel inverse on its
image. Pullback is therefore onto L²[0,1] modulo null sets. The dense span
just proved really transfers to all H0. Full support follows also from
continuity and surjectivity of the quotient map.

On the same event, for any g in H0, including a mark-dependent g,

    <g,Kg> = sum_(x,r) r |<g,u_x>|².

The trace-norm series justifies this equality. If it is zero, every
summand is zero, and the deterministic dense-span conclusion forces g=0.
This proves injectivity simultaneously, with no uncountable intersection
of fixed-g probability-one statements.

The compact positive spectral theorem now gives an orthonormal eigenbasis
(f_j), eigenvalues kappa_j>0 tending to zero, and sum_j kappa_j<infinity.
Injectivity of the self-adjoint K also makes Ran K dense. Spectral calculus
gives precisely the self-adjoint inverse and its closed form:

    D(A) = {f:sum_j |<f,f_j>|²/kappa_j²<infinity} = Ran K,
    Af = sum_j kappa_j^(-1)<f,f_j> f_j;

    D(Q) = {f:sum_j |<f,f_j>|²/kappa_j<infinity} = Ran K^(1/2),
    Q(f) = sum_j kappa_j^(-1)|<f,f_j>|².

The compactness gives a finite top eigenvalue, strictly positive since K
is nonzero. More strongly, conditional on e, the intensity of marks with
r t_x>R is c_q R^(-alpha)J_e. Its probability of being nonempty is
1-exp(-c_q R^(-alpha)J_e)>0 for every R>0. Such a rank-one term forces
||K||>R by positivity. Thus the finite positive norm has unbounded support
and is nonconstant; a scalar trace law alone is not used to conclude this.

Operator norm is continuous for trace norm. Finally

    (M b_N)/n^(1+1/(2alpha))
       = 2(2+1/n)^(1/(2alpha)) -> 2^(1+1/(2alpha)).

Since every n corresponds to an attainable odd N, continuous mapping and
this deterministic factor prove the original all-integer-n inverse-gap law.

## Objections and presentation notes

There are **no blocking objections and no original-scope mathematical repair
is required**. The following clarifications would make a later manuscript
more precise; none changes G or supplies a missing asymptotic hypothesis.

| ID | Candidate location | Severity | Clarification |
|---|---|---|---|
| P1 | Lines 254–262 | Nonblocking presentation | State the proper-descendant/nonleaf condition explicitly in the finite level-component sentence, then remove the self term by its bounded cost. For a leaf the component is empty. The exact endpoint calculation in this review explains the intended one-cell convention, including terminal H_N=0 and multi-level preorder descents. |
| P2 | Lines 555–558 | Nonblocking presentation | Use convergence of the symmetric-difference mass to zero, allowing a possible singleton and branches at x in the one-sided set limits. The literal set limit need not be the singleton from both directions. At regular x both yield the claimed L² continuity. |
| P3 | Lines 573–577 | Nonblocking presentation | Retain the valid Borel membership-map argument on the whole leaf support. Merely distinguishing a countable dense subset would not, by itself, justify the alternative sentence for an arbitrary compact measurable space. The regular-cut family here separates every leaf pair, which is sufficient. |
| P4 | Line 54 versus lines 45–46 and 358 | Typographic | Unify u and nu for the centered cut vector. The frozen scope and later definition remove any mathematical ambiguity. |

No assessment of general decorated-family transfer is issued. No universal
comparison between an inverse gap and the largest individual cut is used.
The candidate's nested-cut example is consistent with the full operator
limit and rules out replacing it by a maximum. Finite diagnostics cannot
repair a failed infinite-limit step; the PASS rests on the analytic bounds
and deterministic/probabilistic arguments above.

## Reading extents, finite checks, provenance, and seal

Reading extents for this review, distinguished from the author's readings:

* Read in full: current project AGENTS.md and upstream.json; frozen
  candidate.md (737 lines), original-scope.md (83), source-contracts.md
  (136), literature-screen.md (90), review-brief.md (43), working-math.md
  (70), and checks.py (117). The latter was inspected, not executed.
* Parsed the entire frozen full preprints tree and its 13 matched source
  paths; no truncated sources/tree.json was used. The large manuscript
  catalogue was used only for identification, not as a theorem premise;
  no full catalogue reading is claimed.
* Principal pinned source: main.tex 1–167, blocks.tex 1–237, trees.tex
  1–299, metric.tex 1–235, references.tex 1–111. All were read. This is a
  contract audit under accepted upstream truth, not re-verification of
  upstream word/ladder arguments. Other preserved upstream bodies were
  blob-authenticated but are not claimed read.
* Pinned companion statements: spectral FK–Ising introduction 1–222;
  FK–Ising walk introduction 1–90; spanning-tree walk introduction 1–125.
  Their actual finite models, generators and main statements were read.
  They concern q=2 or spanning-tree-weighted ordinary-conductance surface
  models. None was substituted as a theorem proving G. Their proof bodies
  were not read for this review, and no global duplicate/novelty conclusion
  follows from this bounded comparison.
* Aldous CRT III, preserved text lines 350–425, 1860–1910 and 1970–2010:
  continuum-tree definition, Corollary 22 and its normalization context.
  These are the actual primary statements used for nonatomic leaf mass.
  Source URL: https://www.stat.berkeley.edu/~aldous/Papers/CRT3.pdf .
* Janson 1312.1211v1, preserved text 595–785: local limit, cyclic identity
  (4.7), total-size formula, and Lemma 5.1. Source URL:
  https://arxiv.org/pdf/1312.1211v1 . The identity was also derived above;
  no F-regime integrable-toll LLN is imported into G.
* Fill–Janson 2104.02715v1, text 80–325: stated subtree-power limits,
  moment distinctions and the separate alpha=1/2 expectation. ADN
  2009.08185v1, text 100–225: Theorem 1.1 and discussion of length measures.
  URLs: https://arxiv.org/pdf/2104.02715v1 and
  https://arxiv.org/pdf/2009.08185v1 . These readings cross-check scale and
  credit; their later proofs were not read or used in place of Sections 4–6.
* No fresh literature search or global novelty certification was conducted.
  Other papers listed in the author's screen were not re-read for this proof
  gate. Historical F and the supplied parent corrections were respected;
  its verdict was not appealed or inferred anew from G.

All primary texts above were already present as authenticated private
inputs. No new download was needed. The complete original retrieval URLs,
sizes and hashes are preserved in the frozen source-retrieval and literature
records; `sources-read.json` records this review's actual extents and the
hashes of its primary text inputs, not the author's broader claims.

The independently authored diagnostic enumerates valid offspring words,
not the author's recursively generated tree tuples. It checked 126
selected-child equalities on 305 valid words, including a separate critical
law with unary offspring to probe zero remainders. It checked 1,252 nonleaf
preorder component boundary cases, including descents of height eight.
The frozen `diagnostics-receipt.json` reports finite support only. No
numerical experiment proves the beta bound, point-process convergence,
trace tails, CRT properties, or injectivity. No Lean proof is claimed.

`inputs-manifest.json` gives exact byte sizes and SHA256 for the entire
134-file read-only candidate package, plus the three current project
instruction/catalogue files read outside it. `outputs-manifest.json` gives
exact sizes and hashes of all reviewer payloads. `seal.json` binds both
inventories; `seal.sha256` is detached, and its SHA256 anchor is reported
in the terminal handoff. `verify.py --seal-sha256 HASH` checks the external
anchor first, both inventories, all bytes, and exact candidate/reviewer
membership without running candidate or diagnostic code or writing files.

Only this assigned review directory was written. No nested agents, sibling
or shared-index edits, staging, commits, uploads, submissions, external
messages, manuscript/Lean assets, acceptance changes, or count changes were
made. Parent integration and the separate contribution gate remain outside
this proof review.
