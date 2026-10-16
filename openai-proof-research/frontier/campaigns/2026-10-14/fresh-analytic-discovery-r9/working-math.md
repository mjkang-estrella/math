# Working mathematics after scope fixation

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

## 1. Exact selected-child conditioning identity

Write a_j(z)=P(sum_{i<=j}(xi_i-1)=z), pi_s=a_s(-1)/s, N odd.
For any nonnegative g on offspring and any nonnegative F on positive
integers, conjectured identity (to check exactly before using):

 E sum_{v in T_N} g(k_v) sum_{child w of v} F(|T_w|)
 = N/a_N(-1) sum_{s=1}^{N-1} F(s) pi_s
                    sum_{k>=1} k p_k g(k) a_{N-1-s}(1-k).       (W)

Derivation: cyclic fringe formula, choose one child and permute it first,
then sum over the total size t of the remaining k-1 GW trees. The convolution
sum_t P(F_{k-1}=t) a_{N-1-s-t}(0) equals a_{N-1-s}(1-k): a skip-free walk
ending at -(k-1) must first hit that level at some t; the remainder has sum
zero. This includes the empty-forest convention. It is not an asymptotic
replacement. LLT then gives, for a>1/2,

 E sum_v g(k_v) sum_w |T_w|^a <= C_a N^{a+1/2} E[xi g(xi)].

Thus g(k)=k 1_{k>K} costs ONLY E[xi²;xi>K]. No third moment.

## 2. Cyclic-tail route

For every nonlink/nonloop block, two independent edge-disjoint paths give
E[R_B(o,x)^alpha] <= C_alpha k (same elementary estimate as F).
For fixed offspring cutoff K, finitely many possible block shapes imply
max_{k<=K,i,B} E[R_B(o,x_i)^alpha;R_B(o,x_i)>L] ->0.
Grounded inverse-block trace is at most sum_{child i} S_i R_B(o,x_i).
Split corner resistance at L and offspring at K. Bounded corner terms cost
L sum_w S_w=O_P(L N^{3/2}), negligible relative to N b_N. The alpha moment
of all remaining terms, by concavity and (W), costs a constant times
E[xi²;xi>K] plus the finite-shape tail above. This would pay all cyclic
blocks without deleting their disorder.

## 3. Cut measure route

For each nonroot tree node w, let I_w be its preorder cell interval and
s_w=|I_w|. Let b_w indicate parent link and the opposite-pole child.
The fixed bounded label b has spine mean theta=p_2/2. Source tree:paths
therefore gives uniform centered cumulative sums o_P(sqrt N).
For a Lipschitz test phi(I) vanishing when |I|<delta,

 (1/sqrt N) sum_w b_w phi(I_w)
 = integral_0^1 dt (1/sqrt N) sum_{w ancestor of v(t)}
                             b_w phi(I_w)/s_w.

The weights along each path have uniformly bounded variation, because the
interval endpoints move monotonically, and 1/s is bounded on support.
Summation by parts removes b_w-theta with o_P(1). Uniform height convergence
then turns the sum into (2theta/sigma) integral ell(dx) phi(I_x).
The ancestor interval endpoints converge at a.e. (t,h), by monotonicity and
the sandwich between level h-epsilon and h+epsilon. Need pay cells at the
root/last node explicitly in final proof.

## 4. Spectral-tail route

Use the unweighted cyclic fringe identity to bound
E[(N^alpha sqrt N)^-1 sum_{|T_w|<=delta N}|T_w|^alpha]
 <=C delta^{alpha-1/2}. This is the strict alpha>1/2 threshold.
For any nonnegative coefficients c_w and Pareto R_w,
P(sum c_w R_w/b_N>eta) <=C eta^-alpha N^-1/2 sum c_w^alpha,
by 1-exp(-sum x)<=sum(1-exp(-x)) and the Pareto Laplace bound.
This pays small-mass bridge terms in TRACE, not maximum norm.
The trace of r<=epsilon terms has expectation O(epsilon^{1-alpha}), since
N^-1/2 E sum_w s_w=O(1). Finite remaining marks converge by their conditional
Laplace functional. Interacting cut rank-ones are retained in the limit.
