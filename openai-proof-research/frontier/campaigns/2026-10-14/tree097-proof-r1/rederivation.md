# Independent rederivation of every new step

Notation follows candidate.md. Source labels refer to the pinned source097
build files (assembly.tex, brownian.tex, introduction.tex), read in full.
lambda_Q(D) = inf over 0 != g in H^1_0(D) of int <Q grad g, grad g> / int g^2
(assembly.tex lines 11-22; NO factor 1/2; Brownian covariance rate 2Q).

## 0. Source contracts actually used (stipulated true)

- prop:adaptive (assembly.tex 32-50): K nonempty, bounded, open, convex,
  centrally symmetric, lambda_Q(K)<=kappa^2 trQ for EVERY positive definite
  diagonal Q; distinct axes j_1..j_s; q_i: R^{i-1} -> [-delta,delta]
  arbitrary. Then signs exist with x^(0)=0,
  x^(i)=x^(i-1)+(q_i(earlier assigned coords)+eps_i)e_{j_i}, x^(s) in K.
  Unlisted coordinates stay 0. kappa=1/100, delta=1/4.
- prop:filtered (60-87): d>=1, n>=0, C_t invertible, C_tC_t^T+b_tb_t^T=I;
  body D = {|x_j|<B_0, ||R_t x||<A_0 sqrt d, 0<=t<=n};
  lambda_Q(D)<=H_0 trQ, constants absolute.
- lem:slab-energy (95-108): lambda_Q((2D_*D) cap slabs) <=
  D_*^{-2} lambda_Q(D) + pi^2 delta^{-2} sum_i m_i Q m_i^T.
- Column bound (148-177): ||M e_{d+j}||^2 <= ||b_j||^2 <= sigma^2; initial
  columns zero; hence sum_i m_iQm_i^T <= sigma^2 trQ.
- lem:brownian-rate (brownian.tex 8-19): bounded nonempty open convex D,
  start at any x in D (0 if symmetric): survival exponent equals lambda_Q(D).
- lem:gaussian-path-correlation (73-88): centered continuous Gaussian
  process; events "A X(s) in K for all s in I" with K CLOSED symmetric
  convex, I closed; probability of intersection >= product.
- thm:signing (introduction.tex 10-20): d,N>=1, unit-ball vectors, one
  signing with all prefixes <= C sqrt d.

## 1. Intersection lemma

Let D,E be bounded open symmetric convex (nonempty, so 0 is interior to
both). For 0<a<1, cl(aD)=a cl(D) is contained in D, since 0 in int D and
D convex; same for E. Let W be Brownian motion of rate 2Q from 0.
P(W[0,T] in D cap E) >= P(W[0,T] in cl(aD) and in cl(aE))
>= P(W[0,T] in cl(aD)) P(W[0,T] in cl(aE))   [path correlation, closed sets]
>= P(W[0,T] in aD) P(W[0,T] in aE).
Apply -1/T log and T -> infinity, using lem:brownian-rate only for the
bounded open convex sets D cap E, aD, aE. Scaling the Rayleigh quotient gives
lambda_Q(aD)=a^{-2}lambda_Q(D). Hence
lambda_Q(D cap E) <= a^{-2}(lambda_Q(D)+lambda_Q(E)); let a -> 1. Correct.
This is the same pattern the source uses in its slab proof (brownian.tex
104-139), and it needs no closed/open rate equality.

## 2. Gaussian-body energy

K closed, bounded, symmetric convex in R^m, gamma_m(K)>=1/3.
a=Phi^{-1}(2/3), so P(|g_1|<=a)=1/3. If h_K(theta)<a for some unit theta,
K lies in {|<theta,x>|<=h_K(theta)}, of Gaussian measure 2Phi(h)-1<1/3:
contradiction. So h_K>=a everywhere and, K being closed convex,
aB_2 subset K (R1: the text says "width"; the support function is meant).
phi(x)=max(0,1-dist(x,K)/a) is (1/a)-Lipschitz, equals 1 on K, and is
supported in {dist<=a}=K+aB_2 subset K+K=2K. 2K is compact and contained
in int(3K)=3 int K (0 interior). g=phi sqrt(rho) is Lipschitz with compact
support in the bounded open convex set 3 int K, so g in H^1_0(3 int K).
int g^2 >= gamma(K) >= 1/3.
d_j g = sqrt(rho)(d_j phi - x_j phi/2), so
|d_j g|^2 <= 2 rho (d_j phi)^2 + (1/2) rho x_j^2 phi^2,
int <= 2/a^2 + 1/2 (|d_j phi|<=1/a a.e., phi<=1, E x_j^2=1).
Rayleigh quotient: sum_j Q_jj (2/a^2+1/2) / (1/3) = (6/a^2+3/2) trQ.
H_G=6/a^2+3/2 (about 33.84) is absolute. Correct with the source
normalization.

Reduction for DGLN bodies: DGLN (line 605) bodies are closed with nonempty
interior, possibly unbounded. For symmetric B with gamma(B)>=1/2,
K=B cap R*closedball has measure >=1/3 for R large, is closed, bounded,
symmetric, convex and lies in B. Correct.

## 3. Reserved slack and the fixed good set

Choose absolute D_*, sigma<1/2 with H_0/D_*^2+pi^2 delta^{-2} sigma^2 <=
kappa^2/2 (possible: increase D_*, decrease sigma). sigma<1/2 makes
C_i=(I-b_ib_i^T)^{1/2} invertible and C_i^2+b_ib_i^T=I (check: with
eta=(1+c)^{-1}, c=sqrt(1-|b|^2), -2eta+eta^2|b|^2=-1). Slab lemma plus
column bound: lambda_Q(K_0)<=kappa^2 trQ/2 for all Q.
R_{i-1}e_{d+i}=0, so R_iR_i^T=C_iR_{i-1}R_{i-1}^TC_i+b_ib_i^T=I_d by
induction from R_0R_0^T=I_d.
x(eps)=(0,z), z_i=eps_i+m_i(0,z): triangular, since m_i is supported on
coordinates d+1..d+i-1. Unique, linear and odd in eps, injective
(eps_i=z_i-m_i x). A_good={x(eps): x(eps) in K_0} is finite, symmetric
(K_0 symmetric), and defined from the input sequence only.

## 4. Hitting every Gaussian-half body (causal unclipping)

Fix any symmetric DGLN body B with gamma_m(B)>=1/2; K as in §2. Choose
absolute D_G with H_G/D_G^2<=kappa^2/2; E=3D_G int K is bounded, open,
symmetric, convex, lambda_Q(E)=lambda_Q(3 int K)/D_G^2<=kappa^2 trQ/2.
§1 gives lambda_Q(K_0 cap E)<=kappa^2 trQ for every Q; K_0 cap E is
nonempty, bounded, open, convex, symmetric. Apply prop:adaptive with axes
e_{d+1..d+n} and q_i=clip_delta(m_i x^(i-1)), a [-delta,delta]-valued
function of earlier assigned coordinates. The output x has zero initial
block (x^(0)=0 and only listed axes change; R2), x in K_0 cap E, and
m_i x^(i-1)=m_i x because later coordinates do not enter m_i. Since
x in K_0, |m_i x|<delta, so clipping was inactive: x_{d+i}=eps_i+m_i x.
This is the defining recursion, so x=x(eps) in A_good, and
x in E subset 3D_G K subset 3D_G B. The point depends on B; the SET A_good
does not. Hence s_b(A_good)<=3D_G for EVERY such B.
Cancellation: R_i x=(I-eta_ib_ib_i^T)R_{i-1}x+b_i(eps_i+eta_ib_i^TR_{i-1}x)
=R_{i-1}x+eps_ib_i, R_0x=0, so R_i x=sigma S_i (S_i the signed prefix).

## 5. DGLN law, symmetry, every fixed prefix

DGLN Thm 1.2 / Thm 3.4 (T finite subset of R^m; actual statement and proof
of part 2 read, lines 241-256, 915-919, 964-1070). With s_b<=3D_G it gives a
random Y on A_good with P(|<Y,theta>|>=t)<=2exp(-t^2/(2s_g^2)), s_g<=3 sqrt2
D_G, for every unit theta in R^m. The minimax proof only needs that T meets
every closed symmetric convex K_f of measure >=1/2, which §4 supplies.
Mixing Y and -Y keeps the support in A_good and all two-sided tails.
Pull back through the injective eps -> x(eps): one centrally symmetric law
on {-1,1}^n.
Hard support: every support point lies in K_0 subset 2D_*D, so
||R_t x||<2D_*A_0 sqrt d for ALL 0<=t<=n simultaneously:
max_t ||S_t|| <= (2D_*A_0/sigma) sqrt d = A sqrt d.
Marginals: for fixed t and unit theta in R^d,
<theta,S_t>=sigma^{-1}<R_t^T theta,Y> with ||R_t^T theta||=1, so each fixed
prefix has the two-sided tail with s=s_g/sigma, absolute.
n=0: A_good={0}, point mass. Correct, and it is ONE law for all prefixes,
not a family of prefix-specific laws, and not just terminal marginals.

## 6. Tail to MGF

Z symmetric with P(|Z|>=u)<=2exp(-u^2/(2s^2)):
E Z^{2k}=int_0^inf 2k u^{2k-1}P(|Z|>u)du<=2(2s^2)^k k!.
E e^{lambda Z}=E cosh(lambda Z)<=1+2 sum_{k>=1}(2s^2lambda^2)^k k!/(2k)!
<=2exp(2s^2lambda^2)-1<=exp(4s^2lambda^2) (since (e^x-1)^2>=0).
So E exp<u,S_t> <= exp(B^2||u||^2/2), B=sqrt8 s. Correct.

## 7. Heavy-light assembly (regime q=log(1+L)<=d)

ell(v)=descendant leaves. Heavy child = argmax ell (deterministic ties).
Maximal heavy paths partition V; each ends at a leaf; exactly L chains.
Light child w of v: some sibling has ell>=ell(w), disjoint, so
2ell(w)<=ell(v). Hence any root path has <=K=floor(log2 L) light edges.
For a chain C with head h, the chains met strictly before C on [root,h]
correspond one-to-one to the light edges on [root,h] (O2), so k<=K. A path
enters each chain once and leaves it by a light edge, so the k chains are
distinct and their intersections with [root,h] are initial segments whose
lengths depend only on the tree (possibly internal prefixes).
Sample one prefix law per heavy chain, independently across chains.
Z_C=Y_1+...+Y_k with independent Y_a, each a FIXED prefix of its chain's
single sample, so E exp<u,Z_C> <= exp(K B^2||u||^2/2).
Chernoff: P(<u,Z_C> > a) <= exp(-a^2/(2KB^2)). With
a=B sqrt(2K[d log5+log(2L)]) each term is 5^{-d}/(2L).
1/2-net N of S^{d-1}, |N|<=5^d (maximal separated set, volume), and
||z||<=2max_{u in N}<u,z> (for unit z, <u,z>=1-||u-z||^2/2>=7/8).
Union over L*5^d pairs: P(max_C||Z_C||>2a)<=1/2. Hard bounds hold on the
whole support. Some realization satisfies both. For v in C, path sum =
Z_C + (prefix of C ending at v), hence
max_v ||.|| <= A sqrt d + 2B sqrt(2K[d log5+log(2L)]).
L=1: K=0, single chain, Z=0, bound A sqrt d. No division by K or B.
Correlations between different Z_C are irrelevant (union bound).

## 8. Unary compression (regime q>=d)

Unary chain: starts at root or at a child of a branching vertex, follows
unique children, ends at a leaf or branching vertex. Every vertex lies in
exactly one chain; distinct chains have distinct last vertices, so m=L+b.
sum over nonleaves of (outdeg-1) = (|V|-1)-(|V|-L) = L-1, so b<=L-1,
m<=2L-1. The parent of a head is a branching vertex, which ENDS its chain,
so strict ancestor chains on any root path are complete.
Sign each chain by thm:signing (prefixes <=A_0' sqrt d); w_C=e_C/(A_0' sqrt d)
is in the unit ball. P(||g||>r)<=5^d exp(-r^2/8)=1/(2m) for
r=2 sqrt(2[d log5+log(2m)]), using ||g||<=2max_N<u,g>.
Bansal et al. 2111.07049v1 Lemma 4.1 (lines 888-892; ITCS Lemma 21 lines
1028-1034 identical), d>=2, m-node tree, K=rB_2 symmetric convex with
measure >=1-1/(2m): one signing tau with every root-path sum (prefix(T)
= all paths from the root, lines 165-167) in O(1)K; proof (943-979) gives
5K. Multiplying every original sign in chain C by tau_C keeps its internal
prefix bound. Path sum at v = (compressed root-path sum over strict
ancestor chains) + tau_C (internal prefix of C):
||.|| <= A_0' sqrt d (1+5r) = O(d+sqrt(d log(1+L))).
d=1: greedy on the original tree gives |sum|<=1 at every vertex.

## 9. Regime combination and explicit constants

q=log(1+L)>=log 2.
q<=d: K<=log2 L<=q/log 2; d log5+log(2L)<=d log5+log2+q<=d(log10+1).
Bound <= A sqrt(dq/log2) + 2B sqrt(2(log10+1)/log2) sqrt(dq).
q>=d, d>=2: log(2m)<=log(4L)<=log4+q<=3q, so r<=2 sqrt(2q(log5+3)), and
A_0' sqrt d(1+5r) <= A_0'(1/sqrt(log2)+10 sqrt(2(log5+3))) sqrt(dq).
q>=d=1: bound 1 <= sqrt(dq/log2).
So C = max of these absolute coefficients. The regime choice depends only
on (d,L); the two signings need not agree. Correct.

## 10. Edge cases

Zero labels: b_i=0 gives eta=1/2, C_i=I, zero column, zero predictor row;
nothing divides by a norm. Repetitions: no genericity used. Empty tree and
d=0: zero sums. Root label included once (first vertex of root chain /
root unary chain). Degrees arbitrary: only L enters. Depth and unary
lengths: absent from all bounds (hard prefix bound and thm:signing are
length-free; union bound counts chains, not vertices).

## 11. Points examined that do not create a gap

- Using the source slab lemma for K_0 (unbounded slabs) directly, rather
  than the new intersection lemma: correct, the slab lemma is stated for
  exactly this set.
- prop:adaptive needs ALL positive definite diagonal Q: every bound above
  is uniform in Q.
- DGLN subgaussian definition (two-sided tail with 2exp(-(t/s)^2/2)) equals
  the candidate's (b).
- A_good lies in a coordinate subspace of R^m; DGLN requires only finite T.
- Bansal's general statement "any convex body" is used only for a
  Euclidean ball (O1).
