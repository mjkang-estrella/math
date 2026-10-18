# A prefix-bounded law with dimension-free subgaussian marginals

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Author-side proof,
not an independent gate. This is supporting mathematics for original-scope.txt;
it is not proposed as a separate campaign contribution.

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

## 5. Optional coefficient-to-sign contraction, not needed for tree assembly

Let z be the noise coefficients and r_i=R_i(0,z), c_i=sqrt(1-||b_i||^2).
The block map [[C_i,b_i],[-b_i^T,c_i]] is orthogonal: C_i^2+b_i b_i^T=I,
C_i b_i=c_i b_i, and c_i^2+||b_i||^2=1. Define
 y_i=-b_i^T r_{i-1}+c_i z_i.
Then ||r_n||^2+sum_i y_i^2=sum_i z_i^2. Hence the linear map Y:z->y is a
contraction. Moreover
 epsilon_i=z_i-eta_i b_i^T r_{i-1}
          =(1-eta_i c_i)z_i+eta_i y_i=eta_i(z_i+y_i).
Thus epsilon=diag(eta_i)(I+Y)z has operator norm<=2 as a function of z. The
same law is consequently O(1)-subgaussian on the whole sign vector. This
stronger observation is not used in the frozen tree theorem, is not a new
count, and carries no separate novelty claim.

## 6. Boundary of the earlier assembly idea

An unconditional endpoint law does not by itself control an arbitrary
inherited vector or yield a conditional/shift-robust transition. Independent
laws on all maximal unary chains may accumulate variance with branch depth.
Also a path leaves an ancestor HEAVY chain at an INTERNAL vertex; terminal
marginals alone would be insufficient. The full tree argument instead uses
fixed-prefix marginals, at most logarithmically many ancestor heavy chains,
and only L chain-start union events. No conditional drift lemma is asserted.
