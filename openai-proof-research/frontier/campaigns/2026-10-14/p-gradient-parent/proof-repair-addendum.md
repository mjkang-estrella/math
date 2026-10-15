# I345 proof repair addendum, round 1

Status: candidate support, not an acceptance. This addendum responds to
`../p-gradient-proof/review.md`, without changing its frozen I345 input.
The review is a conditional proof pass; contribution review is separate.

## Claim and dependency scope (R3, R6, R7)

The claim remains: for every integer n >= 2, constants alpha_n in (0,1/3]
and C_n exist such that every bounded weak p-harmonic function on B_1,
for every finite p >= 3, satisfies

    ||Du||_{L-infinity(B_1/2)} + [Du]_{alpha_n;B_1/2}
       <= C_n osc_{B_1} u.

There are no sign, noncriticality, level-set or boundary hypotheses.
No claim for 2 < p < 3 is made: epsilon = 1/(p-2) <= 1 is used in the
operator family below. This is a homogeneous equation result. It does
not solve the full inhomogeneous C^{p'} MathDB conjecture.

I345 section 9 is a **summary of the internal I236 proof**, not an
independent revalidation and not a self-contained replacement for it.
Replace that heading and the two corresponding claims in I345 section 1
by this dependency statement. The precise input is finite-positive-tau
fitted-class affinity from I236 `analytic-attempt.md`, sections 1–6,
with its proof review I239. Its constants may depend on tau and the fit
constant. No uniform-in-tau assertion is used. A publication manuscript
must include that full argument as an appendix (including the cone
infimum, viscosity-to-weak passage and contact argument), or cite an
accessible complete version; a review verdict is not a mathematical
reference. The pinned OpenAI theorem inputs are assumed true as directed.
I236 is a proved internal dependency, not an additional stipulation.

`input-hashes.json` binds the exact candidate, internal proof and reviews.
Later manuscripts require fresh hashes and a check that these repairs
have actually been incorporated. This document does not silently replace
the independently reviewed bytes.

## Compact-p interface (R1)

The needed lemma is a common interior C^{1,theta(n,P)} bound for
3 <= p <= P < infinity once the gradient bound is common. The primary
source is Uhlenbeck, *Regularity for a class of non-linear elliptic
systems*, Acta Math. 138 (1977), 219–240, specifically (1.3)–(1.4),
(4.9)–(4.12), (5.1) and Theorem (5.4), with (5.5).

The parent read the full main argument, printed pages 219–239, from the
primary scan recorded below. The separate compact-parameter audit is
complete in `../p-gradient-uniformity/lemma.md`, with source and output
hashes in its `manifest.json`. It supplies explicit common perturbation
and decay choices and an oscillation-normalized bound. R1 is resolved
at supporting-proof level, pending the fresh full proof gate.
The issue is common choices in the iteration, not merely
fixed-p existence of constants. The correct substitution uses the
paper's exponent s=(p-2)/2, rho(Q)=Q^s, C=0. The bounded-gradient input
comes from I345 section 2.1. In dimension two a constant extension to
dimension three preserves the weak p-equation and permits restriction
of the resulting estimate. It is not an affine lift.

## Uniform small-solution lemma (R2)

Fix N, lambda_0 > 0, Lambda_0 < infinity, rho > 0 and K < infinity.
Consider autonomous, continuous, degenerate-elliptic operators F(X,q)
on symmetric N by N matrices and R^N, with F(0,q)=0. Suppose on the
common jet ball |X|,|q| < rho they are C^2, have C^2 norm at most K,
and their matrix derivatives have eigenvalues in
[lambda_0,Lambda_0]. There exist sigma > 0, alpha > 0 and C < infinity,
depending only on these common data, such that every continuous
viscosity solution of F(D^2 Z,DZ)=0 in B_1 with ||Z|| <= sigma is
C^{2,alpha} in B_1/2, with a common finite C^{2,alpha} bound C.
One may decrease sigma to obtain any fixed sufficiently small bound on
the first and second derivatives.

This is the parameter-uniform version of Savin, *Small perturbation
solutions for elliptic equations*, Theorem 1.3 and Proposition 4.1.
Theorem 1.3 alone says its smallness constant depends on F; the
uniformity follows from the proof of Proposition 4.1, printed pp. 571–573.
In particular, p. 572 explicitly argues by a sequence of **varying** F_k
with one second-derivative bound K, extracts F_k and DF_k uniformly, and
obtains a linear constant-coefficient limiting equation with common
ellipticity. Its quadratic approximation and iteration radii depend
only on the common data. The lower-order variables and x-dependence in
that theorem are absent here. Reducing the common jet radius if needed
gives the last sentence. The parent has read the theorem and this proof;
the source's earlier Harnack argument is a cited external theorem, not
claimed to be independently reproved here.

Here is its exact application. Write xi=(a,b), |a|^2+b^2=1, b>=b_0>0,
Pi=I-xi xi^T, S_e=diag(I,sqrt(e)), and allow epsilon,A,e,d independently
in [0,1]. Set

    B_d(q) = 1 + epsilon(2d q_t+d^2 |q_x|^2)
                  + epsilon^2 A d^2 q_t^2,
    F_d(X,q) = X[(d q_x,1+e d q_t)]
                  + max(B_d(q),0) tr(S_e Pi S_e X).

These operators are continuous and degenerate elliptic on all jets.
For |q| <= 1/8, B_d >= 3/4, so the max has no switch on this common
neighborhood. They are polynomial there, with uniformly bounded first
and second jet derivatives. At q=0 their coefficient form is

    Q(h,s) = |h|^2 + (1+e)s^2 - (a.h+b sqrt(e)s)^2,
    (b_0^2/3)(|h|^2+s^2) <= Q(h,s) <= 2(|h|^2+s^2).

For a != 0, split h into its component parallel to a and its orthogonal
component to obtain precisely the scalar form in `ellipticity.md`.
For a=0 the bounds are immediate. The three compiled Lean lemmas prove
the scalar inequalities; this geometric split is a paper argument.
The common bounds on the q derivative of the coefficient matrix permit
a smaller radius rho depending only on N,b_0 with eigenvalues, for
example, between b_0^2/6 and 3. Thus every hypothesis of the uniform
lemma holds, including the endpoint parameters e=0, A=0 and d=0.

For the actual W in I345 (7.1), let a_0=||W||_{B_1} <= sigma. If a_0=0,
W=0. Otherwise put d=a_0/sigma and Z=W/d. Dividing F_1(D^2 W,DW)=0 by
d gives exactly F_d(D^2 Z,DZ)=0. Consequently

    ||DW||_{B_1/2} + ||D^2 W||_{B_1/2} <= (C/sigma) a_0.

This proportional estimate is essential; an absolute small-solution
bound alone would not give I345 (7.5).

## Strengthened bad-scale selection (R4)

Let s_0=1/8 and let b:(0,s_0] -> [0,1] be nondecreasing with b(s)->0.
Suppose no constants B,gamma>0 bound b(s) by B s^gamma for all
sufficiently small s. Given gamma_i=1/i, the function
f_i(s)=b(s)/s^{gamma_i} has unbounded supremum near zero. Choose a_i>0
so that

    M_i = sup_{a_i <= s <= s_0} f_i(s) > 2i.

This is finite since b<=1. Choose s_i in [a_i,s_0] with f_i(s_i)>M_i/2.
Then f_i(s_i)>i and, for every s in [s_i,s_0],

    f_i(s) <= 2 f_i(s_i).

Since b<=1, s_i^{gamma_i}<1/i, so s_i->0. With b the supremum of the
bad-parameter quantities beta over the normalized family, choose an
actual center, radius r_i<=s_i D(z_i), and beta_i>b(s_i)/2. From the
supremum defining beta_i choose an actual bad parameter
lambda_i>beta_i/2; then

    b(s_i)/4 < lambda_i <= b(s_i).

No monotonicity of goodness is required. Finally, for every fixed
integer k>=1,

    s_i/lambda_i^k < (4/i)^k s_i^{1-k gamma_i} -> 0.

This supplies both the displayed running-maximum estimate and all the
scale separation used in the infinite-viscosity branch. The gamma_i
sequence may be replaced by a smaller positive sequence without
affecting this construction.

## Quantified coarse-cylinder lemma (R5)

Fix n,L and b_0>0. There are d_*>0, k_*>0 and C<infinity depending
only on these data with the following property. Let U be an actual
affine lift of a weak p-harmonic solution, p>=3, defined on a
neighborhood of a fitted cylinder Z_eta(z,H;P). Suppose

    |U(z+h)-U(z)-P.h| <= eta H in that cylinder,
    c=|P| in [1/2,L+1],  A=1-c^{-2}>0,
    epsilon=1/(p-2),  e=epsilon A<=1,
    b=xi.(P/c)>=b_0,  0<eta<=d_* e.

Rotate P=c e_N. For ell=(H/4)sqrt(eta/e), put

    U(z+ell T_e(x,t))=U(z)+c ell[t+e W(x,t)],
    T_e=diag(sqrt(e) I,1).

The ellipsoid is inside the fitted cylinder: its transverse radius is
H sqrt(eta)/4 and its axial radius is <=H/4 when d_*<=1. The fit gives
||W||<= (4/c)sqrt(eta/e)<=8 sqrt(d_*). Choose d_* so this meets the
uniform threshold and its gradient smallness conclusion. The preceding
lemma, the actual constrained equation (I345 (7.3)), and scaling give

    ||T_e D^2 U T_e|| <= C e/H

throughout the half ellipsoid. Moreover

    P_new=DU(z)=c(sqrt(e)D_x W(0),1+e W_t(0))

has axial component at least c/2 and hence is nonzero. It satisfies
|T_e^{-1} N_{P_new}|<=C. If 0<lambda<=e and 0<r<=k_* ell, every
h in Z_lambda(0,r;P_new) obeys

    |T_e^{-1}h| <= C r + sqrt(lambda/e)r <= C' r.

Choose k_* so these segments stay in the half ellipsoid. Taylor's
formula proves

    sup_{h in Z_lambda(0,r;P_new)}
      |U(z+h)-U(z)-P_new.h| <= C e r^2/H.

The parameter A belongs to the **coarse fit slope P** in this lemma.
In I345 section 8 its application uses A'_i=1-|Q_i|^{-2}, whose
positivity and comparison with the base-scale A_i have first been
proved by (8.2)–(8.4). They cannot be interchanged before that step.

## Primary source receipt and remaining gates

- Uhlenbeck scan: https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6219-11511_2006_Article_BF02392316.pdf
  SHA256 `bb041a82ffd0b1c7e1b694a162aac642c2755dfd3bf00726e443ac8106e7239a`.
- Savin author-hosted paper: https://www.math.columbia.edu/~savin/Small_pert.pdf
  SHA256 `e575cc8833c7e5906000cb8e972845038dd2f78ae89fc8cc928cb7e63321e812`.
- The independent proof review's exact-arithmetic script has been rerun
  successfully by the parent. Its finite checks do not prove the
  analytic theorem. The supporting Lean project has its own pinned
  build and axiom-audit receipt.

Outstanding: fresh review of the R1 audit and the repaired proof
interfaces; contribution/novelty review; full
manuscript and appendix integration; manuscript validation and precise
formal-coverage statement. No public upload or submission has occurred.
