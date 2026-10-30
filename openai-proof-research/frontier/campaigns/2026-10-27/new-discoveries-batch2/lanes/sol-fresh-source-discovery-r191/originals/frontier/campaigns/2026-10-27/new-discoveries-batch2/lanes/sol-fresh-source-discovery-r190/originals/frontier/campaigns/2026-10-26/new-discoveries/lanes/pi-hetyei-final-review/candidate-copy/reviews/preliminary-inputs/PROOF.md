# Proposed full proof of Hetyei Conjecture6.10 (MathDB319292)

**Research candidate, credit0. No Lean endpoint or independent review yet.**
The argument below is a proposed full mathematical proof, not an accepted discovery.
Exact source, bounded prior-art limits and formal scope must pass separate review.

## 1. Literal source target and normalization

Gábor Hetyei, arXiv0912.0573v1 (3December2009), printed p19 Conjecture6.10,
asks `n*kappa_(n-1)>kappa_n` for every n>=12, equivalently
`n*K_(n-1)>K_n` for every n>=11. Printed pp19–20 were personally rendered
and read. The actual source identities (15)–(18), Lemma6.9 and (21) give

    sum_(n>=0) K_n*t^n/n! = U(t) = 1/((1-t)(1-log(1-t))),
    kappa_(n+1) = (n+1)*K_n,
    a_n = (-1)^n*(K_n-n*K_(n-1)).

Put u_n=K_n/n!, u_0=1, u_1=0. The denominator of U is

    1 - sum_(j>=2) t^j/(j*(j-1)).

Therefore

    u_n = sum_(j=2)^n u_(n-j)/(j*(j-1)),
    b_n = u_n-u_(n-1) = (-1)^n*a_n/n!.

The target is exactly b_n<0 for n>=11. The relation then gives
the literal kappa inequality for ranks>=12. We do NOT claim as a result
the source p20 equation(23), which prints the opposite integral sign.
That ancillary sign discrepancy receives no discovery credit.

The source's explicit nonnegative ordered-composition formula(16), or
equivalently its finite signed-Stirling formula(18), supplies a concrete
finite presentation of K. A final Lean endpoint must prove its bridge to
the recurrence, not leave an abstract generating-function premise.

Exact recurrence arithmetic gives

    b_3 = -1/3,
    b_12 = -10819/9979200 < -1/2000,
    b_14 = -3676549/1816214400 < b_12,
    b_14-b_12 = -1707491/1816214400.

The first sign change is not separately counted. All finite checks are in
flat-bernoulli-spectral-check.json; finite sampling is not the all-order proof.

## 2. Finite symmetric arrowhead approximants

For N>=1, let t_i=i/N, i=0,...,N-1, c_i=1/N and
v_i=sqrt(c_i*(1-t_i)). On R direct-sum R^N form the symmetric matrix

                  H_N = [ 0    v^T      ].
                        [ v    diag(t_i) ]

Write u_n^(N)=(H_N^n)_(00), b_n^(N)=u_n^(N)-u_(n-1)^(N).

For a real vector (a,z), completing squares gives

    (a,z)^T*(I-H_N)*(a,z)
      = sum_i (sqrt(1-t_i)*z_i-a/sqrt(N))^2 >=0,
    (a,z)^T*(I+H_N)*(a,z)
      = sum_i (sqrt(1-t_i)*z_i+a/sqrt(N))^2
          +2*sum_i t_i*z_i^2 >=0.

Thus the spectrum of H_N lies in [-1,1]. Its restriction to the
codimension-one subspace a=0 is nonnegative. Hence it has at most one
negative eigenvalue, counted with multiplicity: two orthonormal negative
eigenvectors admit a nonzero linear combination with center coordinate0,
whose quadratic form would be negative. Each negative eigenvector has nonzero center coordinate, so this combination is nonzero. There is a negative eigenvalue:
the center spectral measure has mean (H_N)00=0 but second moment

    (H_N^2)00 = sum_i c_i*(1-t_i) = (N+1)/(2*N) >=1/2.

If all eigenvalues were nonnegative, zero mean would force zero second
moment. Denote the unique negative eigenvalue by -q, with 0<q<=1.
For every spectral value lambda, (lambda+q)*(1-lambda)>=0, so

    lambda^2 <= (1-q)*lambda+q.

Integrating against the center spectral measure (mean0) proves q>=1/2.
Let w_lambda>=0 be its spectral weights, whose sum is1. We have

    b_n^(N) = sum_lambda w_lambda*(lambda-1)*lambda^(n-1).

Repeated nonnegative eigenvalues cause no difficulty. All assertions are
about ordinary finite real symmetric matrices, not an assumed infinite
operator or an unproved Stieltjes representation.

## 3. Finite spectral propagation criterion

Consider any such center spectral measure, with mean0, spectrum contained
in [-1,1], unique negative eigenvalue -q, q>=1/2. Suppose, for some c>0,

    b_12 <= -c,    b_14 <= b_12,    -b_3 >= 1/4.

Then all b_n, n>=11, are strictly negative, with quantitative bounds
that are uniform in the matrix dimension.

For even indices, put

    T = w_(-q)*(1+q)*q^11,
    S_m = sum_(lambda>=0) w_lambda*(1-lambda)*lambda^11
                                  *(lambda/q)^(2*m).

Then b_(12+2m)=q^(2m)*(T-S_m), and S_0=T-b_12.
The hypothesis b_14<=b_12<0, together with q<=1, gives

    b_14 <= q^2*b_12,
    S_1 >= S_0.

For z>=0 and integer m>=0 the elementary tangent inequality
z^m>=1+m*(z-1) gives S_m>=S_0+m*(S_1-S_0)>=S_0.
Consequently

    b_(12+2m) <= q^(2m)*b_12 <= -c*4^(-m).

For odd indices, set d_lambda=w_lambda*(1-lambda)>=0. Since the
center spectral mean is0, sum d_lambda=1. Moreover

    -b_(2m+1) = sum_lambda d_lambda*(lambda^2)^m,
    sum_lambda d_lambda*lambda^2 = -b_3 >=1/4.

Convexity of nonnegative integer powers (or their tangent inequality)
therefore yields -b_(2m+1)>=(1/4)^m. This includes n=11. All even
n>=12 and odd n>=11 have the required strict sign. The argument uses
only finite sums and a positive-weight power inequality.

## 4. Convergence to the exact source recurrence

The center moments of H_N satisfy u_0^(N)=1, u_1^(N)=0 and

    u_n^(N) = sum_(j=2)^n p_j^(N)*u_(n-j)^(N),
    p_j^(N) = (1/N)*sum_(i=0)^(N-1) (1-t_i)*t_i^(j-2).

For example, solve the node recurrence
z_(n+1,i)=v_i*a_n+t_i*z_(n,i), z_(0,i)=0, with
a_(n+1)=sum_i v_i*z_(n,i). Substitution gives precisely this finite
convolution, with no analytic inverse-matrix assumption.

For each fixed j, the Riemann sums tend to

    integral_0^1 (1-t)*t^(j-2) dt = 1/(j*(j-1)).

Induction on n in the finite convolution proves u_n^(N)->u_n and
b_n^(N)->b_n for every fixed n. The three exact values in section1
therefore imply, for all sufficiently large N,

    b_12^(N)<=-1/2000, b_14^(N)<=b_12^(N), -b_3^(N)>=1/4.

Apply the finite criterion. Its bounds are independent of N, so passage
to the limit preserves a strictly negative bound:

    b_(12+2m) <= -(1/2000)*4^(-m) <0,
    b_(2m+1) <= -4^(-m) <0.

Thus b_n<0 for every n>=11, proving Conjecture6.10 via section1.
Only one combined source-question outcome is proposed; the quantitative
bounds, matrix criterion, source-known count formulas and elementary
power convexity receive no separate discovery credit.

## 5. Independent analytic cross-check (not needed by the spectral route)

The classical reciprocal-logarithm Stieltjes identity gives, near t=0,

    1/(1-log(1+t)) = e/(e-1-t) - integral_1^infinity W(s)/(s+t) ds,
    W(s)=1/((1-log(s-1))^2+pi^2).

It follows that b_n=(-1)^n*e/(e-1)^(n+1)-I_n, where
I_n=integral_1^infinity W(s)*s^(-n-1) ds. Odd n are immediate.
For k=2,...,6, on [1+2^(-k),1+2^(-(k-1))], use log2<7/10
and pi^2<10 to bound W(s)>1/((1+7*k/10)^2+10). Integration at n=12
gives the explicit rational J in flat-bernoulli-cutoff-certificate.json,

    J>1/400> (2719/1000)/(1718/1000)^13 > e/(e-1)^13.

All these intervals lie below3/2<e-1, so for n>=12,
I_n>=(e-1)^(12-n)*J>e/(e-1)^(n+1). This confirms the sign by a
different mechanism. The spectral proof avoids any need to formalize the
classical logarithmic Stieltjes identity or a keyhole contour integral.

## 6. Outstanding acceptance gates

- Independent adversarial source/math/novelty/eligibility review, including
  whether a prior renewal-sequence theorem already subsumes the claim.
- Full Lean source recurrence/composition bridge, finite spectral criterion,
  arrowhead structure, moment recurrence and actual convergence; no residual
  spectral or representation hypotheses are allowed at the final endpoint.
- Final manuscript, rendered visual checks, independent final review,
  deterministic packet and fresh extracted strict replay.

No formal or discovery acceptance is claimed here. Current campaign total21/30.
