# W032: a unit-step filter computable from smooth-modulus remainders

Parent next mechanism, 2026-10-08. **Unreviewed derivation; no experiment.**
Verified complete factoring improvement: **NONE**. This changes the
computation after global carry-label periods became expensive. It does not
assume constant labels, a shorter period, or a free useful-digit selector.

Keep the accepted D,C_k,F and checked gcd(D,N)=1. Choose m=2R+1 and
canonical unit points a_i=a0+i, i=0,...,m. All labels may vary. Define
Z=Delta^m d_R(a_i) modulo N. Unlike the old stencil, this needs only
m<N width, not mD<N. Multiplying by the known unit D gives, from the
exact floor formula,

    D*d_R(a) = C_R(a^2)+epsilon(a)+h(a)*N
               -D*frac((C_R(a^2)+h(a)*N+epsilon(a))/D) mod N,
    epsilon(a)=sum_(k<R) N^(2k-2R)*C_k(a^2).

This equation is an equality of rational lifts modulo integer multiples
of N; the right side as a whole is integral. The degree of C_R(a_i^2)
is 2R and that of epsilon(a_i) is at most 2R-2. Applying Delta^m kills
both polynomial terms. The h term becomes an integer multiple of N,
even though h varies. Thus gcd(Z,N) is the gcd of N with an integer
residual of absolute value strictly less than D*4^R. The old small-
residual proof no longer gives N^o(1), because no factorial-width
restriction limits R. This is only removal of that specific obstruction.

## Eliminate the expensive scalar under an explicit small-tail guard

The stronger computational saving is available whenever EVERY selected
point passes the exactly checkable guard |epsilon(a_i)|<1. Put
sigma(a)=1 if epsilon(a)<0 and 0 otherwise, including epsilon=0.
Let K=C_R(a^2)+h(a)*N, an integer, and set

    t(a)=[K-sigma(a)]_D,           y(a)=sigma(a)+t(a).

For integer K and |epsilon|<1, ordinary mathematical floor gives exactly

    floor((K+epsilon)/D)=(K-sigma-t)/D,
    D*d_R(a)=C_R(a^2)-y(a) mod N.                     (1)

No rounding at epsilon=0 is discarded. Negative epsilon with K divisible
by D is precisely why sigma is required. Because the leading term is
annihilated across the unit-step stencil,

    gcd(Z,N)=gcd(Delta^m y(a_i),N).                    (2)

One need not acquire h, C_R's values, V, or any quadratic-algebra power
to evaluate the right side. Modulo D, the definition of h implies

    K = -sum_(k<R) (N^(-1) modD)^(2R-2k)*C_k(a^2) modD.

Compute this lower-degree polynomial once modulo D, reduce its values
minus sigma to obtain t, then form y and the binomial difference. This
uses only public N, known smooth modulus D, explicit coefficient
construction, exact tail-sign checks, and a final gcd. Inverting N modulo
D is a checked unit operation; N is never inverted modulo itself.

The bound 0<=y<=D gives a crude non-strict residual bound. The original
strict bound follows because (y+epsilon)/D is the exact fractional part
in [0,1), and Delta^m epsilon=0. Hence |Delta^m y|<D*4^R also for this
reduced computation. The interval's endpoints alone would not justify
strictness.

## Costs and decisive questions

The actual saved work is 2R+2 scalar power evaluations. Polynomial
coefficient acquisition remains polynomial in R, as in the exact-period
proposal. Modular evaluations use O(R^2) residue operations at bit width
O(logD) with straightforward Horner evaluation, plus binomial weights
and the final gcd. The exact guard can use the integer numerator
sum_(k<R)N^(2k)*C_k(a_i^2) and comparison with N^(2R), retaining its
full O(R logN+polynomial(R)) width on these canonical inputs. This
guard/sign work is NOT free and may dominate; sharper interval bounds
would need a proved implementation. No complete bit-speedup is asserted.

There is also a concrete conservative guard avoiding the wide N^(2R)
numerator. Evaluate the integers C_k(a^2), k<R, and put
M_a=max_(k<R)|C_k(a^2)|. If M_a<N^2-1, the geometric-series bound gives

    |epsilon(a)| <= M_a*sum_(h=1..R)N^(-2h)
                  < M_a/(N^2-1) < 1.

Let j be the highest index k<R with C_k(a^2) nonzero (it exists since
C_0=D). After factoring out N^(2j-2R), the remaining lower-index tail
has absolute value less than M_a/(N^2-1)<1. Since C_j(a^2) is a nonzero
integer, sign(epsilon)=sign(C_j(a^2)). Thus one finite integer-polynomial
evaluation table certifies both the guard and sigma, without high-precision
N powering. Coefficient values are read at their full actual widths;
for starts a0 polynomially bounded in R these widths are O(R log(R+1))
up to the coefficient-construction bound, whereas general canonical a
costs O(R logN+R log(R+1)). Straightforward evaluation of all R polynomials
at O(R) points costs O(R^3) integer operations. This is a real alternative
guard with paid setup, not a new proven factoring speedup.

Every failed guard or nonunit point is retained as its own branch. The
ordinary proper gcd exits are paid and separated from (2). If the guard
fails, this simplified evaluator has no authority to replace the scalar
filter; skip it or use an explicitly priced different algorithm.

First decisive test: independently verify (1), (2), the varying-label
annihilation, and the width/cost of the guard. Then analyze the resulting
lower-degree polynomial modulo the smooth D, rather than hypothesize a
random high digit. With R fixed and D fixed it only produces bounded
integer arguments and cannot handle arbitrarily large prime factors.
With R growing, choosing D large enough for factors is paid in bit width
but does not itself force a large scalar loop. Whether the resulting
remainders have useful N-dependent separating support remains unresolved.

This can be related to older public coefficient/height screens only after
checking their exact input-dependence and parameter regimes; it is not a
new factor-yield theorem or an all-algorithm lower-bound counterexample.
No symbolic-program or numerical run has been performed. Any selected
diagnostic must first freeze the source, inputs, guard failures and budget.
