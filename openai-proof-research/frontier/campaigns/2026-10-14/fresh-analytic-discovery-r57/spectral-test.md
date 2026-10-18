# A critical-width spectral test

This is an abstract test of a proposed estimate, not a model for the
physical q=4 spectral law. It does not refute any source theorem or any
occupation limit. It sharpens the statement that merely replacing the
source's exponential rapidity estimate by its rational counterpart would
leave an operation unpaid.

For L>=1 define the inner function on Re w>0

    F_L(w) = ((w-exp(-L))/(w+exp(-L)))^2
             ((w-exp(L))/(w+exp(L)))^2.

Its four zeros are positive real, its limits at zero and infinity are 1,
and its width is 2L. Take the dilation-invariant measure on these functions
and their translates

    mu(dL,ds)=(1+L)^(-2) dL ds,   f_(L,s)(w)=F_L(exp(s) w).

The transversal measure is finite and the degree is constantly four. All
zeros lie in the strongest possible fixed cone. Thus no zero-angle or
degree pathology is involved.

Put g_L(s)=1-F_L(exp(s)). Then

    F_L(exp(s))=tanh^2((s+L)/2) tanh^2((s-L)/2),
    0<=g_L(s)<=sech^2((s+L)/2)+sech^2((s-L)/2).          (1)

In particular int g_L(s)^2 ds is bounded uniformly in L, so the current
energy int |1-f(1)|^2 dmu is finite. By multiplying the two bump bounds
in (1) and integrating s, there are absolute c,C>0 such that

    int g_L(s)^2 g_L(s+l)^2 ds
      <=C[exp(-c l)+exp(-c|l-2L|)+exp(-c(l+2L))]

for l>=0. One can first use a slightly larger exponential decay rate in
the sech bound, then absorb the linear factor in convolution by decreasing
c. Integrating L against (1+L)^(-2) gives

    I(l):=int |1-f(1)|^2 |1-f(exp(l))|^2 dmu
         <= C/(1+l)^2.                                (2)

To see the middle-term estimate directly for l>=4, split L into
[l/4,3l/4] and its complement. On that interval the density is O(l^-2)
and the exponential integral is bounded; off it, the exponent is at least
c l/2, except for an integrable further tail. Bounded l costs a constant.
Thus this example satisfies exactly the square-norm decay one would obtain
from an O(1/l) rational-row bound on a fixed current vector. Its width
survival probability is of order 1/(1+t), as in the source's integrated
width-tail argument.

Nevertheless it does not support any power gain in the source's
Laplacian-band norm. Let

    B(f)=f(1)^2+f(1)^(-2)+f(i)^2+f(i)^(-2)-4.

The expression f(1)^k B(f) is interpreted after canceling the inverse
powers, so it is well-defined almost everywhere for integers k>=2.
For |s|<=1 set a=exp(-L-s), c=exp(-L+s). Uniformly in this range, expansion
of the two *squared* Blaschke factors gives

    log f(1)=-4(a+c)+O(exp(-3L)),
    log f(i)= 4i(a-c)+O(exp(-3L)).

Choose the branches tending to zero as L tends to infinity. Consequently

    B(f)=4[(log f(1))^2+(log f(i))^2]+O(exp(-4L))
        =256 exp(-2L)+O(exp(-4L)).                     (3)

The cancellation of pure small-root and pure large-root quadratic terms
is present; the mixed product survives. For k large, restrict integration
to log(k)<=L<=log(k)+1 and |s|<=1. Here f(1)^k is bounded below by a
positive constant, and (3) is bounded below by c k^-2. Therefore

    ||f(1)^k B(f)||_(L2(mu))
       >= c k^-2/(1+log(k)).                          (4)

Every proposed bound C k^(-2-epsilon), epsilon>0, fails for this measure.
The radial two-dimensional integral of the displayed lower comparison
r^-2/log r is divergent. That observation concerns the available norm
majorant: it does NOT prove divergence of a signed potential, of an actual
physical correlation, or of its renormalized remainder.

This example explains why the finite signed row calculation in
working-interface.md cannot simply be fed into the old width-tail proof
to recover its power remainder. Even granting a stronger endpoint inner
representation with positive real zeros, finite degree moment, finite
current energy and (2), further information about the actual spectral
measure or cancellation is required. Identifying its signed leading
contribution could in principle produce a renormalized telescoping formula;
this test neither supplies nor rules out that new mechanism.
