# I333 — a rare-output test for endpoint production bounds

2026-10-13. Parent analytic deduction; not independently reviewed and not a substantial-finding nomination. This tests I332 without assuming its missing production inequality. No numerical scan is used.

Fix v>0. For integers N tending to infinity put epsilon=1/N, n=N^4 and t=sqrt(v)/N² (take N sufficiently large that t<1/2). On the uniform n-cube set

    A_N=product_(i=1)^n (1+t X_i),
    B_N=min(A_N,N/2), c_N=1/E B_N, f_N=c_N B_N,
    u_N=1-2 epsilon f_N.

Then E f_N=1, m_N=E u_N=1-2/N, and epsilon f_N<=c_N/2<3/4 for sufficiently large N. Thus u_N takes values strictly between -1 and 1 and is an admissible kernel. These are rare outputs with relative density fluctuations; their dimension changes with N.

## Tail and moment control

For every fixed integer k>=1,

    E A_N^k=[((1+t)^k+(1-t)^k)/2]^n
             =exp(k(k-1)v/2)+O_(v,k)(N^-4).

Consequently, for every fixed j and arbitrarily large fixed K, truncation at N/2 changes the j-th moments by O_(v,j,K)(N^-K): use E[A^j 1_(A>N/2)]<=(N/2)^(j-k) E A^k with k chosen large. The same bound applies to E A log A after increasing k. In particular c_N=1+O_(v,K)(N^-K). Constants may depend on the chosen K; uniformity in K is not claimed.

For the density entropy Ent(f)=E f log f, product independence gives

    Ent(A_N)=n psi(t)=v/2+O_v(N^-4).

For the density production D_den(f)=(1/4)sum_i E[(f-f^(i))(log f-log f^(i))], independence gives

    D_den(A_N)=n t atanh(t)=v+O_v(N^-4).

Clipping changes this production by a superpolynomially small quantity as well. Indeed a one-bit neighbor satisfies A'/A in [(1-t)/(1+t),(1+t)/(1-t)], and |log A-log A'|<=4t. A clipping difference occurs only when at least one endpoint exceeds N/2, which implies the other exceeds N/6 for t<1/2. The difference of the nonnegative pair products is bounded by 4t(A+A') on that event. Summing n pairs and applying the preceding arbitrary-moment bound makes the error O_(v,K)(N^-K) for any chosen K. Scaling by c_N preserves the assertion.

Also

    (1/4)sum_i E(A_N-A_N^(i))²
       =(1+t²)^n n t²/(1+t²)=v exp(v)+O_v(N^-4).

Clipping and normalization change this by O_(v,K)(N^-K). To see the required remainder control, the clipping map is 1-Lipschitz and a neighbor has comparable A value; hence sum_i E[(f+f^(i))(f-f^(i))²] is bounded by a constant depending only on v. The untruncated bound follows directly from n t²= v and the uniformly bounded third moment.

## Information and production expansions

The exact two-density identity is

    I(u_N)=epsilon Ent(f_N)
          +E[(1-epsilon f_N)log(1-epsilon f_N)]
          -(1-epsilon)log(1-epsilon).

Taylor's formula has an integrable O(epsilon³ f_N³) remainder because epsilon f_N<3/4 and the third moments are bounded. It follows that

    I(u_N)=epsilon v/2 + epsilon²(exp(v)-1)/2+O_v(epsilon³).

The production splits into epsilon D_den(f_N) plus the complementary-density term. Expanding the difference of its logarithms, using the weighted gradient bound above, gives

    D(u_N)=epsilon v+epsilon² v exp(v)+O_v(epsilon³).

Since F(I)=2I+(2/3)I²+O(I³) near zero,

    lim_(N->infinity) [D(u_N)-F(I(u_N))]/I(u_N)²
       =4[(v-1)exp(v)+1]/v² - 2/3.

This value is finite and tends to 4/3 as v tends to zero. The limit N->infinity is taken first, at each fixed v>0.

Thus a proposed stronger bound D-F>=c I²/(1-m²), with a fixed c>0 for all means near 1, is false: 1-m_N² tends to zero while the displayed ratio stays finite. The weaker dimension-free c I² bound sought in I332 is consistent with this test and is not proved by it. The example also explains why the one-coordinate coefficient blowing up at endpoint bias cannot simply be imposed on arbitrary high-dimensional kernels.

All asymptotics here concern an explicit admissible family. They do not resolve full S313 or establish an optimal global production coefficient.
