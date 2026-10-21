# Paid integrated reduction: odd normalization, powers, approximation and restrictions

PREFREEZE calculations, not a frozen or nominated theorem. All assertions below are author deductions relative to the stipulated Source192 theorem. They have no independent correctness/contribution grade. Full operative source and relevant original project proof were read first; the primary composition, Fourier, symmetrization and approximation operations were read before this extended calculation. Private reading records identify exact versions and limits.

Write L(f)=sum_i fhat({i}), A(f)=sum_i |fhat({i})|, d(f)=max{|S|:fhat(S) is nonzero}, with uniform measure on the sign cube. The ambient dimension is distinguished from the number of relevant coordinates. Nothing here changes any old full target or disposition.

## 1. Pay the balanced/odd normalization completely

Given ANY nonconstant Boolean f on n signs, first replace x_i by sign(fhat({i})) x_i (sign(0)=1). This leaves its degree and bias mu=Ef unchanged and makes L(f)=A(f). Add one independent sign y and define

    g_0(y,x)=y f(y x_1,...,y x_n).

The map (y,x) -> (y,z=yx) preserves uniform measure. Hence Eg_0=E[y]Ef=0 and

    g_0(-y,-x)=-g_0(y,x),
    g_0hat({x_i})=fhat({i}),       g_0hat({y})=mu.

Its full Fourier expansion is exact:

    g_0(y,x)= sum_{|S| odd} fhat(S) x_S
              + y sum_{|S| even} fhat(S) x_S.             (1)

Distinct terms remain distinct characters, so there is no cancellation in this display. If d=d(f)>0, its exact degree is

    D=d                  if d is odd,
    D=d+1                if d is even.                   (2)

Change only y to -y when mu<0. This preserves oddness, degree and the coefficients of every x_i, and makes the y coefficient |mu|. Call the resulting function g. It is balanced, odd, has nonnegative singleton coefficients, and

    L:=L(g)=A(f)+|mu| >= A(f),     d(g)=D<=d+1.          (3)

This pays balance without assuming that a source readout has zero bias or that its zero-score fibers admit a symmetry-compatible tie rule. It is a one-sign Fourier identity, not a new substantial operation. It does not preserve coordinate transitivity: y is distinguished.

Source192 supplies f with A(f)>2 sqrt(d). Consequently its g satisfies

    L>sqrt(D),        D>1.

The first follows from D<=d+1<4d. The second also follows from the elementary Boolean bound A(g)<=I(g)<=D; a degree-one Boolean function is a constant or signed coordinate. Fix one such finite g for the rest of these calculations. Its huge unspecified size is not an efficient construction bound.

## 2. Pay exact block composition, including degree equality

For Boolean h on m inputs and a balanced nonconstant Boolean g on n inputs, substitute independent copies g_1,...,g_m on disjoint blocks. In the Fourier expansion

    (h o g)(x)=sum_{S subset [m]} hhat(S) product_{i in S} g_i(x_i),

every term in each g_i has nonempty support because Eg=0. A monomial in the composite therefore identifies its set S of occupied blocks uniquely. Within each block its coordinate support is also unique. This proves both that products contributing to a chosen monomial cannot cancel across distinct S, and that

    (h o g)hat({(i,j)})=hhat({i}) ghat({j}).             (4)

Choose a nonzero top monomial of h and a top monomial of g in each occupied block. Its coefficient is the product of their nonzero coefficients. Thus

    d(h o g)=d(h)d(g).                                  (5)

Equation (4) is exactly the primary balanced-composition operation, whose proof was read. The top-monomial argument makes its degree compatibility explicit. The independent outputs g_i are uniform signs, so E(h o g)=Eh. Odd h and g yield odd h o g under simultaneous reversal of every leaf bit.

Let F_1=g and F_{k+1}=g o F_k. Then for every k>=1,

    F_k is Boolean, balanced and odd;
    N_k=n^k,       d_k=D^k,       L(F_k)=A(F_k)=L^k;
    F_khat({(i_1,...,i_k)})=product_{j=1}^k ghat({i_j}). (6)

Set alpha=log(L)/log(D)>1/2. The exact identity is

    L(F_k)=d_k^alpha,     L(F_k)/sqrt(d_k)=(L/sqrt(D))^k. (7)

No uniform numeric alpha or small seed is asserted. No all-degrees assertion is needed, but one is cheaply available for the extremal degree budget: if D^k<=d<D^(k+1), the same F_k has degree<=d and L(F_k)>d^alpha/L. Thus an existential polynomial factor is already paid by normalization plus ordinary self-composition. It does not require uniformizing the source's changing Gaussian copy counts, and cannot be nominated here as a substantial quantitative advance.

## 3. Low influences and vanishing low Fourier levels are also paid

Let theta=max_i Inf_i(g). Then theta<1. Indeed, if Inf_i(g)=1, Booleanity on the finite cube forces g(x)=x_i h(x_{-i}) with Boolean h. Every singleton coefficient except the ith is zero, and |ghat({i})|=|Eh|<=1, contradicting L>1. Similarly a singleton coefficient of absolute value1 would make g a signed coordinate. Write a=max_i ghat({i})<1 and W=sum_i ghat({i})^2. We have 0<W<1. If W=1, Parseval leaves only singleton terms; a real linear polynomial taking only signs on the whole cube has exactly one nonzero coefficient, contrary to L>1. The latter statement follows by comparing its squared polynomial: all pairwise products of distinct coefficients must be zero and their squared sum is1.

For balanced block composition, the edge in leaf coordinate (i,j) is pivotal iff g_i flips on that edge AND the outer function is pivotal in coordinate i. The latter event depends only on the other blocks' outputs, so it is independent of the former; those outputs are uniform signs. Hence influences multiply. Iterating gives

    max_v Inf_v(F_k)=theta^k,
    I(F_k)=I(g)^k,
    max_v |F_khat({v})|=a^k,
    sum_v F_khat({v})^2=W^k.                            (8)

Thus the same exact power-law violation already has arbitrarily small individual influences and singleton coefficients. No added low-influence theorem remains unpaid at this scope.

There is also an exact spectral recursion. Put

    s(t)=sum_{S nonempty} ghat(S)^2 t^{|S|},  0<=t<=1.

For independent rho-correlated leaf pairs, each pair of block outputs is balanced with correlation equal to the previous noise stability. Fourier orthogonality therefore gives

    Stab_rho(F_k)=s iterated k times (rho).              (9)

For 0<t<1, s(t)<t because its coefficients sum to1 and some degree>=2 coefficient is nonzero. Iteration decreases to0: any positive limit below1 would contradict s(t)<t. For every fixed rho in (0,1) and fixed integer r, the sum of squared Fourier coefficients on levels1 through r is at most rho^(-r) Stab_rho(F_k), hence tends to0. Equations (7)-(9) coexist: a growing signed first-level sum does not force nonvanishing first-level squared mass. This is ordinary product/noise calculus, not a new invariance principle.

## 4. Carry the construction through approximation, rather than stop at a Fourier-error gap

A direct Fourier comparison alone has a dimension loss. If a real multilinear p satisfies |p-F_k|<=epsilon pointwise, then

    |L(p)-L(F_k)| <= epsilon E|H_{N_k}| <= epsilon sqrt(N_k). (10)

For a nontrivial seed L<sqrt(n) (strictness follows from Cauchy-Schwarz unless H_n is a scalar multiple of a sign), the signal-to-error ratio L^k/sqrt(N_k) decays. Thus (10) does not give a constant-error approximation lower bound from L^k alone. Conversely, replacing exact degree by approximate degree in the DENOMINATOR of a violation is automatic since approximate degree<=exact degree. That is not a new operation either.

The strongest compatible scalar-bias reduction repairs the lower-bound issue completely for the composed family. For independent signs of common mean t, define

    B(t)=E_t g = sum_S ghat(S)t^{|S|},       -1<=t<=1.

It is an odd polynomial with |B(t)|<=1, B(0)=0 and B'(0)=L>1. Independence of blocks gives

    E_t F_k = B iterated k times (t).                   (11)

Fix 1<lambda<L. By continuity choose 0<a<1/2 so that on [0,a], B'(t)>=lambda and

    |B(t)/(Lt)-1|<=K t^2<=1/2                          (12)

for some finite K (take K=0 if the higher coefficients vanish; that case cannot occur here but causes no problem). This follows by the odd Taylor expansion, not by a global monotonicity claim about g or B. B is increasing on [0,a] and B(a)>a, so for every z in [0,a] it has a unique inverse value psi(z) in [0,a]. Put t_0=a, t_j=psi(t_{j-1}). Then

    0<t_j<=a lambda^(-j),       B^k(t_k)=a.

Writing B(t_j)=Lt_j(1+e_j), |e_j|<=K t_j^2<=1/2, gives

    log(t_k L^k/a)=-sum_{j=1}^k log(1+e_j),
    |log(t_k L^k/a)|<=2K a^2/(lambda^2-1)=:C_0.         (13)

Consequently t_k<=a exp(C_0)L^(-k). This pays the precise expansion rate L, rather than stopping at an arbitrary lambda<L.

Suppose p uniformly approximates F_k within epsilon_0=a/8, and let q(t)=E_t p. Its degree is at most d(p), |q(t)|<=1+epsilon_0 on [-1,1], |q(0)|<=epsilon_0 and |q(t_k)-a|<=epsilon_0. The mean value theorem gives xi in (0,t_k) with

    |q'(xi)| >= (a-2epsilon_0)/t_k >= 3a/(4t_k).

The classical interior Bernstein polynomial inequality, in the actual primary interface read, is

    |q'(xi)|<=d(p)(1+epsilon_0)/sqrt(1-xi^2).

Using xi<=a and (13),

    d(p) >= [3 sqrt(1-a^2)/(4(1+a/8) exp(C_0))] L^k.   (14)

This is a positive constant depending only on the fixed seed, for EVERY k.

The usual error1/3 convention also follows with no conjectural approximation-composition theorem. If |p-F_k|<=1/3 on the cube, put u=3p/4, whose values lie in [1/2,1] when F_k=1 and [-1,-1/2] when F_k=-1. For an odd positive integer r, the polynomial

    M_r(u)=E[majority of r independent signs of common mean u]

has degree at most r, and for |u|>=1/2 its distance from sign(u) is at most 2 exp(-r/8), by the elementary bounded-sign exponential-moment bound. Choose once and for all odd r with 2exp(-r/8)<=a/8. Then M_r(3p/4), multilinearized on the cube, approximates F_k within a/8 and has degree at most r d(p). Equation (14) proves

    approximate_degree_(1/3)(F_k) >= c_g L^k,           (15)

where c_g>0 is independent of k. The trivial upper bound is D^k. This entire lower bound is paid by scalar bias iteration, the primary interior polynomial derivative inequality, and constant-error reduction. It does not establish matching approximate degree, nor a new substantial contribution merely because it is not stated verbatim in Source192.

For completeness the exponential bound used above follows from E exp(t(Y-EY))<=exp(t^2/2) for a sign Y, applied independently and optimized at t=|EY|; equivalently the standard two-point convexity/Hoeffding argument. All constants are fixed before k varies.

## 5. Decision and parity-decision reductions do not supply a new result

The actual primary conditional-score proof yields for a parity decision tree of depth h,

    E[(sum_i E[X_i|leaf])^2]<=2h,
    L(f)<=E|sum_i E[X_i|leaf]|<=sqrt(2h).               (16)

It explicitly treats correlation-free refinement, so polynomial cell degree cannot simply replace h. Applied to F_k, this gives h>=L^(2k)/2. Ordinary decision trees give h>=L^(2k). Both are compatible and fully paid.

A second actual primary already supplies explicit fixed Boolean seeds with exact degree2 and parity depth growing like3^k, and degree3 seeds with a6^k parity lower bound. Its affine elimination and full self-composition reductions were read, including their non-parity and certificate hypotheses. Our unspecified exponent 2alpha>1 does not establish an improvement over those explicit exponents; alpha has not even been numerically bounded away from1/2. We do not nominate a degree/query separation or infer a stronger certificate lower bound from the new source's title.

## 6. Restriction, full symmetrization and monotonicity comparisons

Take a uniform random subset J of exactly m of N coordinates, and set the other coordinates independently to uniform signs. For the restricted function f_{J,z}, averaging its singleton coefficient at i in J kills every original Fourier term except {i}. Therefore

    E_{J,z} L(f_{J,z})=(m/N)L(f),
    d(f_{J,z})<=min(d(f),m).                            (17)

Some restriction achieves at least the expected signed sum. The guaranteed ratio from (17) is (m/N)L(f)/sqrt(min(d,m)), which is no larger than L(f)/sqrt(d): if m>=d this is immediate; if m<d use sqrt(md)<=N. Thus ordinary restriction is fully available but its guaranteed estimate does not improve the seed exponent. This is not a theorem that no specially chosen restriction can help.

Averaging over all coordinate permutations preserves L and degree for bounded real functions, as in the primary symmetrization proof, but does not preserve Booleanity. There is a sharp elementary obstruction to obtaining arbitrary violations by demanding full permutation symmetry. If a nonconstant symmetric Boolean f on N coordinates has degree d, its values on Hamming layers are given by a nonconstant univariate polynomial p(j) of degree d. Then p(j)^2-1 vanishes at all N+1 integers j=0,...,N. It is not the zero polynomial, so

    2d>=N+1,       L(f)/sqrt(d)<=sqrt(2N/(N+1))<sqrt(2). (18)

Thus a full symmetric Boolean upgrade is impossible. This does not contradict the older cyclic construction, whose group is much smaller. The simple oddification (1) distinguishes a coordinate, and no cyclic balance claim is made. In fact an odd cyclic Boolean function on an even number of coordinates is impossible: the alternating sign vector is carried to its negative by a one-step rotation. Cyclic invariance and oddness would force f(x)=-f(x). This blocks a particular simultaneous symmetry demand; it does not refute balanced cyclic functions, balance without oddness, or any old full scope.

Finally ordinary coordinate sorting does not preserve the degree budget. Write f=a+x_i b with b=(f_+-f_-)/2 taking values -1,0,1. Increasing rearrangement of that fiber is

    C_i f=a+x_i |b|=a+x_i b^2,
    d(C_i f)<=max(d(f),2d(f)-1).                         (19)

The bound can be attained: on three signs let

    f(x_1,x_2,x_3)=(x_2-x_3+x_1 x_2+x_1 x_3)/2.

If x_2=x_3 then f=x_1 x_2; otherwise f=x_2. Hence f is Boolean of exact degree2. In coordinate1, a=(x_2-x_3)/2 and b=(x_2+x_3)/2, so

    C_1 f=(x_2-x_3+x_1+x_1 x_2 x_3)/2

has exact degree3. This is an exact obstruction to degree-preserving compression, not just an unproved estimate. The primary monotone bounded-function symmetrization preserves influence only after monotonicity is assumed, and takes values in [-1,1]. It does not turn (1) or the source's cancellation cells into monotone Boolean cells for free. No monotone full-scope result is claimed.

## 7. What is closed and what remains

The strongest developed generic construction is completely paid: one source seed gives odd balanced Boolean powers with an exact degree/linear-sum exponent above1/2, vanishing individual influences and fixed low-level squared mass, a scalar-bias proof of a standard-error approximate-degree lower bound, and the available decision-tree lower bounds. These are source plus classical/elementary compatible operations. Neither a changing source copy count nor a crude approximation-error estimate is left as a purported new difficult gap.

There is no full substantial nominee. No uniform explicit exponent improvement, matching approximation complexity, monotone Boolean construction, or balance-preserving cyclic construction has been established. They are not frozen conjectures, substitute targets or nominations. The source theorem, ordinary strengthened specializations and the older cyclic scope remain outside nomination. The calculations do not assert impossibility of all neighboring results or exhaustive literature clearance.
