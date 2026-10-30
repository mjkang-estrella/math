# Author proof of the frozen sharp variance-energy inequality

This proves exactly STATEMENT.md. Entropy uses natural logarithms. The energy has the factor 4 specified there. This is an author proof, not an independent correctness or contribution verdict.

The proof first treats every finite real probability law, with arbitrary positive masses and distinct locations. An exact right-endpoint decomposition converts energy to a weighted Hardy integral. A potential controls that integral across both continuous scale evolution and discrete mass jumps. The resulting ordered entropy bound has a telescoping probability normalization. Finite deterministic approximations then give the full countable-support assertion without a moment assumption. The sharpness example is proved directly at the end.

## 1. Local variance and the two-endpoint integral

For a finite positive measure restricted to a bounded interval I, write

\[
 M_0=\rho(I),\qquad M_1=\int_I x\,d\rho(x),\qquad M_2=\int_I x^2\,d\rho(x).
\]

If M_0>0, completing the square in c gives

\[
 F_\rho(I)=M_2-\frac{M_1^2}{M_0}.
 \tag{1}
\]

If M_0=0, all three moments and F are zero. In every case F is nonnegative, and for I of length r, taking c to be its midpoint gives

\[
 0\le F_\rho(I)\le \frac{r^2}{4}\rho(I).
 \tag{2}
\]

All these quantities are measurable in the interval endpoints; for example the three moments are integrals of jointly Borel functions, and (1) applies on the measurable set M_0>0.

Changing variables b=a+r in the defining nonnegative integral gives

\[
 E(\rho)=4\int_{\mathbb R}\int_a^\infty
             \frac{F_\rho([a,b))}{(b-a)^4}\,db\,da.
 \tag{3}
\]

Tonelli's theorem permits all exchanges below before finiteness has been established.

Suppose now

\[
 \rho=\sum_{j=1}^N p_j\delta_{x_j},\qquad
 x_1<\cdots<x_N,\quad p_j>0,\quad \sum_jp_j=1.
\]

Repeated locations have already been merged. Fix a left endpoint a which is not an atom. As b increases, F([a,b)) is a nondecreasing step function. When b passes x_j>a, let M be the mass of the earlier atoms in [a,x_j), and, if M>0, let m be their mean. Adding mass p_j at x_j changes F by

\[
 \Delta_j(a)=\frac{p_jM}{p_j+M}(x_j-m)^2.
 \tag{4}
\]

This follows by expanding (1) before and after the addition. If M=0, the change is zero, which we use as the definition in that case. Set \(\Delta_j(a)=0\) for a>x_j. Formula (4) is about the actual measure in this interval; it introduces neither independent replacement samples nor new atom weights.

Since the value starts at zero,

\[
 F_\rho([a,b))=\sum_{j:x_j<b}\Delta_j(a)
\]

for almost every (a,b) with a<b. Integrating each step in b yields

\[
 E(\rho)=\frac43\sum_{j=1}^N
       \int_{-\infty}^{x_j}\frac{\Delta_j(a)}{(x_j-a)^3}\,da.
 \tag{5}
\]

Indeed, \(\int_{x_j}^\infty (b-a)^{-4}\,db=[3(x_j-a)^3]^{-1}\). A term with no earlier atom is zero.

For a fixed j, put d_i=x_j-x_i>0 for i<j and define, for r>0,

\[
 M_j(r)=\sum_{\substack{i<j\\d_i\le r}}p_i,
 \qquad Q_j(r)=\sum_{\substack{i<j\\d_i\le r}}p_i d_i.
\]

The choice of including the finitely many endpoints d_i has no effect on any integral. For r=x_j-a, the quantity \(Q_j(r)\) equals M times \(x_j-m\) in (4). Therefore (5) becomes

\[
 E(\rho)=\frac43\sum_{j=1}^N p_j J_j,
 \qquad
 J_j=\int_0^\infty
       \frac{Q_j(r)^2}{M_j(r)(p_j+M_j(r))r^3}\,dr,
 \tag{6}
\]

where the integrand is zero when M_j(r)=0.

## 2. A weighted Hardy estimate, including all jumps

Fix p>0, finitely many positive distances d_i, and positive masses q_i. Define

\[
 M(r)=\sum_{d_i\le r}q_i,\qquad
 Q(r)=\sum_{d_i\le r}q_i d_i,\qquad T=\sum_iq_i.
\]

Equal distances may be combined. We prove

\[
 \int_0^\infty \frac{Q(r)^2}{M(r)(p+M(r))r^3}\,dr
       \le \frac14\log\left(1+\frac{2T}{p}\right).
 \tag{7}
\]

Both sides are zero if there are no distances. Otherwise define w(r)=Q(r)/r. We always have 0<=w(r)<=M(r). Introduce the potential

\[
 \Psi(M,w)=\frac{w^2}{2M(p+M)}\quad(M>0),\qquad \Psi(0,0)=0.
 \tag{8}
\]

It extends continuously to (0,0) on the cone 0<=w<=M, since it is at most M/[2(p+M)]. Between successive distances M and Q are constant, and hence

\[
 \frac{d}{dr}\Psi(M(r),w(r))
 =-\frac{Q(r)^2}{M(r)(p+M(r))r^3}.
 \tag{9}
\]

At r=d, suppose a mass q is added. M jumps by q and Q jumps by dq, so w also jumps by q. To compute the exact potential jump, parametrize its segment by

\[
 (M,w)=(M_-+z,w_-+z),\qquad 0\le z\le q.
\]

For M>0 its derivative along this segment is

\[
 \begin{aligned}
 \frac{d}{dz}\Psi(M,w)
 &=\frac{w}{M(p+M)}
   -\frac{(p+2M)w^2}{2M^2(p+M)^2}\\
 &=\frac{1}{2(p+2M)}
   -\frac{p+2M}{2M^2(p+M)^2}
       \left(w-\frac{M(p+M)}{p+2M}\right)^2\\
 &\le\frac{1}{2(p+2M)}.
 \end{aligned}
 \tag{10}
\]

At the first jump, which starts from (0,0), this calculation is applied for z>0 and then integrated down to zero. Continuity of (8) justifies the endpoint. Thus every jump from mass M_- to M_+ has increase at most

\[
 \int_{M_-}^{M_+}\frac{du}{2(p+2u)}.
 \tag{11}
\]

Below the smallest distance the potential is zero. Above the largest distance M=T, Q is fixed and w=Q/r tends to zero, so the potential tends to zero at infinity. Integrating (9) on each intervening interval and adding the exact jumps shows that the integral on the left of (7) equals the sum of the potential jumps. The mass intervals in (11) partition [0,T]. Consequently their sum is bounded by

\[
 \int_0^T\frac{du}{2(p+2u)}
 =\frac14\log\left(1+\frac{2T}{p}\right),
\]

which proves (7). This argument uses finitely many actual jumps. It does not replace a step function by an uncharged differentiable approximation.

## 3. The sharp upper bound for every finite law

Write P_0=0 and \(P_j=\sum_{i=1}^jp_i\). Applying (7) to (6), with p=p_j and T=P_{j-1}, gives the stronger ordered estimate

\[
 3E(\rho)
 \le \sum_{j=1}^N p_j\log\left(1+\frac{2P_{j-1}}{p_j}\right)
 =H(\rho)+\sum_{j=1}^N p_j\log(P_j+P_{j-1}).
 \tag{12}
\]

Every argument of the final logarithm is positive. The weights p_j sum to one and

\[
 \sum_{j=1}^N p_j(P_j+P_{j-1})
 =\sum_{j=1}^N(P_j^2-P_{j-1}^2)=1.
 \tag{13}
\]

Jensen's inequality for log, applied with these weights, therefore shows that the final sum in (12) is at most zero. This proves

\[
 E(\rho)\le\frac13 H(\rho)
 \tag{14}
\]

for every finite law, including N=1. In particular the finite energy is now proved finite with a bound independent of locations, spacing, or the least atom mass. For a nontrivial finite law the numbers P_j+P_{j-1} strictly increase, so the Jensen inequality is strict; strictness is not needed for the frozen statement.

## 4. Countably supported laws: no support or moment bound

Let X have any law rho in the frozen statement. For each integer n>=1 define the deterministic finite-valued map

\[
 T_n(x)=2^{-n}\left\lfloor 2^n\max\{-n,\min\{x,n\}\}\right\rfloor,
 \qquad X_n=T_n(X),\quad\rho_n=\operatorname{Law}(X_n).
 \tag{15}
\]

Its range is finite, and T_n(x)->x for every real x. A deterministic function cannot increase discrete entropy. Explicitly, if an output atom has mass q, the input atom masses p_x in its fibre satisfy q>=p_x, so

\[
 H(\rho_n)=\sum_x p_x\log\frac1{\rho_n(\{T_n(x)\})}
          \le\sum_xp_x\log\frac1{p_x}=H(\rho).
 \tag{16}
\]

All summands are nonnegative; regrouping the countable sums is valid. By the finite result,

\[
 E(\rho_n)\le H(\rho)/3.
 \tag{17}
\]

We next justify passing to the original energy. Fix a bounded interval I=[a,b) whose endpoints have rho-mass zero. Since X_n->X pointwise, each of

\[
 \mathbf1_I(X_n),\qquad X_n\mathbf1_I(X_n),\qquad X_n^2\mathbf1_I(X_n)
\]

converges almost surely to its analogue for X. These random variables are bounded uniformly in n by constants depending only on this fixed interval. Dominated convergence gives convergence of the three local moments. If rho(I)>0, (1) consequently gives

\[
 F_{\rho_n}(I)\longrightarrow F_\rho(I).
 \tag{18}
\]

If rho(I)=0, the interval masses tend to zero and (2) proves (18) as well. No global moment of X or X_n has been used.

There are at most countably many atoms. The pairs (a,r) with r>0 and either a or a+r an atom lie in a countable union of straight lines, a two-dimensional Lebesgue-null set. Thus (18) holds for almost every (a,r). Fatou's lemma for the nonnegative integrands gives

\[
 \begin{aligned}
 E(\rho)
 &=4\int_0^\infty\int_{\mathbb R}
           \frac{F_\rho([a,a+r))}{r^4}\,da\,dr\\
 &\le\liminf_{n\to\infty}4\int_0^\infty\int_{\mathbb R}
           \frac{F_{\rho_n}([a,a+r))}{r^4}\,da\,dr\\
 &=\liminf_{n\to\infty}E(\rho_n)
 \le\frac13H(\rho).
 \end{aligned}
 \tag{19}
\]

The approximation is used only to establish the bound for rho itself. The theorem does not change its probability law or its entropy convention. Countable dense supports, accumulation points, and unbounded supports are all covered by this argument.

## 5. Optimality of 1/3

Let U_N be uniform on {1,...,N}; then H(U_N)=log N. The already proved upper bound gives

\[
 E(U_N)\le\frac13\log N.
 \tag{20}
\]

We give an explicit lower bound. Suppose N>=8 and 4<=r<=N/2. For a in [1,N-r], the interval [a,a+r) contains a consecutive block of k integers from {1,...,N}, where k>=r-1. Its unnormalized variance is

\[
 F_{U_N}([a,a+r))=\frac{k(k^2-1)}{12N}.
 \tag{21}
\]

To check this identity, a uniform law on k consecutive integers has variance (k^2-1)/12, and the block has mass k/N. It follows directly from the sums of the first k integers and their squares.

The function k^3-k is increasing for k>=1, and hence on the stated r-range

\[
 k(k^2-1)\ge(r-1)((r-1)^2-1)
             =r^3-3r^2+2r\ge r^3-3r^2.
\]

The allowed left endpoints have length N-r-1. Restricting the nonnegative defining integral for V to them yields

\[
 \begin{aligned}
 V_{U_N}(r)
 &\ge\frac13\left(1-\frac{r+1}{N}\right)\left(1-\frac3r\right)\\
 &\ge\frac13-\frac1r-\frac{r+1}{3N}.
 \end{aligned}
 \tag{22}
\]

Integrating (22) against dr/r from 4 to N/2 gives

\[
 E(U_N)\ge
 \frac13\log(N/8)
 -\left(\frac14-\frac2N\right)
 -\frac1{3N}\left(\frac N2-4+\log(N/8)\right).
 \tag{23}
\]

For N>=8 the last logarithmic term divided by 3N is at most 1/24, using log t<=t with t=N/8. In particular the weaker convenient bound

\[
 E(U_N)\ge\frac13\log N-2
 \tag{24}
\]

holds for every N>=8. Combining (20) and (24) and dividing by log N proves the frozen limit. Any universal coefficient smaller than 1/3 fails for sufficiently large N.

This completes all assertions of the frozen statement. The argument proves a sharp upper bound for this specific interval variance energy. It makes no assertion that the constants in an independent-summand entropy-loss inequality are optimal, and it yields no new dimension or absolute-continuity conclusion by itself.
