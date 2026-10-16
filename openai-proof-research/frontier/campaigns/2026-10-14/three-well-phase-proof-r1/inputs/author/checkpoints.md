# Mathematical checkpoints (saved before packaging)

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

The frozen target is P3R in original-scope.md. Preliminary calculations below will be expanded and checked in candidate.md; they are not an independent verdict.

- Local normalized state: phi_a(x)=sqrt(2a/pi) sech^(1/2)(2ax). Its norm is one, energy -a^2, tail A_a=sqrt(4a/pi).
- If w_a is multiplied by lambda in (0,2), factorization with nu=(sqrt(1+3lambda)-1)/2 in (0,1) gives precisely one negative eigenvalue -a^2(sqrt(1+3lambda)-1)^2. The supersymmetric partner is nonnegative after the energy shift.
- For real k>0 the lifted Birman–Schwinger matrix K_G=D^(1/2)(G tensor R0(k))D^(1/2) obeys (1-2rho) diag K_single <= K_G <= (1+2rho) diag K_single. If justified as a quadratic-form comparison, this gives exactly three negatives at every separation, not merely three near -a^2.
- Coalescence difference is a^2[f(1+2rho)+2f(1-rho)-f(1-2rho)-2f(1+rho)], f(lambda)=(sqrt(1+3lambda)-1)^2. f'''=-(81/4)(1+3lambda)^(-5/2)<0. A central-difference integral proves strict negativity.
- On |k-a|=a/10, write A(k)=(I-K_single(k))^-1. Its residue at a is |eta><eta|/(2a), eta=sqrt(w_a)phi_a. Pairing eta with sqrt(w_a)e^(+/-ax) gives 2a A_a.
- Cross-well block at distance d: separated rank-one kernel e^(-kd)/(2k) (sqrt(w_a)e^(kx)) tensor (sqrt(w_a)e^(-ky)). Its Hilbert–Schmidt error is O(sqrt(1+d) e^(-2ad)), uniformly on that contour; reversal of x,y supplies the opposite direction. This uses the actual exponential tails.
- Offdiagonal interaction determinant log difference begins -4rho^3 F_R(k), F_R=tr(A B12 A B23 A B31). Even walks cancel under the sign flip; higher odd walks start at length5 and their fixed-contour norm is O(e^(-9aR/2)).
- Rank-one replacement yields F_R=e^(-4kR) h(k)+exponentially smaller contour error; h has pole order3, with lim_(k->a)(k-a)^3 h(k)=A_a^6.
- The trace difference should be 8rho^3 Res_(k=a)[k e^(-4kR) h(k)]. Highest residue term is 64 a A_a^6 rho^3 R^2 e^(-4aR). This must be checked via the full determinant argument, not a 3x3 truncation of trial states.
