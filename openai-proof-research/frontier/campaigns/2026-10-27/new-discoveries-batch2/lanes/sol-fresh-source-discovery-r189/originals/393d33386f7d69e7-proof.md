# Finite-centralizer bounded recovery: complete technical author derivation

Myeongjin Kang; no affiliation. Original exposition CC BY 4.0. This is not an independent review or a substantial-result nomination. Scope is exactly scope-freeze.md.

## 1. Averaging with a nontrivial centralizer

Write A=M_phi and E:M->A for the phi-preserving normal conditional expectation. For symmetric interval averages P_k, one has P_k(x)xi -> E(x)xi in Hilbert norm. Indeed the mean ergodic theorem gives the projection onto the fixed Hilbert subspace; the bounded operators P_k(x) have ultraweak cluster points, each fixed by the modular action (translation changes the average by operator norm at most |t| ||x||/k). Their limit vector identifies them with E(x): the limit preserves pairings phi(a* x), a in A, which determine an element of A. This also identifies the fixed Hilbert subspace as the closure of Axi by density of Mxi.

For every normal functional psi, the predual averages converge in norm to psi E. Here is a direct justification, avoiding any uniform mixing assertion. The norm-closed span V of coboundaries rho-rho sigma_t has annihilator exactly A. Hahn--Banach therefore identifies V with the functionals vanishing on A. Thus psi-psi E belongs to V. The averages are contractions, kill each coboundary in norm in the limit, and fix psi E. This proves the assertion. No factoriality or finite dimensionality is needed for these two limits.

Suppose now A is finite dimensional and let mu>0 be the minimum of phi(e) over its minimal projections. The restriction phi|A is a faithful trace. For a>=0 in A, ||a||<=mu^(-1)phi(a): choose a maximal-eigenvalue minimal projection. Every state rho on A consequently satisfies rho<=mu^(-1)phi|A. Also phi(a^2)<=mu^(-1)phi(a)^2. These facts work across all centralizer blocks.

## 2. Positive direction with every source step exposed

Use the filters from canonical source290, sections/03-modular-averaging.tex and 04-bounded-recovery.tex. Choose smooth 0<=f_0<=1, equal to one on [-1,1] and supported in [-2,2]. Its inverse Fourier kernel g_0 is integrable. Set f_r(u)=f_0((u-s)/r), and F_r(x)=integral r exp(-ist)g_0(rt) sigma_t(x) dt. Then F_r(x)xi=f_r(D)x xi and ||F_r(x)||<=C_1||x||, C_1=||g_0||_1 independent of r.

From the hypothesis pass to a subsequence with averaged squared norm >=4gamma>0. Density of Mxi and filtering by F_delta give normalized y_n xi approximating h_n, with averaged squared norm >=2gamma, norm one and support [s-d_n,s+d_n], d_n=2delta_n. Discard a finite head so d_n<=1. Tomita's identity gives phi(y_n*y_n)=1 and phi(y_n y_n*)<=exp(s+1). There is no uniform operator bound on y_n.

Fix n and write y=y_n. Define A_k=P_k(y*y), B_k=P_k(yy*), psi(x)=phi(y*xy), and psi_k=average psi sigma_-t. Then ||B_k||<=||y||^2 and phi(B_k)<=exp(s+1). Section 1 gives

    phi(A_k^2) -> phi(E(y*y)^2) <= mu^(-1),
    ||psi_k-psi E|| -> 0,     psi E <= mu^(-1)phi.

The last inequality follows by domination of the state psi|A; it does NOT identify psi(a) with phi(a yy*). For sufficiently large k (depending on n), the sum phi(A_k^2)+psi_k(B_k) is at most mu^(-1)(1+exp(s+1))+2. The ultrafilter set where the averaged defect exceeds 3gamma/2 meets this cofinite set. Choose k there.

Strong-star continuity on the compact averaging interval permits simultaneous finite Riemann approximation of the defect and the two double-integral moments. Thus there are finite weights p_i and z_i=sigma_(t_i)(y) such that, with A_0=sum p_i z_i*z_i, B_0=sum p_i z_i z_i*,

    sum p_i ||Tz_i xi||^2 >= gamma,
    phi(A_0^2)+sum p_i phi(z_i*B_0 z_i) <= C,
    C=mu^(-1)(1+exp(s+1))+3.

Let eps_i be independent uniform unit-circle scalars and z=sum sqrt(p_i) eps_i z_i. Independence yields E||Tzxi||^2>=gamma and the exact noncommutative fourth-moment identity

    E[(z*z)^2]=A_0^2+sum p_i z_i* B_0 z_i - sum p_i^2(z_i*z_i)^2.

Consequently E phi(|z|^4)<=C. With z=u|z| put z^[K]=u min(|z|,K). The scalar inequality (r-K)_+^2<=r^4/K^2 gives E||(z-z^[K])xi||^2<=C/K^2. Now set v=F_(d_n)(z^[K]). Every realization has norm <=C_1 K and support [s-2d_n,s+2d_n]. Since this filter fixes zxi and is a Hilbert contraction,

    (E||Tvxi||^2)^(1/2) >= sqrt(gamma)-||T||sqrt(C)/K.

Choose a single positive K>=2||T||sqrt(C/gamma). The phase torus is compact and the polar cutoff is norm continuous (write z^[K]=z q_K(z*z) with continuous q_K). Thus a realization attains at least the expectation and gives ||Tv_n xi||>=sqrt(gamma)/2. This proves BR with the exact factor-four band and full frozen quantifiers.

All randomization, moment identity, cutoff, filtering and selection here are source-paid. Only finite-dimensional domination replaces scalar ergodicity in the source's two moment bounds.

## 3. Infinite centralizer: a commuting spectral selector

An infinite-dimensional von Neumann algebra contains countably many mutually orthogonal nonzero projections p_n. Otherwise repeated splitting must terminate after a bounded number of minimal projections, expressing its identity as a finite sum of minimal projections and making the algebra finite dimensional. Apply this to A. Put q_N=sum_(n>=N) p_n. Normality implies phi(q_N)->0.

For p in A, both L(p) and R(p) commute with the modular group and its spectral projections. The Hilbert space L(p)R(p)H identifies with the standard Hilbert space of pMp, and the modular operator restricted there is the modular operator of phi(p)^(-1)phi|_(pMp). One can check this directly: the projection L(p)R(p) commutes with J and Delta, and the restricted Tomita operator sends xxi to x*xi for x in pMp; scaling the cyclic vector by phi(p)^(-1/2) does not change the operator. A nonzero corner of a type III_1 factor is again type III_1. Connes's S invariant is [0,infinity) for such a corner and is contained in the spectrum of every faithful normal state's modular operator. Hence the logarithmic modular spectrum on each p_n corner is all R. In particular every nonempty open spectral interval has a nonzero subspace there. These are standard modular/corner facts, not new constructions claimed here.

Fix any s. Let I_n=(s+2^(-n)-2^(-n-3),s+2^(-n)+2^(-n-3)) and delta_n=2^(1-n). These disjoint intervals avoid s and are contained in [s-delta_n,s+delta_n]. The commuting products Q_n=E_D(I_n)R(p_n) are pairwise orthogonal projections. Their strong sum T is an orthogonal projection commuting with D. Choose a unit h_n in E_D(I_n)L(p_n)R(p_n)H. Then Th_n=h_n and ||TU_t h_n||=1 for every t; all the stipulated means give one.

Suppose v_j in M have ||v_j||<=C and support of v_j xi in [s-epsilon_j,s+epsilon_j], epsilon_j->0. For fixed N, eventually this interval misses every I_n with n<N. Orthogonality gives

    ||Tv_j xi||^2 <= sum_(n>=N) ||R(p_n)v_j xi||^2
                   = ||R(q_N)v_j xi||^2
                   = ||v_j q_N xi||^2 <= C^2 phi(q_N).

The penultimate equality uses q_N in the centralizer, so R(q_N)xi=L(q_N)xi, and commuting left/right actions. First let j tend to infinity, then N. The result is ||Tv_j xi||->0. This excludes every proposed BR output, including all subsequences with epsilon_j=4delta_(n_j). Necessity is proved.

## 4. Boundary of the statement

Type III_1 supplies full corner spectra. The criterion cannot be extended to all factors: for a diffuse finite factor with its trace, D=0. Any nonvacuous BR hypothesis has s=0 and T nonzero; density supplies one x in M with Tx xi nonzero, and the constant sequence x is already bounded and supported at zero. Thus BR holds while the centralizer is infinite dimensional.

No conclusion about bicentralizer triviality, expected amenable algebras, or spectral-gap classification is deduced. No formal verification of operator-algebra arguments is claimed.
