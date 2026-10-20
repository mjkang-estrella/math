# T177C143 — exact frozen author scope

Status: author-proof target, not an independent correctness/contribution grade or acceptance. Runner: Codex / GPT-6 Astra / high / default service tier. Feasibility calculations, actual source/proof/history and primary readings, and the first finite diagnostics preceded this freeze. Extended author-proof assembly follows it. The dated freeze receipt separately binds these exact bytes.

## Definitions and universal finite statement

Let X be ANY finite connected pure simplicial complex of dimension d>=2 with H^1(X;F_2)=0. Use the intrinsic top-face incidence probability weights

w_i(sigma)=#{tau in X(d):sigma subset tau}/[binom(d+1,i+1)|X(d)|]

and weighted support norms ||.||_i. All cochains and coboundary maps delta_i in this statement have coefficients F_2. Let V=X(0), E=X(1), G=(V,E), n=|V|, D_G=diam(G), and

bar_d=sum_{u,v in V} w_0(u)w_0(v) dist_G(u,v).

Suppose alpha,beta>0 satisfy, for every a in C^0 and x in C^1,

||delta_0 a||_1 >= alpha min(||a||_0,1-||a||_0),
||delta_1 x||_2 >= beta dist_1(x,B^1).

Let H be ANY subgroup of Aut(X), and let gamma=min_O sum_{e in O}w_1(e)>0, where O runs over H-orbits on E. Put B=B^2=im(delta_1), F_b={x in C^1:delta_1 x=b}, and lambda(b)=min_{x in F_b}||x||_1.

A stochastic section is ANY probability distribution on the finite set of ALL functions s:B->C^1 satisfying delta_1 s(b)=b for every b. The functions need not be linear, normalized at zero, local, equivariant, efficient, or chosen by a restricted algorithm. One sampled function is used for all inputs. Define

L(X)=inf_s max_{b!=c in B} E||s(b)+s(c)||_1 / ||b+c||_2,
R(X)=inf_s max_{b!=c in B} E||s(b)+s(c)||_1 / lambda(b+c).

The conclusion is

(alpha bar_d-2)/6 <= L(X) <= (2D_G+1)/(gamma beta),
alpha bar_d/2-1 <= R(X) <= (2D_G+1)/gamma.                 (A)

More precisely, for EVERY stochastic section,

sum_{e in E} (1/|B|) sum_{b in B} E||s(b+delta_1 1_e)+s(b)||_1
    >= alpha bar_d/2-1.                                  (B)

The upper bounds are achieved as inequalities by a distribution on F_2-linear sections obtained from automorphic translates of one breadth-first spanning tree.

For the uniform probability law mu_b on F_b, with transport cost the weighted Hamming metric ||x+y||_1,

W_1(mu_b,mu_c)=lambda(b+c).

Moreover R(X) equals the infimum, over ALL joint couplings (Z_b)_{b in B} with Z_b~mu_b, of max_{b!=c} E||Z_b+Z_c||_1/W_1(mu_b,mu_c). The analogous statement with denominator ||b+c||_2 equals L(X). Thus the lower bounds cover arbitrary joint couplings, not merely couplings from a selected sampler. The metric space ({mu_b},W_1) has an embedding into an L_1 space with distortion at most 3/beta.

## Entire pinned source family, all levels

Fix ANY integer d>=3 and ANY odd prime q satisfying ALL largeness assumptions in family177 at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Put N=2d+1, M=q^{binom(N,2)}, and take EXACTLY the source complexes

X_m=skel_d CC(U/Gamma_N(m);(bar H_i)_{i=0}^{N-1}),  m>=2,

with U, Gamma_N(m), H_i and their reductions as in the source construction. Let epsilon>0 be a uniform source expansion constant in degrees 0 and 1 for this fixed d,q, and put

D=M binom(N-1,d), Delta=dD,
K=M binom(N,d+1) binom(d+1,2), n_m=|X_m(0)|,
r_m=max(0,floor(log(n_m/(2D))/log Delta)),
R_m=ceil(log(D n_m)/log(1+epsilon/2))+1.

For EVERY integer m>=2 the full conclusions above hold and give

epsilon r_m/12-1/3 <= L(X_m) <= K(4R_m+1)/epsilon,
epsilon r_m/4-1 <= R(X_m) <= K(4R_m+1).                  (C)

In particular BOTH optimal constants are Theta_{d,q}(log n_m) as m tends to infinity, whereas ordinary cofilling has constant at most 1/epsilon and the fibre-law Wasserstein spaces embed into L_1 with distortion at most 3/epsilon, uniformly in m. No smaller dimension, restricted nonlinear section class, subsequence, or changed complex is substituted. This is one result with a general finite inequality and its source-family application, not multiple nominations.

## Boundaries

No assertion of an optimal leading constant, efficient optimal sampler, deterministic Lipschitz upper bound, higher-degree analogue, new coefficient-uniform expansion, or worldwide priority is part of this scope. Publication remains stopped. I07 puncturing, r80 defining-characteristic growth, r142 interval Betti comparison and every other old frozen statement remain unchanged. Parent alone commissions reviews and assigns any gate or count.
