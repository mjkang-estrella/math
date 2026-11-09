# Fixed supporting scope, r105

This file fixes the exact supporting assertions before extended proof drafting. It is not a campaign candidate freeze or nomination. Status: PREFREEZE/no nominee; no independent correctness/contribution/acceptance verdict.

Work over C, with exactly the group G, central involutions z_n, automorphism alpha, R=CG and e=(1+z_0)/2 of pinned family198 section02. For any bilateral binary sequence c=(c_n) indexed by all integers, let h(c) be the supremum of the ranks over F2 of all finite submatrices of (c_(a+b))_(a,b in Z), including h=0 and h=infinity.

(S1) A nonzero finite-dimensional complex representation on which every z_n acts by (-1)^c_n exists if and only if h(c)<infinity, equivalently c is periodic on all of Z. If h(c)<infinity, its least possible dimension is 2^(3h(c)); every such representation has dimension divisible by 2^(3h(c)). A representation attaining the least dimension can be chosen with signed permutation matrices over Q, and is irreducible over C. The zero sequence is included and has minimum dimension1. No classification of all irreducible G-representations is asserted.

(S2) For every nonzero finite-dimensional R-module Y, let Y_triv be the simultaneous +1 eigenspace of all z_n (n in Z) and L=floor(log_2(dim_C Y)/3). The underlying subspace of H^j(Y) equals Y_triv for every j>=L, where H(Y)=alpha^*(eY); its R-action is twisted by alpha^j. Consequently H is eventually zero on Y exactly when Y_triv=0. For each integer m>=1, among all nonzero Y with H^(m-1)(Y) nonzero and H^m(Y)=0, the minimum dimension is exactly 2^(3m).

(S3) Fix all source198 realization choices once: B,P,[a_*,b_*], C_chain,O,D=B x (B tensor C_chain),X,A=D semidirect X. Put E=B tensor C_chain, b=b_*>=0 and g=max(2,gldim E). Let M be the exact source encoding. For every nonzero finite Y, pd_A M(Y) is finite iff Y_triv=0. If finite, write m for its exact H-extinction time and Y_j=H^j(Y), Q_j=O tensor_B M(Y_j). With pd(0)=-infinity,

pd_A M(Y) = max_(0<=j<m) ((b+5)j + max(pd_B M(Y_j), 1+pd_E Q_j)).

In particular (b+5)(m-1)<=pd_A M(Y)<=(b+5)(m-1)+g+1. Encoded examples attaining input dimension2^(3m) have dim_C M(Y)=3*2^(3m). This asserts no bound for arbitrary finite A-modules, no formula for an unspecified minimal presentation, and no new characteristic transfer.

The research-level whole-algebra question considered is: for this fixed constructed A, does there exist a constant C_A such that pd_A N <= C_A log_2(dim_C N+1) for every nonzero finite A-module N of finite projective dimension? This question is not asserted or frozen as a feasible candidate. No restricted claim is substituted for it.
