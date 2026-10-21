# Prefreeze calculations: beyond one negative eigenvalue

This is a distinct feasibility direction in Source157's matrix proof, not a frozen theorem or a retry of i22's all-cover DP statement, r164 thinning, or Analytic161. No new mathematical gate or count is assigned. Full source matrix-rank and matrix-trees operations were read before these durable calculations; actual primary nullspace/interpolation and tree-closure operations were read during feasibility, before this note. The source tensor construction's base-graph conclusion is stipulated; its full transitive proof has not been read. No conclusion about multiple-negative matrices is inferred from its title.

## 1. Pay the spectral extension exactly

Let v_j tend to infinity, d_j<=v_j, and B_j be real symmetric, entrywise nonnegative, zero diagonal, with ||B_j||<=K for a fixed finite K. Replace the source condition n_-(I-B_j)<=1 by p_j:=n_-(I-B_j)=o(v_j). The source spectral-support argument remains valid in full:

nu_j=(1/v_j) sum_{i=1}^{d_j} delta_{lambda_i(B_j)}.

Any subsequential limit nu is supported on (-infinity,1], because at most p_j eigenvalues exceed1. Every odd trace is nonnegative by entrywise nonnegativity. If nu gave mass h to (-infinity,-1-epsilon], its (2k+1)-st moment would be at most1-h(1+epsilon)^(2k+1)<0 for sufficiently large fixed k. Thus support(nu) is contained in [-1,1]. Zero diagonal gives integral x dnu=0. K is fixed BEFORE the limit, and k is chosen after taking the limit; no exchange with unbounded moments is used.

Permit also rank(I-B_j)<=v_j(1/2+rho)+o(v_j), rho>=0, and liminf d_j/v_j>=1-delta. If theta=nu(R), then r=nu({1})>=theta-1/2-rho by the nullity bound and the closed-set weak convergence inequality. Consequently

  integral_{x!=1}(1+x) dnu = theta-2r <= 1-theta+2rho <= delta+2rho.

On [-1,1], (1-x²)²<=2(1+x), and the left side vanishes at1. Therefore

  limsup ||B_j²-I||_F²/v_j <= 2delta+4rho.                 (1)

This is the same source moment operation with its actual errors tracked. It is not proposed as a new substantial concentration/spectral theorem. Source mr:matching now applies whenever a chosen epsilon exceeds2delta+4rho and epsilon<=8^-4. With tau=epsilon^(1/4), omitted coordinates<=5tau²v and ||B-W||_F²<=8tau²v. This pays the first coordinate-matching step once normalized blocks have been supplied.

## 2. Pay the cross-trace extension

Let J_j be the joint Gram of lists (H_j,Q_j), with ||J_j||<=K and n_-(J_j)<=p_j=o(v_j). Suppose the Q block has o(v_j) eigenvalues above2+epsilon for every epsilon>0, and limsup Tr(H-block)/v_j<=eta. Set P_j=(J_j)_+ and N_j=(J_j)_-. Then

  rank N_j<=p_j,  ||N_j||_F<=K sqrt(p_j),  Tr N_j<=K p_j.

Replacing J_j by P_j changes normalized block traces by o(1) and cross Frobenius norm divided by sqrt(v_j) by o(1). The Q positive-part block has only o(v_j) eigenvalues above2+epsilon: a rank-p_j perturbation changes an eigenvalue count by at most p_j. Write P_j as the Euclidean Gram of (U,V). On the low spectral subspace E of V*V,

  ||U*V E||_F² <= (2+epsilon) Tr(U*U).

The complementary subspace has rank o(v_j) and contribution at most K² o(v_j). Hence

  limsup ||<H_j,Q_j>||_F²/v_j <=2eta.                    (2)

All errors are independent of K AFTER the limit, but existence of one fixed K remains essential. This is source mr:trace-cross plus ordinary rank perturbation and PSD factorization, not a new nonroutine operation.

## 3. Integrate the actual second normalization

Assume for the moment the source's selected blocks and counts have actually been produced: a matching of p_s coordinate pairs with liminf p_s/v>=1/2-3tau²; t_s selected pairs with liminf t_s/v>=c/3; positive definite candidate groups; and one fixed operator bound for the first and second normalized lists. These are temporary INTERFACES, not consequences asserted for p_j>1.

Keep the actual source operations: pair differences R, pair sums H, second-normalized blocks Q_e=X_e D_e^(-1/2), and exact complements L_e orthogonal to D_e^(1/2)U_e. Inverse roots are entrywise nonnegative. Thus sign domination |<R_j,Q_e,k>|<=-<H_j,Q_e,k> outside the own group remains valid; exact complements annihilate the own group. Equations(1)-(2) give the same estimates

  ||<R,R>-2I||_F²<=8tau²v,
  limsup ||<R,Y>||_F²/v<=tau,  Tr<Y,Y>=t_s,

where Y is the concatenated Q_e L_e. The Q spectral support still gives at least t_s/3-o(v) eigenvalues of <Y,Y> above1/4. Delete the R eigenvectors <=1/4 and then left singular vectors of the cross block with singular value>1/8. The surviving joint form is positive definite and has dimension at least

  p_s+t_s/3-(128/49)tau²v-64tau v-o(v).

Therefore the same rank lower bound follows:

  liminf rank(M_s)/v >=1/2+c/9-64tau-(275/49)tau²
                       >=1/2+c/9-65tau.                (3)

For tau<=c/2340 this exceeds1/2+c/12. A linear rank margin rho is compatible if rho<c/12 and2delta+4rho is small enough for the chosen tau. Merely extracting that margin in the original one-negative scope is paid by this source argument and scalar parameter choice; it is not a nominee.

For o(v) negative directions, the entire normalized spectral-to-rank-gain calculation is therefore paid. The missing issue is precisely producing the sign-preserving positive blocks, useful selected weight and common uniform normalization, not a new martingale bound or a vague invocation of inertia.

## 4. Why deleting p-1 vertices does not pay the reduction

Even a connected graph can have a matrix with two negative eigenvalues that retains two after any single vertex deletion. For two equally sized clusters of q>=3 vertices use

  M=diag(I_q-J_q,I_q-J_q)-epsilon [[0,J_q],[J_q,0]],
  0<epsilon<1/4.

Every off-diagonal entry is strictly negative, so M is well-signed for K_(2q). On within-cluster zero-sum subspaces eigenvalues are1. On cluster constants the matrix is [[1-q,-epsilon q],[-epsilon q,1-q]], with both eigenvalues negative. After deleting any vertex the quotient on the two remaining constant directions is [[2-q,-epsilon sqrt(q(q-1))],[-epsilon sqrt(q(q-1)),1-q]]. Its negative diagonals and determinant (q-2)(q-1)-epsilon²q(q-1)>0 show two negative eigenvalues remain. This is only a counterexample to the small-coordinate-deletion shortcut; K_(2q) does not satisfy the source conflict hypotheses for small beta.

## 5. Pay the strongest primary interpolation comparison

Lovasz-Schrijver2017 §2.2 and Algorithm1 (§2.3) use a continuous family with a full-rank COMMON nullspace representation U(t) to cross from one to at least two negative eigenvalues, increasing nullity at the boundary. Their hypotheses are not supplied by arbitrary interpolation between a one-negative matrix and a high-nullity two-negative matrix.

An explicit well-signed example pays this distinction. For even n>=4 let a have n/2 entries1/2 and n/2 entries-1/2, so a is orthogonal to1 and ||a||²=n/4. Put

  M(t)=(1-t)I-J-t aa*,  0<=t<=1.

Every off-diagonal entry is -1-t a_i a_j<0; all matrices are well-signed for K_n. Its eigenvalues are

  1-t-n on span(1),
  1-t-tn/4 on span(a),
  1-t with multiplicity n-2.

At t=0 there is one negative eigenvalue. At t=1 there are two negative eigenvalues and nullity n-2. At the crossing t*=4/(n+4), nullity is only1; the other n-2 eigenvalues are still positive. Thus interpolation does not preserve the endpoint kernel. A common full-rank U(t) of dimension n-2 cannot exist along this path. This does not rule out another sign-preserving deformation on the source graphs.

## 6. Exact failure of the higher-index single-tree primitive

Work in R^(2,2), the orthogonal sum of Lorentz planes with basis (t1,x1,t2,x2) and form diag(-1,1,-1,1). For T>0 use four positive unit vectors

  u1=x1,  u3=sinh(T)t1-cosh(T)x1,
  u2=x2,  u4=sinh(T)t2-cosh(T)x2.

Adjacent cyclic pairs 12,23,34,41 are orthogonal. Opposite pairs have inner product -cosh(T). Their Gram has diagonal1, only opposite off-diagonal entries -cosh(T), and eigenvalues 1+cosh(T),1+cosh(T),1-cosh(T),1-cosh(T). It has exactly two negative eigenvalues for every T>0.

Suppose a literal analogue of source mt:finite-tree existed for these four positive line sequences: nonempty subtrees S_i, required contacts for all orthogonal pairs, and each bag's normalized joint Gram uniformly bounded as T tends to infinity. Opposite subtrees must be disjoint, since a bag containing1,3 (or2,4) has Gram norm at least1+cosh(T).

But four subtrees cannot have exactly a chordless contact cycle. Proof without an external graph theorem: if S1 and S3 are disjoint, let P be their unique connecting tree path. Any connected subtree meeting both S1 and S3 contains P. Both S2 and S4 do, hence intersect, contradicting the other forced disjointness. Thus the universal single-tree replacement is FALSE already for four lines in signature(2,2).

The example has base interaction graph2K2 and does not satisfy the source large-set conflict conditions. It blocks the primitive, not the desired graph-specific conclusion, not all normalization strategies and not any theorem in the stipulated source. It is an elementary diagnostic, not a substantial negative-result nominee.

## 7. Stronger integration: the fixed-base sublinear-index direction is false

This observation was reached after Sections1-6, still PREFREEZE. It is stronger than merely leaving the normalization step unpaid. It uses the source's actual parameter order: one finite base G is fixed, THEN s tends to infinity.

Let G be ANY finite simple graph on m>=1 vertices, let A_G be its ordinary adjacency matrix, and set

  epsilon=1/(2m),  D= -I_m-epsilon A_G,
  M_s = D tensor J_s.                                    (4)

All entries are rational. For real x,

  |x* A_G x| <= sum_{uv edge}(x_u²+x_v²)
               <=(m-1)||x||².

Thus I+epsilon A_G is positive definite, with eigenvalues>1/2. D is negative definite and invertible. A pair of distinct vertices in the same blow-up fibre has matrix entry D_uu=-1<0. A pair in distinct fibres has entry -epsilon on a base edge and0 on a base hole. Hence M_s is well-signed for exactly G[K_s], with unrestricted diagonal -1. Since J_s has eigenvalues s once and0 with multiplicity s-1,

  n_-(M_s)=m,   n_+(M_s)=0,
  rank(M_s)=m,  nullity(M_s)=m(s-1).                     (5)

In particular n_-(M_s)/(ms)=1/s tends to0 while rank(M_s)/(ms)=1/s tends to0. For s>=2 the source threshold rank>ms/2+1 fails. Take G to be ANY actual fixed base supplied by Source157, satisfying all G1-G3 and alpha<=2: this exact same escape works. It is not merely a small graph failing the source conflict hypotheses.

Therefore the attempted same-fixed-base extension from one negative eigenvalue to an arbitrary sublinear negative-index budget is FALSE. It is also false to say that the fixed base's conclusion survives EVERY constant number of negative eigenvalues, since the constant m is allowed and fixed throughout the s-limit. This does not refute an exactly-two-negative assertion on suitable bases, or a statement that chooses a new base depending on a specified small index p; neither is frozen or proposed here.

The exact location of the escape is visible in the original proof. Every fibre block is -J_s and has a negative direction. All m original labels are indefinite, so the first positive-block retention step retains no labels. Orthogonal negative directions over holes cost only the finite base dimension m. The spectral extension in Sections1-3 is correct only AFTER its sign-preserving bounded positive-block hypotheses are supplied; it cannot create those hypotheses. No assertion that it proves a rank bound for (4) is made.

The Strong Arnold distinction is essential. If G has a hole uv and s>=2, choose nonzero zero-sum vectors a,b in R^s and let X have block ab* on (u,v), block ba* on (v,u), and all other blocks zero. Then X is symmetric, vanishes on all diagonal and edge positions of G[K_s], and M_s X=0 because J_s a=J_s b=0. Thus (4) does NOT satisfy Strong Arnold. No higher-index Strong-Arnold counterexample is claimed.

This elementary tensor construction is a paid rejection of the broad candidate direction, not a substantial nominated discovery. It uses only diagonal dominance, tensor eigenvalues and the actual source parameter order.

## 8. Product-tree and finite-index repairs were tested, not assumed

The four-line example in Section6 fits two Lorentz factors; its chordless cycle alone would not defeat a product-of-two-trees representation. For a family of actual boxes S_v=product_{i=1}^d S_v^(i), with every hole forcing coordinatewise subtree intersection, source mt:single-bag applies separately in each tree. Choosing its d coordinate bags yields a product point contained in all but fewer than3dq vertex boxes. This part of a product-tree repair is fully paid by union of the missing-label sets.

It does not pay the two-normalization construction. Source mt:weighted-bag first retains only cm out of total weight>3m/10. After imposing one coordinate there need not be enough remaining weight to invoke that lemma in the next coordinate. Taking independently selected heavy bags has no general intersection-weight guarantee. No such guarantee is asserted. More basically a positive subspace of a form with index2 need not project to positive subspaces under an arbitrary Lorentz-factor splitting: the positive unit vector2t1+sqrt(5)x2 has a negative projection onto the first Lorentz plane. Thus source flats and their contact conditions cannot be assigned factorwise by simply splitting the negative coordinates. The tensor escape (4) defeats any repair claimed to yield the broad fixed-base sublinear-index conclusion, regardless of representation.

For small fixed p, a maximal family of pairwise orthogonal negative blocks has size at most p; this is ordinary inertia. But in alpha<=2 base graphs there cannot be three pairwise conflicting matching edges (one endpoint from each would be an independent triple). Nor can three labels form pairwise holes. Consequently the pairwise orthogonality counting step alone has no new exclusion at p=2. Source G1 guarantees a conflicting pair across small classes, not an arbitrarily large pairwise-conflicting family. No strengthening of its quantifiers is silently inferred from the coloured distribution test.

A Ramsey fallback makes the quantitative mismatch explicit. A set of negative base blocks has hole-independence clique number at most p and cannot contain a G-clique of size2q, q=ceil(beta m), by G3. Its size is therefore less than the classical Ramsey number R(p+1,2q), with elementary bound binom(p+2q-1,p). For fixed beta>0 and p>=2 this polynomial bound grows like m^p and supplies no small fraction of m. The source chooses beta before its arbitrarily large m; changing beta to depend on the eventual m is not an available quantitative promise. This fallback is paid but ineffective here.

## 9. Outcome of the developed direction

PREFREEZE / no nominee. The complete normalized spectral and second-normalization rank calculation extends to sublinear negative index, but the same-base general matrix conclusion is explicitly false by (4)-(5), even on actual stipulated bases. Small fixed index and Strong Arnold variants remain unresolved by this work and are not nominated conditional results or replacements for any old full target. The exact examples and calculations provide durable mathematical content beyond catalogue selection or merely naming a hard geometric gap. All completed operations are source/classical linear algebra and elementary graph/tree/tensor arguments; no separate nonroutine operation establishing a new substantial full-scope theorem has been paid.
