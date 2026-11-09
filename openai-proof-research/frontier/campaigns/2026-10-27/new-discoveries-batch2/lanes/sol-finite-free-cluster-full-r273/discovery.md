# Leake–Ryder cluster attack: unresolved, no credit

## Literal endpoint

The frozen arXiv:1811.06382v1 body, Definition 2.2 and Conjecture 2.5 (pp6–7), says: for EVERY integer n>=1, every real-rooted p,q,r of degree EXACTLY n, and i,j,k in {1,...,n} with i>=j+k-1, BOTH inequalities

    lambda_i(p boxplus_n q boxplus_n r)+lambda_l(r)
      <=lambda_j(p boxplus_n r)+lambda_k(q boxplus_n r)

are asserted, separately for l=max(j,k) and l=n+1-max(j,k). Roots are nonincreasing, counted with multiplicity. Section 1 defines p boxplus_n q=(1/n!) sum_{h=0}^n p^(h)(x) q^(n-h)(0). Positive scalar monic normalization does not change any root. No source degree lowering or padded roots from Definition 4.5 are silently imported. Only i=j+k-1 needs testing: larger i weakens the LHS. The smaller of the two l is the stronger inequality, but both are retained in the checks and records.

The source date is 14 November 2018 (arXiv submission), while its printed date is 16 November. The inherited n<=2 proof remains an uncredited helper, not a solution of this endpoint.

## Exact coefficient derivation, including collisions

Write P_(n,a,u)=x^(n-a)(x-u)^a, 0<=a<=n, u rational. It is monic, degree n, real-rooted, with the displayed multiplicities (coalescing at u=0). Its coefficient at x^(n-s) is (-1)^s binom(a,s)u^s. Substitution into the DEFINITION gives the coefficient at x^(n-d) of P_(n,a,u) boxplus P_(n,b,v):

    (-1)^d sum_{s+t=d} binom(a,s)binom(b,t)u^s v^t
          (n-s)!(n-t)!/[n!(n-s-t)!],       0<=d<=n.

Terms outside 0<=s<=a, 0<=t<=b are zero. This follows by differentiating the x^(n-s) term t times: its factor is (n-s)!/(n-s-t)!, while the q derivative at zero contributes (n-t)!; division by n! is essential. Reapplying this identity computes the triple without changing n. This is the formula implemented directly by polynomial differentiation in cluster.py; no guessed matrix operation is substituted.

For equal scale u=v=1 the permutation formula yields the exact terminating hypergeometric overlap identity

    P_a boxplus P_b = sum_h [binom(a,h)binom(n-a,b-h)/binom(n,b)]
                    x^(n-a-b+h)(x-1)^(a+b-2h)(x-2)^h,

max(0,a+b-n)<=h<=min(a,b). Proof: pair each root of the first polynomial with a uniformly permuted root of the second; the number h of matched ones has that hypergeometric law; the three sums 0,1,2 have the displayed multiplicities. The permutation formula itself follows from averaging elementary symmetric coefficients and the factorial coefficient above. This identity is polynomial-exact and valid at every allowed multiplicity, unlike a simple-root Taylor expansion. symbolic.py verifies all nontrivial a,b for n2..7. Unequal-scale pairs have a bivariate terminating coefficient sum; we do NOT label them one fixed Jacobi family without a valid parameter map. The 2023 hypergeometric paper supplies general factorization tools, not the desired indexed three-input inequality.

## Structural route retaining the finite-free operation

For a=1 one gets the all-degree identity

    f boxplus P_(n,1,u) = f-(u/n)f'.

For f=prod(x-rho_s), this is det(xI-D-(u/n)11^T), D=diag(rho_s), by the determinant lemma, extended as a polynomial identity through repeated rho_s. For u>=0, rank-one interlacing gives ordered roots theta_1>=rho_1>=theta_2>=rho_2>=...>=theta_n>=rho_n, counting multiplicity. This is a valid single-step representation and an exact collision-safe comparison. It does not assert a common fixed matrix realization of all four terms in the conjecture: after another convolution, the new diagonal consists of the roots of the preceding output and the rank-one vector is reset. Forgetting this reset recreates the false generic-Hermitian shortcut.

For example, three rank-one factors in degree3 give exactly

    x^3-(u+v+w)x^2+(2/3)(uv+uw+vw)x-(2/9)uvw.

In degree4 they give x times [x^3-(u+v+w)x^2+(3/4)(uv+uw+vw)x-(3/8)uvw]. These symbolic scale formulas were derived directly, then used to guide bounded exact isolation, rather than starting from a floating-point sweep.

A collision-splitting diagnostic can also be derived without divergent simple-root denominators. For r=x^(n-c)(x-w)^c, w>0 fixed, p=P_(n,1,epsilon*u), q=P_(n,1,epsilon*v), with u,v>0 and c>=2, the exact operator is 1-epsilon*(u+v)D/n+epsilon^2*uv*D^2/n^2. Near w, putting x=w+epsilon*y and dividing by epsilon^c*w^(n-c), its leading polynomial is

    y^(c-2)[y^2-c(u+v)y/n+c(c-1)uv/n^2].

The two nonzero roots are d_+>d_->0, the zeros of that explicit quadratic. Other c-2 roots remain EXACTLY w; the two split roots are w+epsilon*d_±+O(epsilon^2), by the implicit function theorem applied only to the simple roots of this rescaled quadratic. All other roots remain near 0 by continuity, hence these are the two highest ordered roots for small positive epsilon. No claim about the remaining low cluster is inferred. The leading split roots satisfy d_-<=c*min(u,v)/n and d_+<=c*(u+v)/n: evaluate the quadratic at c*min(u,v)/n to get -c*uv/n^2<=0, and use the root sum. Thus the most immediate tight high-cluster rank-one patterns are locally consistent, not a counterexample.

This is a uniform-in-epsilon calculation for each fixed n,c,w,u,v, NOT a uniform estimate over n, all scales, or all multiplicities. It supplies no global indexed comparison.

## Exact bounded diagnostics and preserved false lead

Two-cluster runs use n=3..6, every a,b,c=1..n-1, p scale1, and q,r scales from {1/4,1,4}, then separately {1/100,1,100}. Each run covers 2016 input triples. Threecluster.py uses n=3,4,5; every positive multiplicity partition a+b+c=n; clusters 0,v,1 with v in {1/100,1/2,99/100}; all p,r templates and q=p or q(x)=(-1)^n p(-x). It covers 828 triples. These are restricted finite families, not a universal search. Inputs are explicitly real-rooted. Outputs are exact rational polynomials; SymPy's rational real-root isolation intervals with multiplicities are expanded and reversed to descending order, and total real multiplicity is checked against n. A strict violation is accepted only if the LOWER interval bound of LHS-RHS is positive. Uncertain interval signs and exact equalities are not promoted to proofs. No strict violation was certified. There is no inference that all inspected inequalities hold exactly, still less the universal conjecture.

Preserved diagnostic: n3, p=q=x^2(x-1), r=x^2(x-100), pair=x^3-101x^2+(200/3)x, triple=x^3-102x^2+134x-200/9. The triple's middle root lies strictly in (1,2): signs at 0,1,2 are -, +, -, and the third root lies above2. The pair's top two roots sum101. Hence middle(triple)+100>101. BUT the pattern i=2,j=1,k=2 requires l=2 for BOTH source alternatives, and lambda_2(r)=0. This is a countermodel only to an incorrectly strengthened statement with l=1. It receives zero credit and is not a conjecture refutation. separated-diagnostic.json retains exact isolating intervals and the index warning.

## Precise missing bridge and classical-adaptation objection

Single-step interlacing controls each root between adjacent old roots, but the conjecture compares TWO marginal root displacements at DIFFERENT indices after TWO operations. Subtracting two interlacing inequalities does not compare those displacements. A needed global lemma would bound

    lambda_(j+k-1)((p boxplus r) boxplus q)-lambda_k(r boxplus q)
       <= lambda_j(p boxplus r)-lambda_l(r)

for each literal source l, uniformly through collisions. Neither the hypergeometric overlap formula nor single rank-one interlacing establishes that lemma, and a reduction of arbitrary factors to rank-one factors preserving this four-term defect has not been proved.

The strongest classical-adaptation objection is substantial: the coefficient identities, overlap distribution, determinant lemma, rank-one interlacing, and elementary rescaled-cluster expansion are classical tools/routine adaptations. Even a full restricted-family result from them would not be a new full-scope endpoint. Source §4 already proves largest-root submodularity using pinching and interlacing. Reading Proposition4.4/Theorem4.8 shows the obstacle to simply changing its subscript1: positivity ABOVE ALL roots and a bound of at most one remaining larger root imply the requisite extremal-root comparison. A sign at an interior root does not identify its rank; intervening roots change the sign, and pinching/majorization does not give the same componentwise matching. No missing indexed induction lemma is hidden as an assumption here.

Disposition: HOLD / unresolved. No PROOF.md, no Lean/manuscript, no nomination or credit. Novelty clearance is also incomplete for the reasons in SCOUTING.md.
