# Source326 — prefreeze derivations, first checkpoint

This is research working prose, not a frozen author-proof nominee. Real Banach spaces throughout unless an explicit realification paragraph says otherwise. No correctness/contribution/count assignment. All source operations are stipulated true.

## Source interfaces and already-paid consequences

Let C_q(X) use the L2 Rademacher norm, q>=2. Ordinary AP means approximation uniformly on each compact set by bounded finite-rank endomorphisms, with no uniform bound on their norms. No separability is assumed. Source main theorem is for nonzero X; finite-dimensional X is allowed. Finite tuple arguments also cover the zero space separately.

The operative fixed-length norm c_m(Y) compares ell2 coefficient norms with L2 signed sums. Source lem:lifts gives bounded lifts with a=(2*24*D_g*sqrt(m))^-1 and b=(2*24*D_f*sqrt(m))^-1 when c_m(G*)<=D_g,c_m(F)<=D_f. Source lem:coefficient is a rank-at-least-two assertion for binary Fourier matrices, not an operator-rank bound. It uses d=ceil(2 log2 m)<m and min(ma,mb)>=80d(d+1)^2. Source lem:growth turns w_(n-2m)(T)<=2w_n(T) into w_(2n-4m)(T)>=c1 w_n(T) for any operator. Source thm:uniform-decay then excludes that slow decrease for finite-rank operators, using one fixed operator's Hilbert factorization. It also covers their operator-norm closure.

With q,r>=2,C,D>=1 choose m so min(m^(1/r)/(576D),m^(1/q)/(48C))>=80d(d+1)^2. Let D_g=12D m^(1/2-1/r),D_f=C m^(1/2-1/q). There are source constants c1>0, integer K0>log2(1/c1), n0=4m(K0+2)+2, and rho_N=1 before n0 and 2^-floor((N-n0)/(2m)) after n0. These do not depend on dimension, separability, rank, or approximation bounds. This gives a genuine exponential-in-N bound, with a non-effective coefficient-minimization constant in n0.

Source lem:compact-domain gives, for each finite-dimensional E subset X, G, compact injective J:G->X and contraction i:E->G with Ji=inc_E, ||J||<=2, c_m(G*)<=12 c_m(X*). Its quotient construction does not make coordinate truncations descend. AP is used exactly to approximate J via S_j J, not to bound S_j. Source already states the uniform K-constant theorem, entropy duality, and the Grothendieck-pair consequence. They are not candidates here.

The old authored histories read at exact selected extents discuss these mechanisms and distinguish operator rank from binary rank. Their external family statements/statuses are not premises. No historical clearance is inferred from the scan.

## A fully compatible operator transfer to develop

For T:X->Y, use the compact-open approximation condition:
for each compact M subset X and epsilon>0 there is finite-rank R:X->Y with sup_M ||Rx-Tx||<epsilon.
Assume C_r(X*)<=D and C_q(Y)<=C; no cotype of X or Y*, no AP of either dual, no nonzero/separability/reflexivity assumptions are inserted.

For finite-dimensional E subset X construct J:G->X as above. Approximate T on closure J(B_G), so R_j J -> TJ in operator norm. Then source thm:uniform-decay applies to TJ:G->Y. Its norm is at most 2||T||, while its domain dual has precisely the required fixed-length cotype. Pull back a Walsh input in E through i. This yields w_N(T)<=2rho_N||T||. This route works with unbounded ||R_j||: only R_j J has an operator-norm limit.

If X has AP, choose R=T S on compact M. If Y has AP, approximate on T(M) and choose R=S T. Thus either endpoint's ordinary AP is sufficient for this transfer; AP of a dual/subspace/quotient is never needed. This is the strongest direct compatible composition of the two source mechanisms, and is not by itself being treated as substantial.

The next question is whether this Walsh estimate yields a controlled K-convex-operator norm and factorization through a K-convex space. These are different claims. Pisier 1980 already defines R(T)=sup_n||Rad_n tensor T|| and proves cotype-two factorization for compact-open approximable operators (Cor.2.16), by a tensor/nuclear decomposition. Hinrichs 1999 is an exact operator-Walsh comparator; its title/abstract are not enough to import any theorem. Actual proof access is still being pursued.

## Why deleting all approximation is not a target

Pisier 1983 Theorem 3.2 embeds E=ell1 isometrically into a separable X with X and X* both cotype two (one may choose X separable). Sections 2 and 3 construct it by graph-quotient extensions with cotype constants that do not accumulate under iteration. Theorem 3.1 and Remark 3.6 explicitly prohibit AP for the infinite-dimensional constructed spaces. Since ell1 has only trivial type, this is a concrete obstruction to unconditional AP removal, independent of any failed naive approximation argument. Original Section 1 dependencies and missing scan formulas are being read/recovered; no bare catalogue assertion supplies this comparison.

## Further prefreeze feasibility direction

The source compact domain handles one tuple length. It is natural to test whether nested finite-dimensional enlargements at increasing lengths can yield one compact domain with finite dual cotype at a slightly weaker exponent. Dyadic weights and a length-dependent jump introduce a factor 2^L; choosing available tuple lengths to grow rapidly may turn this into a small power of tuple length. This is an exploratory construction, not a theorem or a fixed scope. Classical compact factorization may already subsume it, and no priority or substantiality is inferred.

## Completion of the source operator reduction (not a nominee)

Fix q,r,C,D,m and the source decay sequence once. For each finite Walsh input x=(x_u), let E be its span. Choose source J and i for that E and the fixed m. Choose finite-rank R_j:X->Y with sup_{closure J(B_G)}||(R_j-T)x||<1/j. Then R_j J has finite rank and converges to TJ in norm. Its norm need not be bounded through ||R_j||; convergence itself gives the appropriate norm limit. The source norm-closure assertion applies with c_m(G*)<=12 D m^(1/2-1/r) and c_m(Y)<=C m^(1/2-1/q). Thus

    ||W_N^T x|| = ||W_N^(TJ)(i x)||
                 <= rho_N ||TJ|| ||i x||
                 <= 2 rho_N ||T|| ||x||.

Taking the supremum proves w_N(T)<=2rho_N||T|| for all N. This covers zero inputs and T=0. If X has ordinary AP, compact-open approximation is supplied by TS_j; if Y has ordinary AP, it is supplied by S_jT on T(M). Neither implication asserts AP passes to a subspace, quotient or dual. Nonseparable endpoints cause no problem: every input and compact test set is handled directly. No uniform approximation constant enters.

At q=r=2, Pisier's original 1980 Corollary 2.16 already gives the stronger Hilbert-factorization conclusion for precisely this compact-open approximation condition (domain dual and range cotype two), with gamma_2(T)<=C||T||. Its actual Section 2 tensor decomposition iterates a small remainder in nuclear norm; this is a proved compatible operation, not a missing BAP assumption. It is paid. For other exponents, the source Walsh transfer is also paid. The earlier question about general K-convex operator factorization is not a nominated theorem or a claimed unresolved world problem. The 1981 projection/semigroup arguments were read, but the later Hinrichs operator comparator could not be read; no theorem is imported from its abstract and no novelty conclusion is based on it.

## Completed AP-removal comparison

The original Pisier 1983 Sections 1–3, including their extension construction and iteration leading to Theorems 3.1–3.2 and Remark 3.6, were read before freezing. Missing scanned formulas were visually recovered. Taking E=ell1 in the actual embedding theorem gives the obstruction described above. The original paper uses a first-moment Rademacher normalization in places; comparison here is existential through classical moment equivalence, not a transfer of numerical constants. No AP-removal nominee is advanced.

## Feasibility calculations leading to the frozen compact-factorization scope

These calculations motivated the frozen statement; this completion records them durably. The source compact-domain lemma fixes m, so independently choosing G_m does not give one compact domain with finite cotype. A direct sum also loses the injectivity needed for a unique linear lift of an arbitrary compact image.

Instead require level l to supply all moment lengths m<=M_l=2^(2^l). Given m, the first admissible level L satisfies 2^L<=2(1+log_2 m). P_L collapses the first L+1 coordinates into coordinate L with weights 2^(L-h), preserving the weighted sum j exactly. Its norm is at most 2^(L+1). Together with the source shift identity QR=Q, this gives

    c_m(G*) <= 48 D (1+log_2 m) m^(1/2-1/r)

for one quotient G and every m. Decreasing rearrangement then gives the stated cotype-s bound for every s>r. The logarithmic loss is summable after multiplying by k^(-1/r) and raising to s>r. No endpoint assertion is hidden.

To include a whole compact image K, insert finite eta_l-nets into E_l, with eta_l=2^(-2l-4). The representatives z_0=v_0 and z_l=2^l(v_l-v_(l-1)) telescope to x in K, have norm squared at most 793/768, and have uniformly vanishing square-sum tails with finitely many possible coordinate values. Their quotient images therefore form a compact set. Injectivity of J makes that lift independent of choices and yields a linear compact U=J^(-1)T. Adding a prescribed finite-dimensional E to E_0 preserves every estimate.

The exact statement was then frozen, unchanged, at SHA256 fbd2600bdc050aac6e4ab130c3d4a35f88db4fa2af26b5e2b163ee922d760433. AUTHOR-PROOF.md develops all steps at that scope. No intermediate AP, primal cotype, K-convexity or complex version is used.

## Author-side compatibility checks

The quotient kernel is closed because j is bounded. P_L and R preserve j, and injectivity of J proves QP_L=Q and QR=Q. Truncations of j establish compactness only and are never asserted to descend to G. Finite-level lifts need not be linear: independent choices at each level are allowed on a finite sign cube, and the square-sum estimate places every atom in H. Quotient duality is applied to the surjective finite moment map V_m, whose displayed right inverse proves surjectivity.

The first-k Rademacher norm is bounded by the full norm by conditional Jensen; this is why rearrangement yields cotype s. The compact lift set is closed by uniqueness and closedness of K, not by continuity of arbitrary net choices. Zero spaces, zero maps and zero E are included. Reflexivity follows from a countable ell2 sum of finite-dimensional spaces and a closed quotient, not from type.

These are author calculations, not an independent correctness verdict. No mathematical obligation within the frozen statement is presently identified as unresolved. Literature distinctness and substantial contribution are not decided here.

## Late original interpolation comparison (target unchanged)

After the statement and author proof were written, a narrow final comparison search located Jarchow–Matter 1988, Interpolative constructions for operator ideals, Note di Matematica 8, 45–56, DOI 10.1285/i15900932v8n1p45. The publisher's original scan was fetched and ALL twelve pages were visually read, including the full proof operations and references. This is a late read, not a prefreeze clearance claim.

The exact general operation is their (10), proved using the interpolation couple (domain/ker(T), range): for operator ideals A,B, an operator in A^s intersect B^i factors as R S with R in A^theta and S in B_(1-theta). Their (12)(a) gives cotype weakening (C_r)_(1-theta) subset C_(r/theta). Their concluding (13) concerns separate type/cotype estimates on two factors, with a K-convex range hypothesis; it does not state cotype of the intermediate identity.

The strongest directly compatible application here is concrete. Since X* has cotype r, T*:X*->Y* has operator cotype r with constant at most D||T||. It is compact by Schauder's theorem. In (10) take A=K and B=K intersect C_r. K is the closed injective/surjective ideal of compact maps and C_r is injective, as recalled in the actual paper. For each theta in (0,1), this yields

    T* = R_theta S_theta,
    R_theta and S_theta compact,
    S_theta of operator cotype r/theta.

Compactness of R_theta follows from K^theta=K. Compactness of S_theta follows from B_(1-theta) subset K_(1-theta)=K, using (5)(c); alternatively a bounded sequence with convergent image under the compact dominating map has Cauchy images under the interpolatively dominated map. The cotype inclusion may be checked directly rather than invoking the proof that (12)(a) omits: if ||Sx||<=c||Ax||^theta||Bx||^(1-theta), A has cotype r and B is bounded, then

    (sum ||Sx_i||^(r/theta))^(theta/r)
       <= c (sum||Ax_i||^r)^(theta/r)
              (max_i||Bx_i||)^(1-theta)
       <= c C_r(A)^theta ||B||^(1-theta)
              Rad_2(x_i),

because max_i||x_i||<=Rad_2(x_i). Thus that weaker operator-level conclusion is paid, including simultaneous compactness of its factors.

This comparison does not turn the output-side map S_theta into an identity estimate on its intermediate space. It controls Rad_2 of preimages in X*, whereas the frozen conclusion controls Rad_2 directly in G*. No bound on such preimages, no identity factorization, and no one-space-all-exponents assertion is supplied by (10) or (13). These are exact interface distinctions, not evidence that no different classical argument proves the frozen target. The hierarchy/P_L/moment argument in AUTHOR-PROOF.md supplies the required identity estimates and unique compact lift at the unchanged frozen scope.

The nominee remains an author proof for independent contribution review; this late original comparison receives no favorable grade from the author. No source truth or old target was revisited.
