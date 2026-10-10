# I71 — simultaneous variation and aggregate-energy algebra rounding

**Disposition: no nomination. AR_K remains unproved and unrefuted, including exact B=I.** This continuation produces an actual linked, exactly normalized sequence with *strict local maxima for the full simultaneous basis objective* whose chosen-basis normalized error tends to 2, while its global orbit distance tends to zero. Thus even negative-definite full Hessian, positive diagonal signs, and globally optimal individual plane moves do not give the proposed entrance. This strengthens I69's saddle test; it does not refute AR or an argument using true global comparisons.

The second route gives a common spectral-cut construction with total slice energy, an all-three-slot compression estimate, a cap-preserving **global** bookkeeping identity for an arbitrary refinement tree, and an explicit terminal certificate. The missing estimate is the cumulative loss needed to reach that certificate. A real matrix-family counterexample proves that total energy and an output cap alone cannot pay this estimate; it fails the linked Gram identity and is not an AR counterexample. A separate exactly diagonal linked test shows why a dimension-independent number of spectral stages is not a valid stopping argument.

These are author-level technical partials and method obstructions, not independent proof/significance acceptance or a ninth finding. Eight findings remain accepted; I68's C66 verdict remains PASS ORIGINAL / TECHNICAL ONLY, and I70's symplectic screen is not duplicated. No agents, staging, commits, publication, shared edits, or prior-seal changes were performed.

## 1. Contract and independently audited inputs

All statements **and proof operations** at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are premises. None of the new I69 deductions is thereby an upstream axiom. The complete inherited assignment and returned I69 report are frozen verbatim from the I71 task JSON in `../sources/i71_global_variation_algebra_rounding/brief.txt`. Prior immutable evidence is hash-referenced, not recursively copied. The only mutable paths are exactly `README.md`, `frontier/README.md`, `frontier/TEN-FINDINGS.md`, and `frontier/iterations/README.md`.

Write, for a fully symmetric real cubic on R^m,
\[
 (T_x)_{ij}=T(e_i,e_j,x),\quad B_T=\sum_rT_r^2,
 E(T)=\sum_{r,s}\|[T_r,T_s]\|_F^2,\quad
 \beta(T)=\|B_T-I\|_F^2,\quad R=E+\beta.
\]
All indices/pairs are ordered and all norms unnormalized. Let
\[
 d(T)^2=\inf_{U\in O(m)}\|T-D_U\|_F^2,
 \qquad D_U=\sum_i u_i^{\otimes3}.
\]
AR_K requires, for every fixed finite K, one modulus rho_K(t) tending to zero at zero, uniformly over **all** m and all such T with B_T<=KI, satisfying d(T)^2/m<=rho_K(R/m). Signs are absorbed into U. This report does not produce that modulus or an all-orientation lower-bound counterexample.

The following input audits distinguish original proofs from the new arguments below.

* **I65/I69 linkage: PASS ORIGINAL as used.** For Delta_T:x->T_x, direct exchange of symmetric tensor indices gives Delta_T^*Delta_T=B_T. In particular ||T_x||_F<=sqrt(K)||x|| under the cap, and ||T||_F^2=tr B_T. Also the crossing contraction gives ||Phi_T-P_T||_HS^2=E(T), with P_T=Delta_T Delta_T^*. No positivity or algebra structure of a rounded spectral projection is inferred.
* **I65 scalar sign rounding, repeated in I69: PASS ORIGINAL.** For z,h>=0, (z-1)^2<=(z^2+h-1)^2+2h. The difference at h=0 is z(z+2)(z-1)^2, and its h derivative is 2(z^2+h). In any basis, with M the non-pure-diagonal mass, summation proves signed cost<=beta+3M. Under B<=I, the sharper cost<=tr(I-B)+2M follows from 0<=|T_iii|<=1. These apply without a greedy-maximizer hypothesis and are used in §5.
* **I69 Walsh identification and simplicial normalization: PASS ORIGINAL as used.** Nontrivial normalized characters of (F_2)^k form an ONB of the zero-mean subspace in R^(m+1). Their triple product sums are 1/sqrt(m+1) exactly when their labels sum to zero. Multiplication by sqrt((m+1)/(m-1)) gives I69's tensor. The elementary partial-permutation calculation in §3 independently verifies its normalization and commutator sign. Neither the I69 Hessian observation nor parent evidence replay is assumed as a theorem.
* **I65 supplied codimension bound: PASS ORIGINAL as used.** For an m-plane in R^(m+k), its projected coordinate columns form a Parseval frame. Keeping m columns A gives ||A||op<=1 and m-||A||_F^2<=k. Full SVD polar completion U, including singular A, has ||A-U||_F^2<=k. Each of the three tensor telescoping sums is bounded by ||A-U||_F, because its paired-column map is (A tensor A)J, (U tensor A)J, or (U tensor U)J, of norm at most one. The discarded projected cubic has norm<=sqrt(k). Therefore the original bounds 16k and, after scaling, 32s^2k+2m(s-1)^2 follow. The factors in §3 are explicit; no general factor discovery is asserted.

I69's complete-deflation residual identity, its nonmonotone residual example, multiscale supplied-block budgets, and scalar unitalization are preserved unchanged and are **not analytic inputs to the new propositions**. They receive no additional independent full-proof verdict here. In particular no state is asserted reachable by deflation from exact B=I. The accepted R014/CE61 theorem and original-cap smooth-source interface retain their reviewed scopes. New §3 and §§4–5 are independent arguments, not repairs to I69.

## 2. Route A: exact simultaneous and finite comparisons

Put F(U)=sum_i T(u_i,u_i,u_i). For every T,
\[
 d(T)^2=\operatorname{tr}B_T+m-2\max_U F(U).                 \tag{2.1}
\]
At a true global maximizer, express T in that basis. Sign changes give c_i=T_iii>=0. Let C_ij=T_iij. First variation gives C=C^t, and for every skew matrix A,
\[
 H_T(A):=6\sum_iT(e_i,Ae_i,Ae_i)+3\operatorname{tr}(CA^2)\le0. \tag{2.2}
\]
This includes cross terms between different plane directions. It follows by differentiating exp(tA)e_i, not by summing independent plane tests.

### 2.1 Correlated skew directions, with covariance retained

For any symmetric zero-diagonal S and independent centered variance-one random variables g_i, use
\[
 A_{ij}=(g_i-g_j)S_{ij},\quad s_i=Se_i.
\]
For j,k different from i,
E[A_ji A_ki]=(1+delta_jk)S_ij S_ik; also
E[A^2]=-S^2-diag(S^2). Therefore, without dropping the shared-g_i covariance,
\[
 \begin{split}
 \mathbb E H_T(A)={}&6\sum_iT(e_i,s_i,s_i)
       +6\sum_{i,j}T_{ijj}S_{ij}^2\\
       &-3\operatorname{tr}(CS^2)-3\sum_i c_i(S^2)_{ii}.       \tag{2.3}
 \end{split}
\]
The covariance identity holds even before imposing stationarity. At a maximizer it is nonpositive for **every** S. One can further average S over off-diagonal parts of tensor slices; every term in (2.3), including the trace term, must remain. The sequence in §3 satisfies the full stronger deterministic condition (2.2), so no choice of such covariance can make these necessary second-order conditions alone imply AR-sized error at that basis.

### 2.2 Actual global finite comparisons

Let Q=I+Z be any orthogonal matrix and z_i=Ze_i. Cubic expansion, C=C^t, and Z+Z^t=-Z^tZ give
\[
 F(Q)-F(I)=3\sum_iT(e_i,z_i,z_i)+\sum_iT(z_i,z_i,z_i)
              -\tfrac32\operatorname{tr}(CZ^tZ).           \tag{2.4}
\]
Thus global maximality gives the nonpositivity of (2.4) for **all** orthogonal Q, not merely small Z. The cubic term is not a negligible error at a macroscopic replacement. Formula (2.4) applies equally to replacing many coordinates simultaneously.

For a unit v, the concrete Householder comparison Q=I-2vv^t is
\[
 F(Q)-F(I)=-6v^tCv+12T(v\circ v,v,v)
                   -8\left(\sum_i v_i^3\right)T(v,v,v).    \tag{2.5}
\]
This also allows determinant -1, as the target is O(m). The cap implies ||C||op<=sqrt(K): Cx is the vector of diagonal entries of T_x. Together with ||v\circ v||<=1 and |sum v_i^3|<=1, this proves |F(Q)-F(I)|<=26sqrt(K). Applying that estimate successively bounds the change along any supplied sequence of r reflections by 26r sqrt(K); it is not a lower bound on the improvement obtainable by such a sequence.

These are developed global comparisons, not a claim that their mere existence solves the maximization problem. The next section proves that replacing them by their quadratic consequences is invalid. A general proof would have to select useful large Q from T and E, or otherwise exploit (2.4) at nonlocal scale. Random skew averaging cannot silently strengthen “local maximum” into “global maximum.”

## 3. A linked, exactly normalized strict-local-maximum obstruction

**Proposition 3.1.** For every k>=2, set m=2^k-1 and index coordinates by nonzero elements of (F_2)^k. Define
\[
 A_{abc}=\mathbf1_{a+b+c=0},\quad D_{abc}=\mathbf1_{a=b=c},
 \qquad T^{(m)}=\frac{A+3D}{\sqrt{m+8}}.                     \tag{3.1}
\]
Then:
\[
 B_{T^{(m)}}=I,\quad
 E(T^{(m)})=\frac{38m(m-1)}{(m+8)^2},\quad
 \frac{\|T^{(m)}-D\|_F^2}{m}=2-\frac6{\sqrt{m+8}}\to2.   \tag{3.2}
\]
The identity basis is a strict local maximum of the **full** F on O(m), has positive diagonal entries, and is globally optimal along every individual coordinate-plane replacement including sign choices. Nevertheless d(T^{(m)})^2<=236 for every m in the sequence. Thus its global normalized distance tends to zero.

**Proof of the linked identities.** All entries are invariant under every permutation of the three indices. For a nonzero r, A_r swaps a with a+r when both labels are nonzero and kills e_r. It is a symmetric partial permutation with
\[
 A_r e_r=0,\quad A_r^2=I-e_re_r^t,\quad
 [A_r,A_s]=-(e_re_s^t-e_se_r^t)\quad(r\ne s).              \tag{3.3}
\]
For the commutator, the two compositions agree except at labels r,s: their difference sends e_s to -e_r and e_r to e_s. As D_r=e_re_r^t, all cross terms in sum_r(A_r+3D_r)^2 vanish, and the square sum is (m-1+9)I.

For r!=s, write L_rs=[D_r,A_s]+[A_r,D_s]. Its four nonzero entries connect r and s separately to r+s; each has magnitude one. The support is disjoint from the two entries of [A_r,A_s]. Thus ||L_rs||^2=4, their inner product is zero, and
\[
 \|[A_r+3D_r,A_s+3D_s]\|^2=2+9\cdot4=38.
\]
Summing all m(m-1) ordered unequal pairs and scaling proves E in (3.2). The tensor norm is m and F(I)=3m/sqrt(m+8), giving the distance formula.

**Proof of strict local maximality.** Repeated-index entries with two different labels vanish, so C=3I/sqrt(m+8), stationarity holds, and each c_i is positive. For every skew Q, put v_i=Qe_i. Since ||A_i||op<=1,
\[
 \begin{split}
 H_{T^{(m)}}(Q)
 &=\frac{6\sum_i v_i^t A_i v_i-9\|Q\|_F^2}{\sqrt{m+8}}\\
 &\le-\frac3{\sqrt{m+8}}\|Q\|_F^2.                       \tag{3.4}
 \end{split}
\]
Here the diagonal cubic contributes -9||Q||^2: its first term is zero because Q_ii=0. Negative definiteness in the exponential coordinate chart proves strict local maximality for each m. Its neighborhood need not be uniform in m; no such assertion is used.

Restricting the cubic to any two coordinate axes gives 3(x^3+y^3)/sqrt(m+8), because A has only distinct-index entries. For any orthonormal pair in that plane, the sum of these two cubic values is at most 6/sqrt(m+8): the sum of absolute cubes in each unit column is at most one. Hence every single finite plane move, with either column sign, has F<=F(I). This is stronger than I69's flat-plane saddle, but is still a restricted global comparison.

**Proof of a good global orientation.** Put W=A/sqrt(m-1) and s=sqrt((m-1)/(m+8)). Character orthogonality identifies W with the classical simplicial tensor on the zero-mean hyperplane in R^(m+1). The supplied codimension-one polar construction audited in §1 gives a basis U with
\[
 \|W-D_U\|^2\le32\frac{m+1}{m-1}
       +2m\left(\sqrt{\frac{m+1}{m-1}}-1\right)^2\le100.
\]
The last inequality follows from (m+1)/(m-1)<=3 and sqrt(1+2/(m-1))-1<=1/(m-1); 2m/(m-1)^2<=4 for m>=2. Because W and D are orthogonal as tensors,
\[
 \|T^{(m)}-W\|^2=m(1-s)^2+\frac{9m}{m+8}\le18,
\]
using (1-s)^2<=1-s^2. Therefore the same global U costs at most 2*100+2*18=236. This U is constructible from the character transform and a full SVD of a specified projected coordinate frame. No unknown dilation is postulated. In particular F(U)>=m-118, which eventually exceeds F(I) by order m. This is an actual large finite comparison, not a Hessian-based inference. ∎

The proposition refutes a dimension-uniform “every second-order local maximum rounds” theorem, even if strict local maximality and all finite individual plane comparisons are included. It **does not** refute AR, the use of (2.4) at a true global maximizer, or an algorithm that takes sufficiently large global moves. Its construction uses the old simplicial/Walsh algebra plus an explicit small diagonal perturbation; it is a method obstruction, with no priority or substantial-result nomination.

## 4. Route B: common spectral cuts with actual aggregate energy

### 4.1 One common cut, proved directly from the source operation

Let X,Y_1,...,Y_N be real symmetric d by d matrices. Diagonalize X with eigenvalues lambda_i. For a width h>0 and a uniformly random shift theta in [0,h), partition the line into intervals [theta+zh,theta+(z+1)h); let P_a be their spectral projections. Put
\[
 q(\theta)=\sum_r\left\|Y_r-\sum_aP_aY_rP_a\right\|_F^2,
 \quad C_X=\sum_r\|[X,Y_r]\|_F^2,\quad A_Y=\sum_r\|Y_r\|_F^2.
\]
A pair of eigenvalues is separated with probability min(1,|lambda_i-lambda_j|/h). Consequently
\[
 \mathbb E_\theta q(\theta)
 =\sum_{r,i,j}\min\{1,|\lambda_i-\lambda_j|/h\}|(Y_r)_{ij}|^2
 \le\frac{\sqrt{C_X A_Y}}h.                              \tag{4.1}
\]
Replacing X by the bin midpoints costs at most d h^2/4 and makes it commute with every compressed Y_r. Empty bins and repeated eigenvalues cause no problem. No matrix-count factor or bound on ||X||op occurs in (4.1).

This is the random-grid version of the actual common-cut/Cauchy–Schwarz operation in Bansil–Kachkovskiy §4, especially Remark 4.1. Their optimized breaking points use the same aggregate sum of entry squares and then bound the total normalized Y-energy by N. Here that energy remains A_Y/d. This direct proof does not import external theorem correctness, or the source's precise optimized exponent/constants, as a new premise.

For a linked tensor S on R^d with B_S<=KI, choose X=S_g with g a fresh centered random vector of covariance I (Gaussian or independent random signs). Conditional on S,
\[
 \mathbb E_g C_X=E(S),\qquad A_Y=\|S\|^2\le Kd
 \quad(Y_r=S_r).
\]
Cauchy–Schwarz in g gives expected two-slot loss at most sqrt(Kd E(S))/h. The next step pays for the third slot rather than retaining a generally nonsymmetric family.

### 4.2 Common compression of all three slots

For any orthogonal decomposition P=(P_a) of the *same* space, define
\[
 \Pi_P S=\sum_aP_a^{\otimes3}S=:S',\quad
 L=\|S-S'\|^2,\quad
 q=\sum_r\|S_r-\sum_aP_aS_rP_a\|^2.
\]
In a basis respecting P, q counts entries with the first two block labels different, whereas L counts entries with any labels different. A pattern with two equal block labels contributes a proportion 2/3 to q; three distinct labels contribute proportion one. Therefore
\[
                         q\le L\le\tfrac32q.            \tag{4.2}
\]
This multiplicity argument is invariant under a common basis change; it uses full symmetry essentially.

**The cap is preserved exactly.** If v=sum_a v_a, then
\[
 S'_v=\bigoplus_a P_a S_{v_a}P_a,
 \quad \|S'_v\|_F^2\le\sum_a\|S_{v_a}\|_F^2
                 \le K\sum_a\|v_a\|^2.
\]
The Gram identity makes this B_{S'}<=KI. In fact
B_{S'}<=sum_a P_a B_S P_a, as quadratic forms. This is a comparison with the **pinching** of B_S; no false global inequality B_{S'}<=B_S is used.

Combining (4.1)–(4.2), one random pencil and common three-slot cut has
\[
 \mathbb E L\le\frac{3}{2h}\sqrt{Kd E(S)}.                 \tag{4.3}
\]
Thus there is a realized choice with at most this loss. But (4.3) by itself is not an iterative rounding theorem.

## 5. Global refinement budget and a paid stopping certificate

### 5.1 No per-level normalization reset or hidden square-root accumulation

Start with arbitrary T having B_T<=KI. Let P_0,P_1,...,P_N be any finite sequence of successively refined orthogonal decompositions, including different new bases within previous blocks. Write T_j=Pi_{P_j}T and assume P_0 is the whole space. These are nested orthogonal projections on tensor space. Put L_j=||T_j-T_{j+1}||^2 and L_tot=sum_j L_j. Then
\[
 \|T-T_N\|^2=L_{\rm tot},\qquad
 \operatorname{tr}B_{T_N}=\operatorname{tr}B_T-L_{\rm tot},\qquad
 B_{T_N}\preceq KI.                                      \tag{5.1}
\]
The losses are orthogonal; their square roots are not added across depth.

Both residuals can be compared **directly with the original tensor**. For any two capped fully symmetric tensors T,S of cap K and D=T-S,
\[
 \|B_T-B_S\|_F\le2\sqrt K\|D\|_F,
 \left(\sum_{r,s}\|[T_r,T_s]-[S_r,S_s]\|^2\right)^{1/2}
                      \le4\sqrt K\|D\|_F.              \tag{5.2}
\]
For the first inequality use Delta_T^*Delta_T-Delta_S^*Delta_S=Delta_T^*Delta_D+Delta_D^*Delta_S. For the second expand the difference as [D_r,T_s]+[S_r,D_s]. For any symmetric A_s with sum A_s^2<=KI,
\[
 \sum_{r,s}\|[D_r,A_s]\|^2
 \le2\sum_{r,s}(\|D_rA_s\|^2+\|A_sD_r\|^2)
 \le4K\sum_r\|D_r\|^2.
\]
The triangle inequality in the whole ordered array proves (5.2), without multiplying by its number of slices. Applying (5.2) once to T,T_N gives
\[
 \sqrt{\beta(T_N)}\le\sqrt{\beta(T)}+2\sqrt{KL_{\rm tot}},
 \quad \sqrt{E(T_N)}\le\sqrt{E(T)}+4\sqrt{KL_{\rm tot}},
\]
\[
                       R(T_N)\le2R(T)+40KL_{\rm tot}.    \tag{5.3}
\]
This accounts for every residual change in an arbitrarily deep refinement without assuming monotonicity of E+beta. It is a bookkeeping bound; it does not bound L_tot.

For a cut performed simultaneously in the current blocks, summing (4.3) and applying Cauchy–Schwarz across blocks gives
\[
 \mathbb E[L_j\mid T_j]\le\frac{3}{2h_j}\sqrt{Km E(T_j)}. \tag{5.4}
\]
Writing ell_j=||T-T_j||^2/m and epsilon=R(T)/m, a choice satisfying the expectation bound obeys the conservative recurrence
\[
 \ell_{j+1}-\ell_j\le\frac{3\sqrt K}{2h_j}
                   \bigl(\sqrt\epsilon+4\sqrt{K\ell_j}\bigr). \tag{5.5}
\]
Neither (5.3) nor (5.5) gives a small final ell for an unbounded number of stages. We do not replace E(T_j) by initial E or discard the feedback term.

There is a further adaptation warning. E_g||D_g||^2=||D||^2 holds for a **fixed** D independent of fresh g. It cannot be applied after choosing D=T_j-Pi_{P(g)}T_j from that same pencil. The deterministic replacement is only ||D_g||^2<=||g||^2||D||^2. Equations (4.3) and (5.4) avoid this error by first bounding two-slot cut mass for each fixed pencil and then using (4.2); they never contract an adaptively discarded tensor and claim independent Gaussian isometry.

### 5.2 A terminal certificate not requiring supplied small blocks

For each final block W_a, dimension d_a, let S_a=T_N|_{W_a} and define its total centered-slice energy
\[
 V_a=\sum_{r\in W_a}\left\|(S_a)_r-
            \frac{\operatorname{tr}(S_a)_r}{d_a}I_{W_a}\right\|^2,
 \qquad V=\sum_aV_a.                                    \tag{5.6}
\]
If d_a=1 this is zero. If d_a>=2, full symmetry forces
\[
 V_a\ge\frac{2(d_a-1)}{3d_a}\|S_a\|^2\ge\tfrac13\|S_a\|^2. \tag{5.7}
\]
To prove this, let tau_r=tr(S_a)_r. The adjoint of trace contraction on Sym^3(R^d) is
J(v)_ijk=(v_i delta_jk+v_j delta_ik+v_k delta_ij)/3.
Its norm square is (d+2)||v||^2/3 and tr J(v)=(d+2)v/3. Hence ||tau||^2<=(d+2)||S_a||^2/3. Substitute into V_a=||S_a||^2-||tau||^2/d.

Choose any ONB in each block and sign its diagonal cubic coefficients positively. The mixed mass M of T_N is at most the energy of its blocks of dimension >=2, hence M<=3V. Scalar sign rounding from §1 and (5.3) give the entirely constructive certificate
\[
 \boxed{\quad
 \|T-D_U\|^2\le2\beta(T)+(1+8K)L_{\rm tot}+9V.
 \quad}                                                   \tag{5.8}
\]
Indeed D_U belongs to the range of Pi_{P_N}, so the initial projection loss adds **exactly** by Pythagoras: cost=L_tot+||T_N-D_U||^2. Use cost for T_N<=beta(T_N)+3M and beta(T_N)<=2beta(T)+8K L_tot. This includes small or zero terminal coefficients and costs all discarded tensor slots.

If initial B_T=I, cap one persists and tr(I-B_{T_N})=L_tot. The sharper scalar bound yields
\[
                  \boxed{\ \|T-D_U\|^2\le2L_{\rm tot}+6V.\ } \tag{5.9}
\]
No block-dimension bound, renormalization, inverse of B, or approximate density cap is present in these certificates. They give a general-cap stopping rule once a process actually reaches small L_tot and V. **No theorem here guarantees reaching it from small E+beta.** The missing step is not terminal normalization or cap repair.

### 5.3 Why a bounded number of stages is not a stopping proof

Even the exact linked tensor D_m can retain macroscopic V after many common spectral cuts. Let m=2^k and successively use the diagonal pencils D_g with sign vectors g that read the first N bits of the coordinate labels; take grids separating -1 and +1. There are exactly 2^N blocks for N<=k. All-slot compression leaves D_m unchanged, so L_tot=E=beta=0. On a block of dimension d, its trace vector has d entries equal to one, giving V_a=d-1. Thus
\[
                         V=m-2^N.                       \tag{5.10}
\]
No dimension-independent bound on the number of these binary cuts forces V/m small. This test does not make D hard to round—it is already diagonal—and does not refute algorithms with better stopping or useful choices inside degenerate eigenspaces. It identifies precisely why “repeat the energy estimate a bounded number of times, then scalarize the blocks” is incomplete. Paying potentially growing depth with the *actual*, often much smaller, cut loss remains necessary.

### 5.4 Total energy alone cannot supply the missing global theorem

There is a sharp nonlinked warning for extending BK purely as a matrix-family theorem. On R^d with d=2^k, put
\[
 Y_{j,1}=X_j/\sqrt{2k},\quad Y_{j,2}=Z_j/\sqrt{2k}
 \quad(1\le j\le k),
\]
where X=[[0,1],[1,0]], Z=diag(1,-1), and the subscript places the matrix on the jth real tensor factor. Then
\[
 \sum Y_r^2=I,\quad \sum\|Y_r\|_F^2/d=1,\quad
 \sum_{r,s}\|[Y_r,Y_s]\|_F^2/d=2/k\to0.                 \tag{5.11}
\]
Only the two orderings of X_j,Z_j at each site fail to commute. Their squared normalized commutator norm is 1/k^2.

Nevertheless the least aggregate squared distance to any commuting real symmetric family is **exactly d/2**. Fix a common ONB u_l of an arbitrary candidate family. For each unit u and site j, write x=<u,X_j u>, z=<u,Z_j u>. Since (aX_j+bZ_j)^2=(a^2+b^2)I, taking (a,b)=(x,z) gives x^2+z^2<=sqrt(x^2+z^2), so x^2+z^2<=1. Therefore the retained diagonal energy of all Y_r in any basis is at most d/2. Orthogonal projection onto the diagonal matrices minimizes squared error in that basis, so the error is at least d-d/2. The computational basis attains it by retaining all Z_j and replacing all X_j by zero.

This refutes a putative matrix-family rounding modulus using just total normalized energy, an output cap, and total normalized commutator energy. It does **not** refute AR. For k>=3, padding to d slices, the Gram matrix of this family has 2k eigenvalues d/(2k) and the rest zero, whereas sum Y_r^2=I. It violates Delta^*Delta=B, an invariant necessary for a fully symmetric linked tensor, regardless of a rotation of the slice labels. At k=1,2 one has d=2k, so this Gram argument alone does not exclude linkage; those finite cases are not used for the asymptotic obstruction. Thus a successful global energy decomposition must exploit linkage at its discovery/stopping stage, not only after rounding a generic matrix family.

## 6. Primary/source operations and significance limits

Fresh primary bodies, headers, UTC retrieval times, served versions, and exact PDF extractions are retained in `primary/manifest.json`. Versions below describe the actual responses, not a promise about later endpoints.

* [Bansil–Kachkovskiy, 2608.31000v1](https://arxiv.org/abs/2608.31000v1), Theorem 1.3 and §4/Remark 4.1: common breaking points minimize the sum of cut entry energies. Weighted averaging and Cauchy–Schwarz leave the total family energy before its replacement by N. Section 4 uses that actual lower operation with a shifted grid, not the theorem title. The source's iteration does not pay §5's growing-depth budget or preserve the linked third slot for free.
* [Li–Usevich–Comon, 1804.01358v2](https://arxiv.org/abs/1804.01358v2), §§2–4: the displayed objective is the **sum of squares** of cubic diagonal entries. The paper distinguishes stationary, Jacobi, local, and global diagonality and gives full Hessian formulas and a coupled-direction example. We do not identify that objective with F or import its convergence results as global rounding. The simultaneous-variation operation and the danger of plane-wise tests have clear antecedents. The additional calculation here is the exactly normalized linked sequence (3.1) with vanishing normalized residual and strict poor local maxima.
* [Faisal–Natarajan–Poremba, 2605.26096v3](https://arxiv.org/abs/2605.26096v3), §1.4, §§3–5: the captured PDF, dated October 6, gives per-term operator-norm error 200 epsilon^(1/3) for 2-local qubit Hamiltonians. An indexed older abstract displayed exponent 1/6; the search record is preserved. The proof extracts 2-by-2 Pauli coefficients, pinches at large gaps, and otherwise replaces coefficients by scalar trace parts. Distinct supports make snapping on a private qubit commute with the other term and preserve its commutator bound; shared-qubit removal eliminates the interaction. General linked slices have no supplied qubit-local decomposition or this bounded-stage support account. Aggregate squared error is also different from per-term operator error. In §5.4 discarding the small X-terms gives small error per term but nonvanishing aggregate squared error. That family has two labels on each site, violating the theorem's distinct-support hypothesis, and is not an invocation or refutation of it.
* [Fox, 2004.12343v2](https://arxiv.org/abs/2004.12343v2), Definition 3.4, Corollary 3.7 and Remarks 3.8/3.12: the simplicial algebra and its compressed coordinate realization are classical, with Griess–Harada attribution. The base W in §3 is that algebra in character coordinates. No general associative completion is inferred from its realization.
* [Auddy–Yuan, 2007.09024v2](https://arxiv.org/abs/2007.09024v2), Theorem 3.1 and its polar/tensor telescoping proof: supplied factors and singular-value control precede the rounding step. The audited I65 construction is an elementary supplied-frame variant. Neither proves existence or small codimension of factors for arbitrary AR data.

The pinned entropy `rigidity.tex` was read at the actual exact-jet, simultaneous-diagonalization, compactness, and forward-Lipschitz operations; the Mahler equality passage was read at its Gaussian spectral-moment contraction. Exact zeros give a common basis. They do not supply a positive lower bound on max F from a small normalized residual. I69's frozen actual operator-algebra/CPV/PPT/BDS passages and norm/scope objections remain immutable references; no additional theorem from those sources is imported here. In particular cb/Haagerup hypotheses, exact PPT, exact associative ideals, and a fixed-dimensional total-distance tube are not substituted for the missing estimate.

The positive claims here reduce explicitly to common spectral cutting, full-symmetry multiplicity counting, contraction/Gram inequalities, nested orthogonal projection, and the previously paid scalar rounding. The negative claims are exact test constructions with proofs above. These are useful technical progress on entrance conditions, **not** a completed newly upstream-enabled rounding bridge. A bounded corpus/literature search establishes neither worldwide priority nor absence of a shorter reduction. No MathDB score or count increment is proposed.

## 7. Entropy scope and preserved objections

There is no new entropy law. The original target still requires AR at the general repaired cap, not merely exact B=I. For an actual centered isotropic smooth source density exp(-V), with smooth V and 0<c_-I<=D^2V<=c_+I, retain its **original** coefficient cap B_X<=KI and set u=delta/m. R014 gives
\[
 \eta\le\chi_K(A_Ku),\quad
 e_Z\le4000u/c_K+(2+2340K)\eta,
\]
with repaired Z of cap 4K and ||Z-X||^2/m<=26eta. If a future proof supplies rho_(4K), the existing one-global-orientation reduction gives
\[
 \frac{d_m(f)^2}{m}\le\frac4{q(0)^2}
 \left[2000u+104\eta+4\rho_{4K}(e_Z)\right].             \tag{7.1}
\]
The coefficient triangle-square bound is 52eta+2rho; forward q-Lipschitzness/Poincare doubles that part and adds 2000u, while P>=q(0)I and covariance comparison give the displayed final factor. This is the accepted conditional interface, not an application of the presently unproved stopping estimate. No square-root rate, unrestricted U theorem, or cap inherited through approximation is asserted.

All original objections remain: the heavy star is uncapped and cross-slot deletion is expensive; it is not a realized density counterexample. Rank alone does not preserve input compatibility, and regularized Q is not q(S^(1/2)L). Arbitrary flag deficits have cancelling negative log scales; a missing k-dimensional coupling costs 2k only after the good marginal cost is paid. Generic channels, the diluted harmonic block and §5.4's matrix family lack the required AR conclusion or linkage. Source approximation gives neither coefficient convergence nor preservation of the original cap. Supplied factors/small blocks, fixed-dimensional local tubes, and previous quadrature approximations remain within their original scopes. Original failures and I69's nonmonotone residual example are preserved, not overwritten or repurposed as AR counterexamples.

## 8. Evidence and exact remaining task

Run from the project root:

```bash
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i71_global_variation_algebra_rounding/verify.py
```

The verifier is read-only and offline. It checks the active I71 `seal-v2.json`, exact brief binding, immutable references and exact four-ledger allowlist, fresh primary bytes and PDF replay, selected read-passage bindings, new fixed-domain corpus search **line multisets**, and newly written finite diagnostics. The first `seal.json` is preserved byte-for-byte, with the first report/verifier and its evidence PASS archived. A final analytic boundary check supplied the previously omitted k>=3 qualifier in §5.4; `correction-history.json` records that scope correction, and the verifier also checks every original sealed hash against unchanged files or those explicit archived originals. No inherited proof or mathematical constant was changed. It also runs the unchanged I69 verifier; that in turn checks the full 13,223-entry/749-manuscript tree, 10,373 blobs, fixed 9,340-file corpus, separately inventoried 1,033 outside blobs, all 26 pins, prior immutable references and preserved failures. This avoids recursive evidence copies and does not refresh any old seal.

The new independent diagnostic program uses only the standard library and imports no previous diagnostic modules. It has 6,266 exact integer/rational assertions and five explicitly labeled floating formula records. It checks correlated-skew covariance on arbitrary tensors, finite reflection identities, spectral-grid probabilities integrated exactly over shifts, all-slot multiplicities, residual perturbation bounds, nested loss telescoping, the trace-contraction constant, strict-local-trap normalization/commutators/Hessian bounds, real X/Z family identities, and the exact binary-stage stopping calculation. Finite cases and float records are not universal proofs, orbit optimizations, novelty certificates, or independent analytic acceptance.

Ten fresh HTTP requests succeeded; five PDF extractions are replayed with their original stderr retained. Failed local relative reads, truncated broad displays, and the unavailable optional numpy import are recorded; diagnostics use no numpy. The earliest web discovery display was not separately archived; the later two batches and the actual primary response bodies are retained. No argument depends on an unarchived search snippet. The saved unchanged I69 replay passes; its 61,237 exact assertions and ten floats remain separate from the new counts.

The remaining route-A task is an actual way to exploit the large finite comparisons (2.4) at a **global** maximizer. Any entrance based only on its first/second derivatives, positive signs, and individual finite plane comparisons is now ruled out by (3.1), even in the exact-normalization class. The remaining route-B task is a linked selection and stopping argument that achieves both L_tot/m->0 and V/m->0 from R/m->0. Equations (5.1)–(5.9) already pay every compression, cap, residual, and terminal interface *if those quantities are reached*. Equations (5.5), (5.10), and the nonlinked obstruction (5.11) explain why the available one-step aggregate bound does not yet reach them. These unpaid estimates are not asserted as lemmas, and method failure is not target falsity.
