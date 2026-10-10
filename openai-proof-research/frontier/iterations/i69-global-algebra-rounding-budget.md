# I69 — global algebra rounding with a logarithmic error budget

**Disposition: no nomination. AR_K, including exact B=I, remains unproved and unrefuted.** The logarithmic construction target survives the linked tests below. This continuation pays the terminal/normalization part of any complete capped deflation, derives the exact change of the combined equation residual, proves a logarithmic greedy budget on arbitrary supplied multiscale simplicial direct sums, and tests a genuinely global basis construction. A Walsh-coordinate family shows that two-coordinate optimization and one bounded-block replacement cannot provide its entrance. A scalar unitalization calculation identifies exactly what that global correction removes and what remains. These are technical partials and method obstructions, not a ninth finding.

The author-level analytic conclusions below are separate from the offline evidence PASS and finite arithmetic checks. There is no fresh independent full-proof or significance acceptance. The parent retains review, count, commit, and publication authority. No shared/prior file was edited, no agent was spawned, and nothing was staged, committed, or published.

## 1. Contract and precise target

All statements **and proof operations** in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are true premises. Applicability and the new deductions, rather than upstream truth, are audited here. The complete tree has 13,223 entries, 749 manuscript roots, and 10,373 blobs. The fixed ignored corpus has 9,340 files; the other 1,033 tree blobs remain separately inventoried. Discovery searches and replay use the exact fixed domain and line **multisets**. Neither a catalogue nor those searches certify literature completeness.

The full current assignment, including all unchanged I65/I61/I59/I53 assignments and objections, is frozen verbatim in `../sources/i69_global_algebra_rounding_budget/brief.txt`, with its task JSON. The full I65, I61, I59, I53, I55, I56, I63, I64 reports and R014 acceptance are frozen inputs. The four front-page ledgers are the only mutable inputs. Old immutable evidence, including original failures, is hash-referenced without recursive copies or seal refreshes. Eight findings remain accepted; I67/I68 concern a different candidate.

For a fully symmetric real cubic T on R^m, let
\[
 (T_x)_{ij}=T(e_i,e_j,x),\quad B=\sum_rT_r^2,\quad
 E=\sum_{r,s}\|[T_r,T_s]\|_F^2,\quad
 \beta=\|B-I\|_F^2,\quad R=E+\beta.
\]
The symbol R here is a **squared** residual, not I56's residual norm. All pairs and tensor indices are ordered, and Frobenius norms are unnormalized. Set
\[
 d(T)^2=\inf_{U\text{ ONB}}\|T-D_U\|_F^2,
 \qquad D_U=\sum_i u_i^{\otimes3}.
\]
Signs are absorbed in U. AR_K asks for one modulus rho_K, independent of m, tending to zero at zero, with
\[
 B\preceq KI\ \Longrightarrow\ d(T)^2/m\le\rho_K(R/m).
\]
For exact B=I the proposed budget is
\[
 \Phi_m(E)=E\log(e+m/E),\qquad \Phi_m(0)=0.                 \tag{1.1}
\]
It is a **target**, not a premise. A bound C Phi_m(E) would normalize to C epsilon log(e+1/epsilon), with no surviving log m at fixed epsilon. General-cap rounding still needs its own proof; exact B=I is not restored after restriction.

## 2. Independent audit of inherited deductions actually used

These verdicts concern the written original deductions. Numerical replay is not their analytic premise.

**I65 linkage, signs, and test family: PASS ORIGINAL as used.** Write Delta x=T_x on all m by m matrices. Full symmetry gives Delta*Delta=B. Index contraction gives
\[
 \|P_T\|_{\rm HS}^2=\|\Phi_T\|_{\rm HS}^2=\operatorname{tr}B^2,
 \quad P_T=\Delta\Delta^*,\quad \Phi_T(X)=\sum_rT_rXT_r,
 \quad\|\Phi_T-P_T\|_{\rm HS}^2=E.                       \tag{2.1}
\]
Indeed the cross inner product is sum tr(T_r T_s T_r T_s), and an ordered commutator square contributes twice the difference from tr(T_r^2 T_s^2). At B=I this makes P_T a rank-m projection; it does not make its range an algebra.

For the old simplicial algebra on 1-perp in R^(m+1), put Q=I-11^t/(m+1), s=sqrt((m+1)/(m-1)), and T(x,y,z)=s sum x_a y_a z_a. Expanding Q between diagonal multiplications gives
\[
 \operatorname{tr}(T_xT_y)=\langle x,y\rangle,\quad
 \operatorname{tr}T_x=0,\quad
 [T_x,T_y]=-(xy^t-yx^t)/(m-1).                           \tag{2.2}
\]
Thus B=I and E=2m/(m-1), with the negative sign in (2.2). The Lagrange equations for the cubic maximum have two coordinate values; their objective is (n-2k)/sqrt(nk(n-k)). The positive maximum occurs at a vertex and equals sqrt((m-1)/m). Its complement deletes that ambient coordinate and imposes zero sum on the rest. Consequently the entire unrenormalized greedy chain is
\[
 t_j^2=\frac{m+1}{m-1}\frac{j-1}{j+1},\quad
 c_j^2=t_j^2(j-1)/j,\quad H_j=-t_j I/\sqrt{j(j-1)}.      \tag{2.3}
\]
In particular B'=t_j^2 I-2H_j^2; the final one-dimensional tensor is zero. The factor three in removed mixed mass and all ordered-pair multiplicities are retained below. No repair to these I65 statements is needed.

For completeness, the same compressed four-index contraction gives Phi_T-P_T=(tr(X)I-X)/(m-1). Partial transpose instead has entries P_{il,kj} and equals Phi_T composed with matrix transpose. On skew matrices this changes the sign. The negative eigenspace is the symmetric trace-free complement, dimension (m-2)(m+1)/2, with eigenvalue -1/(m-1). The resulting normalized negative-part trace tends to 1/2. These facts obstruct the particular operator/cb and post-partial-transpose trace entrances, **not** pre-transpose trace distance or Hilbert–Schmidt repair. No such entrance is used here.

**I65 arbitrary-normalization rounding: PASS ORIGINAL.** In any fixed basis let a=sum_{i not=j,r}T_{ijr}^2 and let M be all non-pure-diagonal tensor mass. Then M<=3a/2, with two of the three repeated-index placements counted in a. Directly b=||P_T-D_U||_HS^2=beta+2a. For z,h>=0,
\[
 (z-1)^2\le(z^2+h-1)^2+2h,                              \tag{2.4}
\]
because the difference at h=0 is z(z+2)(z-1)^2 and its h derivative is 2(z^2+h). Apply this with z=|T_iii|, h=B_ii-z^2, whose sum is M. Sign rounding costs at most beta+3M<=9b/4. The reverse estimate follows from AA*-CC*=(A-C)A*+C(A-C)* and ||Delta_T||op<=sqrt K. No inverse B or one-slot normalization is inserted.

**I65 supplied-dilation bound: PASS ORIGINAL, including singular selected frames.** For H subset R^(m+k), select m projected coordinate columns A. They have singular values in [0,1], and m-||A||_F^2 equals the sum of the k discarded column energies, at most k. A full SVD gives an orthogonal polar completion with ||A-U||_F^2<=k even if A is singular. Each of the three tensor telescoping terms is bounded by ||A-U||_F, because its paired-column map is (A tensor A)J, (U tensor A)J, or (U tensor U)J, of operator norm at most one. The discarded coordinate cubic has projected norm at most sqrt k. Hence
\[
 \|Q_H^{\otimes3}D_{m+k}-D_U\|^2\le16k,
 \quad\|sQ_H^{\otimes3}D_{m+k}-D_U\|^2\le32s^2k+2m(s-1)^2. \tag{2.5}
\]
This is used only with an **explicit supplied** dilation. Its existence for general T is still a gap, not an original false statement or a repaired theorem.

R014/CE61, its cap repair, and the smooth-source entropy reduction retain their accepted I63/I64 scopes. They are not reopened. I56's nearest-orbit estimate has a total-distance entrance, not a growing-dimensional normalized one. Nothing below treats parent reproduction as an additional analytic axiom.

## 3. Route A: a complete normalization account for deflation

At a global positive maximizer v in a current space W, stationarity and the spherical Hessian give
\[
 T_v=\begin{pmatrix}c&0\\0&H\end{pmatrix},\quad H\preceq cI/2.
\]
The other slices have blocks [[0,h_a^t],[h_a,S_a]], h_a=He_a. Let S be the full restriction to v-perp. The exact identities, without B=I, are
\[
 B_{00}=c^2+q,\quad B_{0a}=\operatorname{tr}(HS_a),\quad
 B|_{v^\perp}=B_S+2H^2,\qquad q=\|H\|_F^2.             \tag{3.1}
\]
Thus B<=I implies B_S<=I at every step. If the current tensor vanishes, choose any direction with c=H=0 and continue. This convention pays every terminal zero dimension.

### 3.1 Terminal diagonal and small-c costs

Run a complete such chain and call the selected diagonal coefficients c_i and the total discarded mixed mass
\[
 M=3\sum_i q_i.
\]
Classification by the earliest removed index makes all discarded components orthogonal. Therefore
\[
 \|T\|^2=\sum_i c_i^2+M,\qquad
 \|T-D_U\|^2=M+\sum_i(1-c_i)^2.                         \tag{3.2}
\]
Under initial B<=I, 0<=c_i<=1. It follows that
\[
 \boxed{\ \|T-D_U\|^2\le\operatorname{tr}(I-B)+2M.\ }   \tag{3.3}
\]
For exact B=I this is **cost at most 2M**, with diagonal cost at most M. It includes the last zero direction of the simplicial chain. More explicitly, for N=I-B and nu=N_00,
\[
 N'=N|_{v^\perp}+2H^2,\qquad
 \operatorname{tr}N'=\operatorname{tr}N-\nu+2q.           \tag{3.4}
\]
Telescoping gives sum nu_i=tr N_initial+2 sum q_i, rather than resetting N to zero.

For 0<=tau<1 the number of selected directions with c_i<tau satisfies
\[
 (1-\tau^2)\#\{i:c_i<\tau\}\le\operatorname{tr}(I-B)+M. \tag{3.5}
\]
This handles their **payment once M is bounded**; it does not yet construct that bound. Stopping at a d-dimensional tail costs at most another 2d under cap one, and d is not known to be small merely from the initial residual. For arbitrary B the scalar argument (2.4) gives the alternative complete-chain estimate cost<=beta+3M, with no cap assumption. All these are Pythagorean/elementary reductions, not AR.

### 3.2 The exact combined-residual change

A concrete attempted potential was R=E+beta, or its logarithmic transform Phi_d(R). Its exact change is informative. Put
\[
 w_a=\operatorname{tr}(HS_a),\quad
 L=\sum_a\|[H,S_a]\|^2,\quad \nu=1-c^2-q.
\]
Then for every fully symmetric stationary split (maximality is unnecessary for this identity),
\[
 \boxed{R(T)-R(S)=\nu^2-4\nu q-2q^2-8c\operatorname{tr}H^3
       +6\operatorname{tr}H^4+6L+6\|w\|^2.}              \tag{3.6}
\]
Here is a derivation including the cancellation that prevents a naive positive charge. Set C_ab=[S_a,S_b] and W_ab=h_a h_b^t-h_b h_a^t. The 0a commutators contribute 4||H^2-cH||^2+2L. The off-diagonal vector blocks of the ab commutators contribute another 2L, by full symmetry. Hence
\[
 E(T)-E(S)=4\|H^2-cH\|^2+4L+2\langle C,W\rangle+\|W\|^2. \tag{3.7}
\]
In an eigenbasis of H with eigenvalues lambda_a,
\[
 \|W\|^2=2(q^2-\operatorname{tr}H^4),\quad
 \langle C,W\rangle=2\left(\|w\|^2-\sum_{a,b,k}\lambda_a\lambda_b S_{abk}^2\right),
\]
\[
 L=2\operatorname{tr}(H^2B_S)-2\sum_{a,b,k}\lambda_a\lambda_bS_{abk}^2.
\]
Also (3.1) gives
\[
 \beta(T)-\beta(S)=\nu^2+2\|w\|^2-4q
           +4\operatorname{tr}(H^2B_S)+4\operatorname{tr}H^4.
\]
Expansion of ||H^2-cH||^2 and c^2=1-nu-q now proves (3.6). Orthogonal invariance removes the temporary eigenbasis choice. In particular, throwing away the cross term in (3.7) would be invalid.

**A valid-maximizer counterexample to monotonicity.** On R^2 take
\[
 p(x,y)=(2x^3+3xy^2)/\sqrt5.
\]
On the unit circle p=x(3-x^2)/sqrt5, increasing on [-1,1], so v=e_1 is a global positive maximizer. Here
\[
 c=2/\sqrt5,\ H=1/\sqrt5,\ B=\operatorname{diag}(1,2/5),
 \ E=4/25,\ \beta=9/25,\ R=13/25.
\]
The remaining one-dimensional tensor is zero and has R'=1. Thus R increases despite B>=2I/5, B<=I and c>=sqrt(4/5). Even Phi_2(13/25)<Phi_1(1). An analytic comparison is Phi_2(13/25)<(13/25)log7<26/25, since e<3 and e^2>7; whereas log(e+1)>26/25 follows from exp(1/25)<=25/24 and e<24. The numerical values in the diagnostics merely illustrate this strict inequality.

This tensor is an actual linked cubic. It is **not** an exact-B=I counterexample to (1.1), nor does it show this state is reached from an exact-B=I input. It refutes a proposed monotone potential on the natural intermediate class. Appending scalar odeco blocks makes its normalized residual small but leaves only bounded defective mass, so that dilution does not refute AR. A successful potential may need more state information than d and R, or explicit block resets with paid loss.

## 4. A rigorous logarithmic budget on supplied multiscale blocks

This section tests rather than assumes the proposed scale. Let
\[
 T=\bigoplus_b t_b T_{d_b}\ \oplus\bigoplus_j a_j e_j^{\otimes3},
 \quad d_b\ge2,\quad 0\le t_b,a_j\le1,                 \tag{4.1}
\]
with arbitrary numbers and dimensions of blocks. The decomposition is **supplied**. Signs of scalar amplitudes can be absorbed. Face restrictions of simplicial blocks are included: restricting a zero-sum coordinate subspace leaves exactly a scaled smaller simplicial tensor, with the one-dimensional zero case included as a scalar block. Arbitrary compressed subspaces are not all asserted to have form (4.1).

**Proposition 4.1.** Every global-positive-maximizer greedy chain on (4.1) satisfies
\[
 \operatorname{cost}_{\rm greedy}\le256R\log(e+m/R),     \tag{4.2}
\]
with the zero limit at R=0. There is also an explicit global orientation with cost<=402R. In particular exact-normalization direct sums satisfy the proposed E log(e+m/E) budget, uniformly over arbitrarily multiscale mixtures.

**Proof.** A cubic direct sum has maximum max_b c_b: writing x in blocks,
p(x)<=sum c_b||x_b||^3<=max c_b. When the maximum is positive, equality requires a single nonzero block, because sum r_b^3<1 if at least two r_b are positive and sum r_b^2=1. Thus every maximizing choice respects a block until only zero blocks remain. The final zero space can be treated arbitrarily, at its dimension cost.

For one normalized d-block, (2.3) gives
\[
 M_d=3\frac{d+1}{d-1}\sum_{j=2}^d\frac{j-1}{j(j+1)}
 \le9\log(ed),\quad g_d\le2M_d\le18\log(ed).            \tag{4.3}
\]
The scalar inequality sum_{j=2}^d 1/j<=log d suffices for the deliberately loose bound. For tT_d, put
\[
 r_d=d(1-t^2)^2+\frac{2dt^4}{d-1}.                     \tag{4.4}
\]
This is its exact beta+E, not a restored normalization. The same greedy basis has cost at most 2t^2g_d+2d(1-t)^2<=36log(ed)+2r_d. If t^2<1/2, the simpler cap estimate cost<=d(1+t^2)<=2d<=8r_d applies. If t^2>=1/2, then r_d>=1/2. The function x log(e+d/x) increases in x, so
\[
 r_d\log(e+d/r_d)\ge\tfrac12\log(e+2d)\ge\tfrac14\log(ed).
\]
The latter follows from (e+2d)^2>=ed. Since log(e+d/r_d)>=1, the preceding cost is at most 146 r_d log(e+d/r_d), hence at most the stated 256 multiple. A scalar block costs (1-a)^2<=(1-a^2)^2, and is covered too.

Finally f(x)=x log(e+1/x), f(0)=0, is concave: f''(x)=-1/[x(ex+1)^2]. Jensen with weights d_b/m, also including scalar dimensions, gives
\[
 \sum_b r_b\log(e+d_b/r_b)\le R\log(e+m/R).             \tag{4.5}
\]
This pays arbitrary block counts and multiscale tails; it is not a bound involving log m at fixed R/m.

For the global orientation, use the supplied codimension-one dilation for each T_d and (2.5). Since s^2=(d+1)/(d-1)<=3 and s-1<=1/(d-1), its cost is at most 96+4=100. For t^2>=1/2, scaling gives cost<=200+2r_d<=402r_d. For t^2<1/2, use any orientation with nonnegative diagonal values, costing at most 2d<=8r_d. Concatenate these bases and round the scalar signs. Additivity proves the global claim. ∎

This is a technical supplied-block result. Its complete reduction uses the independently audited I65 chain/dilation and Jensen; there is no discovery of the blocks for a general tensor. In particular it is not being classified as technical merely because a search found no new theorem.

### 4.1 Tensor products test large m at fixed normalized error

There is another actual linked family beyond direct sums. For normalized cubics A and C, their three-slot tensor product has B=I and
\[
 \varepsilon(A\otimes C)
 =2\{1-(1-\varepsilon(A)/2)(1-\varepsilon(C)/2)\}.       \tag{4.6}
\]
This follows by factoring both tr B^2 and the crossing contraction sum tr(T_rT_sT_rT_s) in (2.1). For products of simplicial blocks d_j>=3, put eta=sum_j 1/(d_j-1). Then
\[
 \varepsilon=2\left(1-\prod_j(1-1/(d_j-1))\right).
\]
For eta<=1/2, eta<=epsilon<=2eta: use product<=exp(-eta), 1-exp(-eta)>=eta/2, and the elementary union bound.

The product has an explicit coordinate dilation with m=product d_j, N=product(d_j+1), and s^2=product (d_j+1)/(d_j-1). Thus N/m<=exp(eta), s^2<=exp(2eta). Formula (2.5) gives
\[
 d(T)^2/m\le32e^{2\eta}(e^\eta-1)+2(e^\eta-1)^2
 \le160\eta\le160\varepsilon\quad(\eta\le1/2).          \tag{4.7}
\]
For the middle bound use e^eta-1<=e^(1/2)eta and 2eta<=1. The dimension can be enormous while eta stays fixed, for instance with many blocks whose dimensions grow with their number. Therefore this global construction has the required uniform quantifiers on this test class. Tensor products of these classical algebras are already studied by Fox; the polar conclusion is the paid supplied-factor operation. No arbitrary-product greedy estimate is asserted.

## 5. Route B: genuinely global basis variation and algebra completion

### 5.1 Global basis objective, and a linked obstruction to local entrance

Consider the compact global optimization
\[
 F(U)=\sum_iT(u_i,u_i,u_i).
\]
For B=I, the exact orbit cost is 2m-2 max F. Existence of a maximizer is automatic; the bound max F>=m-o(m) is **not**. In coordinates of a global maximizer, sign changes give c_i=T_iii>=0. Rotating the (i,j) plane gives the necessary equations
\[
 T_{iij}=T_{ijj}=:a_{ij},\qquad
 12a_{ij}-3(c_i+c_j)\le0.                               \tag{5.1}
\]
For every real skew K the full second variation, which is stronger than separate plane tests, is
\[
 F''(0)=6\sum_iT(u_i,Ku_i,Ku_i)
       +3\sum_iT(u_i,u_i,K^2u_i)\le0.                  \tag{5.2}
\]
It follows by differentiating exp(tK)u_i twice. Thus a real global method is available as a variational problem, with explicit compatibility conditions. The following family prevents replacing it by pair-coordinate optimality or a small fixed block assumption.

Let G=(F_2)^k, m=2^k-1, k>=2, and index an ONB by the nonzero characters a. On this basis set
\[
 T_{abc}=\frac{\mathbf1_{a+b+c=0}}{\sqrt{m-1}}.          \tag{5.3}
\]
All three indices in a nonzero entry are distinct. This is **exactly the linked simplicial family**, not an arbitrary channel or a newly discovered algebra. Indeed the vectors u_a(g)=(-1)^(a dot g)/sqrt(m+1) form an ONB of the zero-mean subspace in R^(m+1). Their triple coordinate sum is 1/sqrt(m+1) when a+b+c=0 and zero otherwise. Multiplication by sqrt((m+1)/(m-1)) proves (5.3) and its linkage to (2.2). Alternatively its unscaled slices are the permutation x -> x+a with the zero coordinate removed; their commutator is exactly minus the elementary wedge, and each has m-1 entries. Hence B=I, E=2m/(m-1), epsilon->0.

Every pure diagonal coefficient is zero, so F(I)=0 and the normalized cost is 2. After **any single arbitrary two-coordinate orthogonal change**, every new vector is supported on two coordinates; its cubic is still zero. Therefore F remains exactly zero along each such coordinate move. A strict-improvement two-coordinate algorithm can stop here while its normalized error is 2 and epsilon tends to zero. This is not a statement about an algorithm allowed to take arbitrary flat moves and subsequently escape.

The failure persists for a single blockwise reconstruction. For every partition of these coordinates into blocks J with |J|<=b, and every ONB respecting that partition,
\[
 F(U)\le m\sqrt{\frac{b-1}{m-1}},\qquad
 \frac{\|T-D_U\|^2}{m}\ge2\left(1-\sqrt{\frac{b-1}{m-1}}\right). \tag{5.4}
\]
To prove it, a subset J of size q has at most q(q-1) ordered nonzero triples: each ordered distinct pair determines its third index uniquely. Thus ||T|_J||^2<=q(q-1)/(m-1). Cauchy–Schwarz against the q-dimensional coordinate cubic in **any** basis of J gives block contribution at most q sqrt((q-1)/(m-1)). Summing proves (5.4), uniformly over the partition as well as all block bases. In particular b=o(m) still leaves normalized error approaching 2. Repeated adaptive block operations can enlarge coordinate supports and are not ruled out.

Full second variation detects a way out. Choose a,b,c with a+b=c, set K_ab=K_ac=1, K_ba=K_ca=-1, and all other entries zero. Then (5.2), evaluated at the Walsh basis, equals 12/sqrt(m-1)>0. The basis is a saddle for the full objective, despite the flat individual plane curves. The missing global estimate is to use the **entire** condition (5.2), together with B and the associator, to control m-F. Neither (5.1) nor a proof restricted to a supplied small block decomposition supplies it. No global-maximizer theorem is inferred from this saddle computation.

There is no AR counterexample here. Returning by the explicitly known Walsh transform to the supplied coordinate dilation and applying (2.5) gives bounded total cost; I65's Householder basis gives cost 4+o(1). The lower bound (5.4) concerns a restricted set of orientations only.

### 5.2 Scalar unitalization: exact global correction and its remaining defect

A different global operation is to add one dimension. This is an explicit Euclidean normalization of Fox's metrized unitalization, not a new general factor-existence theorem. Let tau_r=tr T_r and, for alpha!=0, define a cubic on Re_0 plus V by
\[
 \widehat T=T+\alpha e_0^{\otimes3}
        +3\alpha\,\operatorname{Sym}(e_0\otimes I_V),    \tag{5.5}
\]
where Sym is the average of the three positions: equivalently the polynomial is p(x)+alpha z^3+3alpha z||x||^2. The slices are
\[
 \widehat T_0=\alpha I_{m+1},\quad
 \widehat T_x=\begin{pmatrix}0&\alpha x^t\\\alpha x&T_x\end{pmatrix}.
\]
Thus e_0/alpha is an **exact unit in the changed, enlarged multiplication**. This does not contradict I65's impossibility of unit recovery in the original multiplication. Direct block multiplication gives
\[
 B_{\widehat T}=\begin{pmatrix}(m+1)\alpha^2&\alpha\tau^t\\
                        \alpha\tau&B_T+2\alpha^2I\end{pmatrix},
\]
\[
 E(\widehat T)=E(T)+4\alpha^2(\|\tau\|^2-\operatorname{tr}B_T)
                         +2m(m-1)\alpha^4.             \tag{5.6}
\]
For (5.6), the 0x commutators vanish, and the xy commutator is [T_x,T_y]+alpha^2(xy^t-yx^t) in the lower block. The ordered cross contraction with wedges is 2(||tau||^2-tr B), fixing the sign and factor four.

In the trace-free exact-B=I case with m>1, take alpha^2=1/(m-1). Scaling all of (5.5) by (1+2alpha^2)^(-1/2) gives an exact-unit, exact-B=I tensor in dimension m+1 with
\[
 E_{\rm new}=\frac{E(T)-2m/(m-1)}{(1+2/(m-1))^2}.       \tag{5.7}
\]
The nonnegativity of the left side independently proves E(T)>=2m/(m-1) on this trace-free class. Equality gives an associative enlarged multiplication, hence an orthogonal decomposition by simultaneous diagonalization. This is precisely the classical projective-associativity/unitalization operation at its paid normalization. It explains why the simplicial block can be globally corrected at bounded cost.

For a general trace-free input, (5.7) removes only the scalar-curvature component: the remaining E can still be of order epsilon m. The new tensor is not trace-free, so the same reduction cannot simply be repeated. For nonzero tau, the off-diagonal normalization terms alpha tau must also be paid; pretending that the enlarged B is scalar would be false. No near-square associative completion for an arbitrary linked tensor has been constructed. This is a concrete limit of the global operation, rather than an appeal to an exact unital theorem as approximate stability.

## 6. Actual source and primary-operation comparison

The actual pinned sharp-entropy `rigidity.tex` supplies exact jets, common diagonalization, forward Frobenius functional calculus, and fixed-dimensional compactness. The retained `matrix.tex` operations supply the source slack and smooth-class cap consequences. They do not include an estimate for max F or for the mixed mass of a full greedy chain. General-Mahler `06-linear-equality.tex` turns a **zero** spectral moment into common diagonalization with a different deficit; it supplies no comparison to the residual budget here.

The pinned Kadison–Kastler `02-foundations.tex` uses cb/Haagerup closeness to a supplied associative product/representation; the near-inclusion `obstruction.tex` uses operator-norm clock/shift obstruction and a common corner inside supplied commuting algebras; the tracial `10_unital_averaging.tex` supplies nuclear/order-zero replacement, projections, averaging and fourth-moment clipping. Their lower proof operations were read, not replaced by title analogies. None constructs the missing linked basis or completion from normalized Hilbert–Schmidt cubic error.

Fresh primary response bodies, headers, retrieval times, served versions, PDF text and extraction warnings are retained in `primary/manifest.json`. These are capture-time versions, not a promise that endpoints will never change. The applicable comparisons are:

* [Fox 2004.12343v2](https://arxiv.org/abs/2004.12343v2), simplicial algebra definitions/associator and Griess–Harada attribution, tensor-product section, and §§5–6, especially the actual c-unitalization formula, associator cancellation, and exact split-algebra characterization. Formula (5.5) uses its metric scaling, not the algebraic unit adjunction with zero cross metric. [Sectional nonassociativity 2211.01073v3](https://arxiv.org/abs/2211.01073v3), §4 and Example 5.5, keeps the curvature conventions distinct. The Steiner companion was refreshed for discovery; no theorem from it is invoked.
* [BDHR 1512.08031v1](https://arxiv.org/abs/1512.08031v1), Lemmas 10–11/Proposition 12, decomposes exact associative Euclidean multiplication into orthogonal simple ideals. The kernel-ideal argument uses exact associativity; small normalized residual does not produce such ideals. [BDS published Proposition 4.1](https://rendiconti.dmi.units.it/volumi/54/017.pdf), with Robeva attribution, supplies the old tangent equations. Its local operation does not supply a normalized global entrance.
* [Auddy–Yuan 2007.09024v2](https://arxiv.org/abs/2007.09024v2), Theorem 3.1 and the actual polar/tensor telescoping proof, starts from supplied factors and singular-value bounds. This pays for the type of construction in (2.5), not for finding its factors. It is a concrete technical antecedent to the positive restricted results here.
* [Bansil–Kachkovskiy 2608.31000v1](https://arxiv.org/abs/2608.31000v1), Theorem 1.3 and Remark 4.1, sums the spectral cut costs across the matrix family and uses its total normalized energy, bounded there by N, producing sqrt N. Corollary 1.4 iterates with count-dependent exponent. A single application to a capped slice family can improve that energy estimate, but the subsequent common-block iterations and preservation of all three tensor slots still require proof. Neither a slogan about matrix-size independence nor improved one-step constants supplies the present growing-family entrance.
* [Kitaev 2405.02434v2](https://arxiv.org/abs/2405.02434v2), §1.2/Definition 2.1/Theorem 2.3, assumes small cb idempotence or uniform Banach/C*-norm axioms, including a unit. Its spectral projection can fail complete positivity. These hypotheses are not consequences of (2.1). [CPV 0810.0812v1](https://arxiv.org/abs/0810.0812v1), Theorem 5.1/§6, classifies exact commutative dagger-Frobenius monoids, with specialness giving normalization. [Poinsot §3.4](https://lipn.fr/~poinsot/Articles/Hilbertian_Frobenius_algebras_rev.pdf) concerns approximate units inside exact Hilbertian algebras.
* [Horodecki–Lewenstein–Vidal–Cirac quant-ph/0002089v1](https://arxiv.org/abs/quant-ph/0002089v1) assumes exact PPT in its low-rank theorem. Its local filtering and null-vector steps force exact commutation from positivity. They do not give a normalized-HS repair; I65's partial-transpose indexing and scope caveat remain essential.

No external theorem is promoted to a stipulated premise. The new elementary derivations do not require certifying the full external proofs. Bounded discovery searches establish neither priority nor absence of a technical reduction. No MathDB score is invented. The positive results in §§3–4 reduce explicitly to block multiplication, Pythagorean identities, the already-paid supplied-factor construction and Jensen. The Walsh test is ordinary character orthogonality applied to the same old algebra; unitalization is credited to Fox. Thus none is nominated as a substantial newly upstream-enabled rounding bridge.

## 7. Entropy scope and preserved objections

There is no new entropy law because neither AR_K nor its needed general-cap entrance is proved. The conditional rate, if the logarithmic budget were eventually established at every fixed cap, is explicit. For an actual centered isotropic smooth source density e^(-V), with V smooth and 0<c_-I<=D^2V<=c_+I, retain the **original** coefficient cap B_X<=KI and put u=delta/m. R014 supplies
\[
 \eta\le\chi_K(A_Ku),\quad \beta_X/m\le2000u/c_K,
\]
and a symmetric Z of cap 4K with normalized repair cost <=26eta and normalized residual
\[
 e_Z\le4000u/c_K+(2+2340K)\eta.
\]
If AR_(4K) supplied rho_(4K), triangle-square gives coefficient-to-odeco error <=52eta+2rho_(4K)(e_Z). Forward q-Lipschitzness and Gaussian Poincare then give map error <=2000u+104eta+4rho_(4K)(e_Z). The original P>=q(0)I and isotropic covariance comparison pay de-normalization, giving
\[
 d_m(f)^2/m\le\frac4{q(0)^2}
       [2000u+104\eta+4\rho_{4K}(e_Z)].                \tag{7.1}
\]
This uses one global U. If, additionally and still conjecturally, rho_(4K)(z)<=C_K z log(e+1/z), CE's eta=O_K(1/log(e/u)) would yield
\[
 d_m(f)^2/m=O_K\left(\frac{\log\log(e^e/u)}{\log(e/u)}\right).
\]
The substitution follows by monotonicity of z log(e+1/z), and by e_Z=O_K(1/log(e/u)); it is not a proved law, a square-root rate, or an unrestricted U claim. Exact-B=I rounding alone would not apply to this Z.

All inherited objections remain: the uncapped heavy star has expensive cross-slot deletion and is not a realized density counterexample; regularized Q is not q(S^(1/2)L); rank alone does not preserve compatibility; arbitrary flag deficits are canceled by negative log scales; missing dimensions cost 2k after a paid marginal coupling; generic channels and diluted harmonic blocks are not linked AR counterexamples; density approximation supplies no coefficient convergence or preserved original cap. I56's total-distance tube and supplied bounded block sizes do not close AR. Prior quadrature nonconvergence and the distinction between exact chosen-orientation bounds and uncertified numerical integration remain unchanged in the frozen originals.

## 8. Evidence, replay, and precise remaining work

Run from the repository root:

```bash
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i69_global_algebra_rounding_budget/verify.py
```

The verifier is offline and read-only. Its provenance scaffolding is transparently adapted from I65; the I69 finite mathematical checks are newly implemented without importing prior diagnostic code. It checks the exact full brief, 19 frozen inputs, the four-ledger allowlist, 790 prior file hashes, complete tree/corpus domain and Git blobs, 26 referenced pinned files, fixed-domain search line multisets, primary bodies and PDF extraction replay, frozen read passages, deterministic independent diagnostics, and the I69 seal. The unchanged I65 verifier was run separately; its saved PASS is provenance only, including its preserved original inventory failure and corrected explicit-domain replay. No prior seal was refreshed. Acquisition scripts are separate writers and are not run by the verifier.

Independent diagnostics use exact integers/fractions for general stationary block identities and the signed residual change, capped complete-chain accounting, scalar rounding, simplicial restrictions, arbitrary-cubic scalar unitalization, and dense Walsh linkage/commutators/character transformations. The full-Hessian and flat-pair computations are separately tested. Floating records evaluate direct-sum, multiscale, tensor-product and failed-potential formulas only; they are not interval certificates or orbit optimization. The independent run has 61,237 exact assertions and ten labeled floating records. There are 28 frozen source/primary passages, 20 successful fresh primary responses, and 11 PDF extraction replays. The BK font warning is preserved; no fresh HTTP request failed. The first displayed web-discovery batch was not separately archived, while the second was; no proof depends on that first batch. A mistaken local transport-file path and its corrected read are recorded in `local-read-failures.json`. Environment details are in the replay output. Finite assertions do not prove any universal theorem above.

The remaining route-A inequality is a bound for the **total newly created mixed mass**, compatible with the cross term in (3.7) and normalization evolution (3.4), or a paid adaptive block replacement that avoids it. Final diagonal normalization is no longer an additional unpaid step once such a mass bound exists. Small-c direction counts are charged by (3.5), but bounding that charge is still part of the unresolved construction.

The remaining route-B entrance is a quantitative global implication from linked associator error to a high value of F (using full simultaneous variations), or an actual near-square associative completion. Pair rotations and a one-shot sublinear coordinate-block partition cannot supply it by (5.3)–(5.4). Scalar unitalization removes only one specified curvature component and cannot be iterated for free. These are developed failed entrances with concrete calculations, not proofs of AR, counterexamples to AR, or additional accepted findings.
