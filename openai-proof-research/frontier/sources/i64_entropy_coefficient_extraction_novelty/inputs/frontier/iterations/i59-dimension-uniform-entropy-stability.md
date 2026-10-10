# I59: dimension-uniform sharp entropy stability — developed partial results and remaining interfaces

Date: 2026-10-09 (America/Los_Angeles; primary captures use UTC). **U remains unproved and unrefuted. No substantial finding is nominated.** All pinned OpenAI statements **and proof operations** at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated premises. This report does not audit their truth, change the acceptance count, or replace the original I53/I55/I56 records.

There is useful progress beyond repeating the fixed-dimensional proof: a simultaneous covariance/Sobolev remainder, a normalization costing only the averaged deficit, a dimension-free Gaussian curl identity, a dimension-free classical-curl bound under a bounded coefficient-energy hypothesis, and an exact channel representation of symmetric-tensor commutator error. An independent probabilistic construction proves that an entire dependent class of orthant-radial log-concave laws has whitened squared W2 distance at most (4m/(m+1)) from an exponential product and entropy gap at most 1. These are proved partial results, not a deficit modulus for all densities. A symmetric-tensor example obstructs naive deletion of heavy directions. An actual rotated exponential equality law obstructs additive conditional-deficit accounting.

## 1. Scope, prior disposition, and screens

Put (Z_m=(E_1-1,\ldots,E_m-1)), with iid mean-one exponentials, and
\[
 \delta(f)=h(f)-m-\tfrac12\log\det\operatorname{Cov}(f),\qquad
 d_m(f)=\inf_{O\in O(m)}W_2(f,OZ_m)
\]
when (f) is centered isotropic. The target is
\[
 d_m(f)^2/m\le C\sqrt{\delta(f)/m}                     \tag{U}
\]
with numerical (C), all dimensions, and every log-concave density. Independent coupling gives (d_m^2\le2m), so the question is small **normalized**, not small total, deficit.

The exact assignment, including the full original I53 assignment, is frozen in [brief.txt](../sources/i59_dimension_uniform_entropy_stability/brief.txt). The full original reports were read. I55 passes H53, Lemma A, B53, the scalar exponent and KL obstruction without repairs. I56 classifies the **full H53** as technical: the normalized odeco derivative has precisely the orbit tangent kernel, normal singular value 2, and a nearest-orbit Taylor estimate; fixed-dimensional compactness supplies entrance. That argument pays the same scope and exponent without cubic deflation. We do not renominate it. Its small-total-distance neighborhood is not a dimension-uniform normalized neighborhood. Uncertified quadrature remains only an approximation to a fixed-orientation upper bound.

Three precise mechanisms were screened before choosing the extended analytical/probabilistic investigation:

1. **Averaged compatibility U.** Extract a normalized approximate symmetric associative algebra from Gaussian curl of (q(L)), then round it to one global orthogonal decomposition. Sections 2–5 pay normalization, higher-chaos Sobolev control and an averaged differential estimate. Normalized coefficient extraction and global algebra rounding remain unpaid.
2. **Probabilistic decomposition U.** Discard a small-dimensional subspace at a paid coupling cost, or choose a flag and use conditional scalar stability. Section 6 proves the deletion cost, writes the exact entropy/covariance correction, and exhibits cancellation on an actual equality law. A suitable large good subspace or globally aligned flag is not constructed.
3. **Orthant-radial test-class theorem.** For (f(x)=c g(\sum x_i)\mathbf1_{x_i\ge0}), (g) log-concave, prove a bound independent of dimension, including nonsmooth and nonproduct cases. Section 7 closes (d_m^2\le4m/(m+1)), (0\le\delta\le1), after whitening, and all invertible affine images. This is a genuine growing-dimensional test-class result, but it neither vanishes with the deficit nor meets the substantiality standard by itself.

The primary audit includes the full sharp entropy scalar/matrix/transport/certificate/approximation/rigidity/geometry arguments, and the actual general-Mahler projection, normalization, spectral-identity and equality passages. Mahler's layer and volume-product deficits are different quantities; no comparison to this entropy deficit is supplied. The complete tree has 13,223 entries and 749 manuscripts; an independent `rg --files --no-ignore` inventory contains 9,340 corpus files. Searches are stored and verified as line **multisets**, not raw output order. Coverage does not mean every manuscript was read. See §9 for primary-literature details, including a relevant August 2026 matrix result absent from the old comparison.

## 2. A simultaneous covariance and Sobolev remainder

Initially let (f) be centered isotropic with the source's smooth positive upper/lower potential-Hessian bounds. Let (F_\#\gamma_m=P_\# f), (P>0) symmetric, (EF=0), and
\[
 DF=q(A),\quad EA=0,\quad A=L+Y,\quad L(x)=\sum_r x_rX_r,
 \quad B=\sum_rX_r^2,\quad C=\operatorname{Cov}F=P^2.
\]
Here (q(a)=\varphi(a)/\Phi(-a)). All norms below are unnormalized unless divided by (m). Set
\[
 \alpha=3/40,\quad a_0=37/40,\quad S=(a_0I+\alpha B)^{-1},\quad
 K=S^{1/2}CS^{1/2},\quad
 D_S(C)=\operatorname{tr}K-\log\det K-m.
\]
Write (Y_d) for Gaussian chaos degree (d\ge2), and (\Omega(B)=\sum_i\omega(\lambda_i(B))), with the **original** source weight.

**Proposition 2.1 (retaining two previously discarded nonnegative terms).**
\[
 2\delta\ \ge D_S(C)+\frac{\Omega(B)}{1000}
  +\sum_{d\ge2}\left\{\frac1{500}
              +\frac{(d-2)(d+68)}{50d}\right\}\|Y_d\|_2^2.       \tag{2.1}
\]
In particular, simultaneously,
\[
 D_S(C)\le2\delta,\quad \|Y\|_2^2\le1000\delta,\quad
 \|\partial Y\|_2^2\le2000\delta,\quad \Omega(B)\le2000\delta.  \tag{2.2}
\]

**Proof.** In `matrix.tex`, immediately before `mat:deficit-reduction`, the supporting-plane replacement has the exact form
\[
 \log\det C+m=\operatorname{tr}(SC)-\log\det S-D_S(C).
\]
The source's subsequent right-hand estimates do not use this discarded term. Carry it with its minus sign through the proof. Likewise the final chaos calculation need not discard the displayed factor
\[
 (1-u)-Q(1,u-1/2)-\frac7{50}u
       =\frac1{50}(1-2u)(1+68u).
\]
Multiplying by (\|G_d\|^2=d\|Y_d\|^2), (u=1/d), retains exactly ((d-2)(d+68)/(50d)). The existing difference (7/50-69/500=1/500) stays unchanged. Thus all terms in (2.1) coexist. For (d\ge3), ((d-2)(d+68)\ge d^2); at (d=2) the remaining coefficient is (1/500=d/1000). Consequently the chaos sum dominates (\|\partial Y\|^2/1000). This proves (2.2). ∎

These are technical extractions of accepted source operations, not new substantial theorems. In particular we have **not** retained the separation surplus (\mathcal C): it is consumed by the two-eigenvalue estimate. The source's rational scalar certificates and tail estimates are used as given, not replaced by sampling.

**Proposition 2.2 (averaged-scale removal of the affine normalizer).** With (G=S^{1/2}F), there is an orthogonal (O) and a coupling such that
\[
 W_2(G_\#\gamma_m,O_\# f)^2\le2\delta.                       \tag{2.3}
\]
Furthermore, for (Q(x)=S^{1/2}q(L(x))),
\[
 \|DG-Q\|_2^2\le\frac{40000}{37}\delta,\qquad
 \|S^{1/2}L\|_2^2=\operatorname{tr}(SB)\le\frac{40}3m,       \tag{2.4}
\]
and
\[
 \|Q\|_2^2\le (2q(0)^2\,40/37+80/3)m.                     \tag{2.5}
\]

**Proof.** The polar decomposition (S^{1/2}P=K^{1/2}O) is valid without commutation. If (V=P^{-1}F\sim f), coupling (G=K^{1/2}OV) to (OV) costs (\|K^{1/2}-I\|_F^2). For each eigenvalue (u>0),
\[
 (\sqrt u-1)^2\le u-1-\log u,
\]
because their difference is (2(\sqrt u-1-\log\sqrt u)\ge0). Equation (2.1) proves (2.3). The source's forward Frobenius Lipschitz bound and (S\preceq40I/37) prove the first part of (2.4). The second is the scalar inequality (\lambda/(a_0+\alpha\lambda)\le1/\alpha). Finally (q(t)\le q(0)+|t|), so spectral calculus gives (q(L)^2\preceq2q(0)^2I+2L^2); trace against (S), average, and use (EL^2=B). ∎

This closes an actual average-scale normalization cost **before** an orientation has been recovered. It neither assumes (P\) near (I) nor uses a uniform inverse of (q). The inherited Jensen/first-chaos estimate (P\succeq q(0)I) also remains available. Estimates involving (P,A) here are stated for the source smooth class. A final density-level estimate could pass to arbitrary log-concave densities using the source's weighted approximation; no convergence of the newly defined coefficients in growing dimension is claimed.

## 3. Route A: averaged Gaussian compatibility

For a matrix field (V), let 
\[
 (\operatorname{curl}V)_{irs}=\partial_rV_{is}-\partial_sV_{ir},\qquad r<s.
\]
Let (\mathcal P) be the orthogonal projection in Gaussian (L^2) onto the closure of row-gradient fields, independently for each row. Put (N=-\Delta+x\cdot\nabla).

**Proposition 3.1 (exact Gaussian compatibility energy).**
\[
 \|(I-\mathcal P)V\|_2^2
  =\sum_{i,r<s}\langle(\operatorname{curl}V)_{irs},
          (N+2)^{-1}(\operatorname{curl}V)_{irs}\rangle.        \tag{3.1}
\]
The right side is understood by chaos expansion for distributional curls. Consequently
\[
 \|(I-\mathcal P)q(L)\|_2^2\le1000\delta,
 \qquad \|(I-\mathcal P)Q\|_2^2\le\frac{40000}{37}\delta.      \tag{3.2}
\]

**Proof.** For one row (v) of pure degree (k), set
(u=(k+1)^{-1}\sum_j\partial_j^*v_j), with (\partial_j^*=x_j-\partial_j). The projection is (\nabla u), since (N u=\partial^*v), and ((k+1)u=\partial^*v). The Gaussian creation/annihilation commutator, or expansion in the product Hermite basis, gives
\[
 \sum_{r<s}\|\partial_rv_s-\partial_sv_r\|_2^2
       =(k+1)\|v\|_2^2-\|\partial^*v\|_2^2
       =(k+1)\|v-\nabla u\|_2^2.
\]
The curl has degree (k-1), so (N+2) acts there by (k+1). Constants have zero residual and zero curl. Sum over orthogonal degrees and rows, then pass by (L^2) completion. Apply the resulting projection contraction to (q(L)-DF) and (Q-DG). ∎

Thus there is a genuine dimension-free averaged compatibility input, with no Gaussian small-ball factor. It is a distance to **row gradients**, not already a small polynomial associativity residual. Symmetry of (q(L)) would identify an exact compatible field as a Hessian locally, but approximate projection does not by itself extract its coefficients. In particular, 
\[
 P_tq(L)(x)=E\,q(e^{-t}L(x)+\sqrt{1-e^{-2t}}L(H))
\]
for (H\sim\gamma_m); it is not (q(e^{-t}L(x))). Replacing one by the other would incorrectly turn averaged compatibility into the source's jets at zero.

There is also a stronger differential conclusion on the bounded-energy part of the problem.

**Proposition 3.2 (classical averaged curl when (B\preceq KI)).** There is a numerical finite (c_q), depending only on the displayed scalar Mills function, for which
\[
 \|\operatorname{curl}q(L)\|_2
 \le\sqrt2\bigl(\sqrt{2000}+c_q\sqrt{1000K}\bigr)\sqrt\delta. \tag{3.3}
\]
The norm uses (r<s), all rows and all Gaussian inputs. There is no dependence on the number of matrices other than the explicit assumption (B\preceq KI).

**Proof of the needed functional-calculus bound.** Use Fourier convention
(\widehat h(\xi)=\int e^{-i\xi t}h(t)\,dt), and set
(c_q=(2\pi)^{-1}\int|\widehat{q''}(\xi)|\,d\xi<\infty).
Here (q'',q'''\in L^2(\mathbb R)): on the negative tail (q) and its derivatives have Gaussian decay times polynomials. On the positive tail write
\[
 q(r)=r/F(r^{-2}),\qquad F(u)=\int_0^\infty e^{-v-uv^2/2}\,dv.
\]
Differentiation under this integral at (u\ge0) gives bounded derivatives of every fixed order near zero, (F(0)=1); Taylor's formula gives (q''(r)=O(r^{-3})), (q'''(r)=O(r^{-4})). On compact intervals the function is smooth. Cauchy–Schwarz with weight (1+\xi^2) and Plancherel now gives the asserted Fourier integrability.

Integrate the Fourier inversion of (q'') twice, using ((e^{i\xi t}-1-i\xi t)/(i\xi)^2). The apparent singularity at zero is removable. For self-adjoint (M), the second Fréchet derivative of this expression is the sum of the two ordered Duhamel integrals over the two-simplex. Its total integration volume is one. Every integrand has one of the forms (U_0 H U_1 X_rU_2) or (U_0X_rU_1HU_2), with unitary (U_j) independent of (r). Since (\sum X_r^2\preceq KI), summing its squared Hilbert–Schmidt norm over (r) gives at most (K\|H\|_F^2) in either case. Minkowski therefore proves
\[
 \Big(\sum_r\|Dq(M+H)[X_r]-Dq(M)[X_r]\|_F^2\Big)^{1/2}
                  \le c_q\sqrt K\|H\|_F.                    \tag{3.4}
\]
This is a family bound, not (m) separate estimates with a suppressed aggregation cost.

Now (\partial_rA=X_r+\partial_rY), and the derivative (Dq(A)) is a contraction on Frobenius matrices by the source divided-difference formula. Hence
\[
 \|\partial q(A)-\partial q(L)\|_2
       \le\|\partial Y\|_2+c_q\sqrt K\|Y\|_2.
\]
The curl of (q(A)=DF) is zero, and antisymmetrization has norm at most (\sqrt2) in the chosen (r<s) convention. Equations (2.2) prove (3.3). ∎

This is stronger than the old negative-Sobolev-to-origin estimate on its stated bounded-(B) class. It still does not prove that a small integrated curl gives small **coefficient** symmetry/associativity error uniformly in (m).

## 4. Heavy coefficients: what is paid and an explicit obstruction

For (0<t\le1/2), the original weight admits the elementary global bound
\[
 \inf_{|\lambda-1|\ge t}\omega(\lambda)\ge10^{-4}t^2.
\]
Use the I53 bounds (\omega\ge10^{-4}) off ([1/2,2]) and (\omega\ge10^{-3}(\lambda-1)^2) on that interval. Thus
\[
 \operatorname{rank}\mathbf1_{\{|B-I|>t\}}\le2\cdot10^7\delta/t^2. \tag{4.1}
\]
For (R\ge2), the source's explicit bound (\omega(\lambda)\ge(117/172000)\sqrt\lambda) on ([2,\infty)) gives
\[
 k_R:=\operatorname{rank}\mathbf1_{(R,\infty)}(B)
       \le(344000000/117)\delta/\sqrt R.                     \tag{4.2}
\]
Equations (2.4)–(2.5) also show that the *output rows* of the regularized field in a bad spectral subspace of rank (k) have energy at most ((2q(0)^2\,40/37+80/3)k). Both are legitimate dimension-uniform payments. Neither controls the unregularized trace of the discarded eigenvalues.

**An additional obstruction to the proposed compression step.** In dimension (m\ge3), index coordinates by (0,1,\ldots,m-1), put (a=1/\sqrt2), and define a fully symmetric tensor by
\[
 T_{0ii}=T_{i0i}=T_{ii0}=a\quad(i>0),\qquad T_{ijk}=0\text{ otherwise}.
\]
Its slices satisfy
\[
 X_0=a\operatorname{diag}(0,1,\ldots,1),\quad
 X_i=a(e_0e_i^T+e_ie_0^T),\quad
 B=\operatorname{diag}((m-1)/2,1,\ldots,1).                  \tag{4.3}
\]
Thus (\Omega(B)/m=O(m^{-1/2})\to0), and there is only one heavy output direction. Yet for the projection (\Pi) onto its orthogonal complement,
\[
 \sum_r\|\Pi X_r(I-\Pi)\|_F^2=(m-1)/2.                    \tag{4.4}
\]
Regularizing good output rows does not change (4.4), since (S=I) there. Restricting **all three tensor slots** to the good subspace kills the whole tensor, losing squared norm (3(m-1)/2). Even full tensor symmetry does not allow a low-rank bad output space to be erased cheaply in the input index.

This is an **abstract tensor obstruction**, not a realized log-concave counterexample. Its commutators are large, and no compatible Jacobian with small source error is produced. One can assign the abstract covariance (C=S^{-1}), making the algebraic covariance discrepancy zero, but that does not realize (C) as the covariance of a compatible transport. Actual Jacobian compatibility and covariance must be used jointly. In particular, it would be invalid to apply (3.3) to the compressed good tensor merely because (4.1) says the deleted rank is small.

## 5. The remaining analytic and algebraic estimates, stated separately

Here are concrete unpaid subproblems, not new theorems or a renamed U.

### 5.1 An exact channel representation of the algebraic error

There is a useful alternative to iterating a many-matrix theorem. For any fully symmetric real cubic (T), define operators on the real Hilbert space of **all** (m\times m) matrices with Frobenius inner product:
\[
 \Phi_T(H)=\sum_rT_rHT_r,\qquad
 \mathscr P_T(H)=\sum_r\langle T_r,H\rangle_F T_r.
\]
Then
\[
 \boxed{\ \|\Phi_T-\mathscr P_T\|_{\mathrm{HS}(\mathrm{Mat}_m)}^2
                     =\sum_{r,s}\|[T_r,T_s]\|_F^2.\ }       \tag{5.1}
\]
Here the outer Hilbert–Schmidt norm is the sum over the (m^2) orthonormal matrix units; it is not an operator norm or a normalized matrix trace.

**Proof.** Full tensor symmetry gives 
\(\langle T_r,T_s\rangle_F=B_{rs}\), where (B=\sum T_r^2). The vectorized operator (\Phi_T) is (\sum_rT_r\otimes T_r), while (\mathscr P_T) is the sum of the rank-one operators formed by the vectors (T_r). Consequently each has squared Hilbert–Schmidt norm (\sum_{rs}\langle T_r,T_s\rangle_F^2=\operatorname{tr}B^2). Their inner product is (\sum_{rs}\operatorname{tr}(T_rT_sT_rT_s)). Expand the commutator squares to obtain (5.1). ∎

If (B=I), the slices are orthonormal, (\mathscr P_T) is the orthogonal projection onto their (m)-dimensional span (V), and (\Phi_T) is unital, trace preserving, self-adjoint and completely positive (the same formula acts on complex matrices). Its operator norm on Frobenius space is at most one, by the Schwarz inequality for a unital completely positive map followed by trace preservation. Thus (5.1) turns small **total normalized** commutator error into closeness of a quantum channel to a very specific rank-(m) projection, with no matrix-count exponent.

This is a proved representation, not a channel-rounding theorem. The missing statement would round this particular pair to a dephasing map
\[
 \mathscr D_U(H)=\sum_{j=1}^m(u_j^THu_j)u_ju_j^T
\]
in squared superoperator Hilbert–Schmidt norm divided by (m), uniformly in (m). It would need the linked Kraus-span structure in (5.1); approximate idempotence of an arbitrary quantum channel does not identify a maximal commutative algebra.

For clarity, **if** 
\(\|\mathscr P_T-\mathscr D_U\|_{\mathrm{HS}}^2\le b\)
is obtained in the exact-(B=I) case, tensor rounding is paid with squared error at most (3b/2). Both are rank-(m) orthogonal projections, so
\[
 \sum_r\|(I-\mathscr D_U)T_r\|_F^2=b/2.
\]
After rotating all three tensor indices, let (M) be the total squared tensor mass outside (T_{iii}). Symmetry counts two of the three permutations of each double-index term, and all distinct-index terms, in the off-diagonal matrix mass (b/2). Thus (M\le3b/4). For each (i), normalization gives (1-T_{iii}^2=\sum_{(j,k)\ne(i,i)}T_{ijk}^2). Rounding each diagonal entry to a sign costs at most this quantity. Hence the full tensor error is at most (2M\le3b/2). Signs are absorbed in the basis vectors. This argument counts the double-index terms explicitly; identifying off-diagonal matrix mass with all off-diagonal tensor mass would be incorrect.

The identity uses classical Kraus/vectorization algebra; no independent novelty claim is made for it. The nonzero-(B-I) passage, channel-to-diagonal-algebra estimate, and preceding analytic extraction still require work.

### 5.2 Unpaid extraction, rounding, and heavy-direction estimates

**Bounded-energy coefficient extraction.** For symmetric matrices (X_r) with (B\preceq KI), does there exist a dimension-independent modulus (\chi_K(\varepsilon)\downarrow0) such that
\[
 \frac{\|X-\operatorname{Sym}X\|_F^2+
          \sum_{r,s}\|[X_r,X_s]\|_F^2}{m}
 \le\chi_K\!\left(\frac{\|\operatorname{curl}q(L)\|_2^2}{m}\right)? \tag{CE}
\]
This is a question about integrated derivatives of one explicit matrix function. It contains no density distance, entropy or unknown orientation. The residuals are bounded on this class: (\sum_{rs}\|[X_r,X_s]\|_F^2\le4\operatorname{tr}B^2\le4K^2m). The exact source proof identifies them from two jets at zero; (3.3) controls a Gaussian average instead. We have not proved the required conversion. Gaussian concentration at the origin and an inverse-(q) bound cannot provide it uniformly.

**Normalized real algebra rounding.** If (T\in\operatorname{Sym}^3\mathbb R^m), (\sum T_r^2\preceq KI), and
\[
 \frac{\|\sum T_r^2-I\|_F^2+\sum_{rs}\|[T_r,T_s]\|_F^2}{m}
          \le\varepsilon,
\]
find a dimension-independent modulus controlling
(m^{-1}\inf_U\|T-U^{\otimes3}\sum e_i^{\otimes3}\|_F^2).
I56 proves this only after **total** distance is small. Its Taylor remainder (\sqrt5d^2) becomes (\sqrt{5m}(d/\sqrt m)^2) after normalization and does not give the desired entrance. Conventional many-matrix theorems still have matrix-count-dependent exponents; the fresh Bansil–Kachkovskiy result does too (§9). No global normalized rounding is proved here.

**Heavy-direction interface.** Before those two bounded-energy questions can address general (f), (4.1) must be combined with actual compatibility to obtain a large good subspace on which the compressed field remains approximately compatible, with the cross-slot cost charged to (\delta) at averaged scale. The star tensor shows why rank counting alone fails. The covariance-normalized field (Q=S^{1/2}q(L)) and its exact defect (3.1) provide a globally bounded-energy alternative, but (S^{1/2}L) has nonsymmetric slices and is not the argument of the same scalar functional calculus. We have not removed that obstacle.

If a single normalized cubic approximation were obtained, the remaining law reconstruction is already paid: forward (q)-Lipschitzness, Gaussian Poincaré and the source lower bound (P\succeq q(0)I) give the same normalized cost as the coefficient approximation, plus (O(\delta/m)). Alternatively (2.3) pays the regularized normalization directly. Local or point-dependent bases cannot be substituted for this single orientation.

## 6. Route B: probabilistic decomposition and exact deficit accounting

**Missing dimensions have a definite coupling price.** If (V) is centered isotropic in (\mathbb R^m), (E\) is a (d=m-k) dimensional subspace and the marginal (\Pi_EV) can be coupled to an orthogonal (Z_d) with cost (b), then
\[
 d_m(V)^2\le b+2k.                                        \tag{6.1}
\]
Indeed, disintegrate the law of (V) over its (E)-projection and lift the marginal coupling. Append an independent (Z_k) in (E^\perp), independent of the whole construction. The reference law is a product across the two orthogonal blocks. Its missing-block cost is (E|\Pi_{E^\perp}V|^2+E|Z_k|^2=2k), since the cross term vanishes. No independence of the original blocks is assumed. This proof also explains why simply dropping bad dimensions without paying (2k) is insufficient.

To account for a flag, let (V=(V_1,\ldots,V_m)) in one fixed orthonormal basis and write
\[
 \mu_i(v_{<i})=E[V_i\mid V_{<i}=v_{<i}],\quad
 s_i(v_{<i})^2=\operatorname{Var}(V_i\mid V_{<i}=v_{<i}),
\]
\[
 \delta_i(v_{<i})=h(V_i\mid V_{<i}=v_{<i})-1-\log s_i(v_{<i}).
\]
Conditional densities are log-concave: integrate the joint density over later coordinates (Prékopa), then restrict to the affine fiber and divide by its mass. They are nondegenerate almost everywhere. Where these quantities are integrable, the entropy chain rule yields the **exact** formula
\[
 \delta(f)=\sum_iE\delta_i+\sum_iE\log s_i.                 \tag{6.2}
\]
For general cases one must first use integrable truncations/extended expectations; a difference of infinities is not a usable budget. The examples below have finite terms. Isotropy only gives
\[
 E s_i^2+E\mu_i^2=1,
 \qquad E\log s_i\le\tfrac12\log E s_i^2\le0.              \tag{6.3}
\]
Thus it gives the wrong sign for an upper bound on (\sum E\delta_i). For a block conditional the correction is (\frac12 E\log\det\operatorname{Cov}(V_{\rm block}\mid V_{\rm past})), not a free additive marginal deficit. For independent blocks the correction disappears after block whitening, but that is the already excluded basic-product case.

**Actual equality-law cancellation.** Let (E_1,E_2) be independent exponentials and set
\[
 U=(E_1+E_2-2)/\sqrt2,\qquad V=(E_1-E_2)/\sqrt2.
\]
This is a centered isotropic, log-concave, orthogonally rotated equality law: (\delta(U,V)=0). Write (R=E_1+E_2\sim\Gamma(2,1)), and (\psi) for the digamma function. Its first scalar gap is
\[
 \delta_U=1-\psi(2)-\tfrac12\log2>0.
\]
Given (R=r), (V) is uniform on ([-r/\sqrt2,r/\sqrt2]), with variance (r^2/6). Therefore
\[
 E\delta_{V\mid U}=\tfrac12\log12-1>0,
 \qquad E\log s_{V\mid U}=\psi(2)-\tfrac12\log6.
\]
The three expressions sum exactly to zero. Their floating values are approximately (0.2306421,0.2424533,-0.4730954). Independent copies of this rotated pair make (\sum E\delta_i\) proportional to (m), while the **actual joint deficit is zero**. This is a counterexample to the proposed additive conditional budget in an arbitrary flag, not to U. It also defeats any claimed small conditional-covariance loss from small joint deficit before choosing a suitable global basis.

One could try to optimize the flag, but neither scalar localization nor pointwise choices of conditional signs construct one global orthogonal exponential law. Nonlinear conditional means and scales incur coupling costs; conditional sign changes need not form an independent product either. We do not nominate the conditional statement obtained by assuming these costs are small. The independent radial construction below is an actual law comparison that avoids those assumptions.

## 7. A proved dependent, growing-dimensional test-class result

**Theorem 7.1 (orthant-radial laws).** Let (m\ge1), and let (g:[0,\infty)\to[0,\infty)) be log-concave, not almost everywhere zero, such that
\[
 f(x)=c\,g(x_1+\cdots+x_m)\mathbf1_{\{x_i\ge0\}}
\]
is a full-dimensional probability density. Let (\widehat f) be its centered covariance whitening. Then
\[
 0\le\delta(f)\le1,\qquad d_m(\widehat f)^2\le\frac{4m}{m+1}<4. \tag{7.1}
\]
Every invertible affine image has the same conclusions after whitening. No monotonicity of (g), differentiability, or support unboundedness is required. The lower entropy bound uses the pinned theorem; the upper bound and coupling below are elementary and would hold independently of that premise.

**Proof.** Let (S=\sum_iX_i). The change of variables (X=SU) gives independence of (S) and (U), with (U\sim\operatorname{Dirichlet}(1,\ldots,1)) and
(p_S(s)=c s^{m-1}g(s)/(m-1)!). Set (\mu=ES>0), (v=\operatorname{Var}S>0), (M_2=ES^2), and (e=m^{-1/2}\mathbf1).

We first prove the radial moment bound (v\le\mu^2/m). Compare (p_S) to the gamma density (p_0) of shape (m) and mean (\mu). The logarithm of their ratio, on its support, is (\log g(s)+(m/\mu)s+\text{constant}), a concave function. Hence the positive set of (p_S-p_0) is an interval. Equal total mass and equal first moment force either equality of the densities or the sign pattern (-,+,-) with two finite crossing locations (a<b). A single-crossing pattern would give a strict nonzero first-moment difference after subtracting the crossing location times the zero mass difference. In the two-crossing case,
\[
 (s-a)(s-b)(p_S-p_0)(s)\le0.
\]
Integrate; the constant and linear terms cancel. Thus (ES^2\le E_0S^2=(1+1/m)\mu^2). This argument also handles flat crossing intervals by choosing their endpoints; the gamma reference is positive everywhere. Finite moments follow from integrability and log-concavity. This is a classical sign-crossing/moment-comparison technique, not a new localization principle.

The Dirichlet moments give
\[
 E\|U-\mathbf1/m\|^2=\frac{m-1}{m(m+1)},\quad
 \operatorname{Cov}X\big|_{e^\perp}=\frac{M_2}{m(m+1)}I,
 \quad \operatorname{Var}\langle X,e\rangle=v/m.
\]
Thus the centered whitened vector is
\[
 Y=aS(U-\mathbf1/m)+\frac{S-\mu}{\sqrt v}\,e,
 \qquad a=\sqrt{m(m+1)/M_2}.
\]
Independently of (S,U), choose (R\sim\Gamma(m,1)). The vector (RU) has iid exponential coordinates. Couple (Y) to
\[
 Z=R(U-\mathbf1/m)+(R-m)e/\sqrt m.
\]
The two displayed orthogonal components give the **exact cost of this coupling**
\[
 E\|Y-Z\|^2
 =\frac{m-1}{m(m+1)}E(aS-R)^2+2
 =2+2(m-1)\left(1-\sqrt{\frac m{m+1}}\frac\mu{\sqrt{M_2}}\right).
                                                               \tag{7.2}
\]
The moment bound implies (a\mu\ge m), so the transverse term is at most (2(m-1)/(m+1)). This proves the W2 assertion, including (m=1). Notice that the deliberately independent radii give a nonzero cost even at the exponential equality law; (7.2) is not asserted to be optimal.

For entropy, direct integration gives
\[
 h(X)=h(S)+(m-1)E\log S-\log\Gamma(m),
\]
and the covariance determinant is ([M_2/(m(m+1))]^{m-1}v/m). Therefore
\[
 \delta(f)=h(S)-\tfrac12\log v+\tfrac12\log m
 +(m-1)\{E\log S-\tfrac12\log M_2+\tfrac12\log(m(m+1))\}
 -\log\Gamma(m)-m.                                         \tag{7.3}
\]
All logarithmic moments are finite: near zero an integrable log-concave (g) on a half-line is bounded above, and (s^{m-1}|\log s|) is integrable; the tail is exponentially bounded. The Gaussian maximum-entropy inequality and Jensen bound the first term by (\frac12\log(2\pi e)) and the brace's first two terms by zero. For integer (m\ge1), the standard Stirling lower bound
(\log\Gamma(m)\ge(m-1/2)\log m-m+\frac12\log(2\pi))
then yields
\[
 \delta(f)\le\frac12+\frac{m-1}{2}\log(1+1/m)\le1.
\]
Finally, if an invertible affine map (M) acts on (X), its whitening differs from the whitening of (X) by the orthogonal matrix ((MCM^T)^{-1/2}MC^{1/2}). Entropy gap is affine invariant and the comparison is the full orbit. ∎

This theorem rules out all such radial laws as counterexamples with nonvanishing normalized distance as (m\to\infty), even when their normalized deficits tend to zero. It does **not** prove U on the class for arbitrarily tiny deficits, or rule out a violation of U's particular rate: (7.1) does not become small when (\delta\ll1/m). It is supporting progress, not a proposed eighth substantial finding.

## 8. Actual families, exact formulas, and diagnostic limits

The read-only [diagnostics](../experiments/i59_dimension_uniform_entropy_stability/diagnostics.py) separate rational assertions from floating evaluation.

* **Asymmetric Laplace products.** (X=E-aE') has the stated asymmetric Laplace density. Centering and dividing by (\sqrt{1+a^2}), the coupling with (E-1) costs exactly (2-2/\sqrt{1+a^2}). The gap per coordinate is (\log(1+a)-\frac12\log(1+a^2)). For products use (a=m^{-1/2}). These are rigorous formulas for one chosen coupling; the printed decimal evaluations are floating approximations. This revisits an old test family, not a new finding. Its full support still makes the directed KL claim impossible.
* **Truncated exponentials.** For density (e^{-x}/(1-e^{-R})) on ([0,R]), (\mu=1-R/(e^R-1)), (v=1-R^2e^R/(e^R-1)^2), and scalar gap (\log(1-e^{-R})+\mu-\frac12\log v-1). Products use (R=\log m+2). Two midpoint resolutions approximate the exact monotone-coupling integral; they are **not certified upper bounds**. At (m=512), the two per-coordinate values are about (0.0004391) and (0.0006412); the visible discrepancy is retained, not described as convergence certification.
* **Uniform simplices.** The standard simplex is orthant-radial with (S\sim\operatorname{Beta}(m,1)). Its exact gap is
  \[
   -\log(m!)+\frac{m+1}2\log(m+1)+\frac m2\log(m+2)-m
        \longrightarrow\frac32-\frac12\log(2\pi)>0.
  \]
  Equation (7.2) has cost tending to 3, while its normalized cost tends to zero. At (m=2048), the floating gap is (0.5806549), cost (2.9996333). This is a useful distinction: high-dimensional uniform simplices have bounded total entropy gap, not a gap proportional to dimension.
* **Dependent radial gamma tilts.** (g(s)=s^{a-m}e^{-s}), (a\ge m), is log-concave and has (S\sim\Gamma(a,1)). It is nonproduct for (a>m). Its entropy is (a+\log\Gamma(a)+(m-a)\psi(a)-\log\Gamma(m)), with covariance eigenvalues (a(a+1)/(m(m+1))) and (a/m). For (a=\kappa m), fixed (\kappa\ge1), (7.3) gives (\delta\to1-1/\kappa). The bounds survive arbitrary dense, ill-conditioned invertible affine coupling because whitening changes only the reference orientation.
* **Cone laws.** The source's cone over (K\subset\mathbb R^n) has deficit (n\log(L_{\Delta_n}/L_K)). A simplex cone is exactly an affine exponential product, so whitened distance is zero. A cube cone has normalized deficit tending to (\frac12\log12-1>0), so it does not probe the difficult small-normalized-deficit regime. The calculation retains the extra height dimension and the covariance factors ((n+1)(n+2)), (n+1).
* **Positive-orthant (\ell_p) balls.** These are actual convex bodies for (p\ge1), with volume (\Gamma(1+1/p)^m/\Gamma(1+m/p)). The exact coordinate and cross moments are
  \[
  E X_i^k=\frac{\Gamma((k+1)/p)}{\Gamma(1/p)}
          \frac{\Gamma(1+m/p)}{\Gamma(1+(m+k)/p)},\quad
  E X_iX_j=\left(\frac{\Gamma(2/p)}{\Gamma(1/p)}\right)^2
          \frac{\Gamma(1+m/p)}{\Gamma(1+(m+2)/p)}.
  \]
  We compute the two covariance eigenvalues and the whitening entropy at (p=1+m^{-1/2}). For (m=32,128,512), the floating normalized gaps are about (0.08413,0.04334,0.02191). No whole-orbit W2 lower bound is obtained, so these cannot refute U. They test a coupled, nonradial perturbation of a simplex beyond products.

There are 192,926 exact rational assertions, including 90 Gaussian Hodge cases through dimension 5 and chaos degree 5, 20 independent channel-identity cases, the exact surplus identity for degrees 2–1000, Dirichlet/covariance identities and the fully symmetric heavy-star construction. These are independent finite algebra checks, not a formal or universal proof certificate. The floating output includes 47 family records. It does not optimize over the orthogonal orbit. An initial missing optional `mpmath` import was removed; the final diagnostics use only the standard library and an explicitly finite asymptotic digamma evaluation. The failed dependency attempt is recorded in the work history; no source or prior seal was changed.

## 9. Primary comparisons and novelty boundary

The [primary manifest](../sources/i59_dimension_uniform_entropy_stability/literature/manifest.json) records 23 fresh responses, all HTTP 200, exact bytes/hashes, UTC timestamps, served versions and 12 PDF-to-text extractions. A successful MathDB response did not establish a target-specific score or ranking; none is asserted. Old source/review failures and seals are hash-referenced unchanged. The retained arXiv versions are FMS v1, MNR v2, FK v2, Bansil–Kachkovskiy v1, Auddy–Yuan v2, BDHR v1, BDS v1, Courtade–Fathi–Pananjady v1, Kipp v2 and Rademacher v2. These are the versions served at capture, not a claim about inaccessible publisher changes.

* [Fradelizi–Marín Sola](https://arxiv.org/abs/2406.07406), Proposition 5.2 and Lemma 5.2, supply the entropy/simplex equivalence through auxiliary dimensions and the fixed cone moment identities. Their log-Laplace variation concerns functional Mahler minimizers. These do not give the required entropy-to-W2 near-extremizer estimate. The final 2026 journal full text was not independently obtained here; the accessible preprint is the comparison used.
* [Melbourne–Nayar–Roberto, published author PDF](https://perso.pages.math.cnrs.fr/users/cyril.roberto/Articles/Melbourne-Nayar-Roberto.pdf), Theorem 1.1 and §§3.1–3.3, give the scalar entropy inequality, entropy-preserving decreasing rearrangement with increased variance, and extremal reduction to two-piece log-affine laws. These do not quantitatively align conditional extremizers across fibers. The sign-crossing comparison used in §7 is a classical kind of moment argument, also present in their scalar proof; it is not claimed as an invented technique.
* [Filonov–Kachkovskiy](https://arxiv.org/abs/1008.4002), Theorems 2–3, give normalized Hilbert–Schmidt powers (1/4) for a pair and (1/4^{k-1}) for (k) matrices, with a count-dependent threshold. Their block proof has no uniform (k=m\to\infty) consequence of the required kind.
* **Fresh stronger comparison:** [Bansil–Kachkovskiy, August 2026](https://arxiv.org/abs/2608.31000), Theorem 1.1 improves the pair power to (1/3), with the extra condition that the rounded first matrix commute with its original. Theorem 1.3 handles one matrix against (N) others but has an explicit (\sqrt N) factor. Corollary 1.4 has squared-distance power (2/3^{N-1}) and (C(N)). We read its spectral partition minimization and averaging construction, including the count dependence. This improves the prior comparison without closing normalized symmetric-algebra rounding; the two-matrix statement must not be advertised as uniform in the growing family size.
* [Biaggi–Draisma–Seynnaeve, published Proposition 4.1](https://rendiconti.dmi.units.it/volumi/54/017.pdf), and the Robeva attribution retained in I56, already identify the cubic tangent equations. [BDHR](https://arxiv.org/abs/1512.08031) characterizes exact associativity. [Auddy–Yuan](https://arxiv.org/abs/2007.09024), Theorems 2.4/3.1 and the polar-factor proof, assume existing odeco tensors or a factorization with almost-isometric factors. No normalized equation-residual entrance theorem is supplied by those hypotheses. I56's technical replacement remains fully credited.
* [Courtade–Fathi–Pananjady](https://arxiv.org/abs/1610.07969), Theorem 1, Corollary 1 and §3.1, concern the EPI deficit and Gaussian extremizers. The proof uses a uniform potential curvature lower bound to obtain contraction and quantitative log-determinant concavity. The hypotheses and deficit differ from U; an exponential equality law here has no such curvature bound. We use neither their theorem nor Gaussian log-Sobolev stability as a substitute.
* [Rademacher](https://arxiv.org/abs/1404.5662), Theorems 1–2, and [Kipp](https://arxiv.org/abs/2411.08722), Theorem 1.5 and its moment-kernel/second-variation proof, constrain local isotropic maximizers. They do not give an arbitrary-body dimension-uniform entropy stability estimate. The cone support/section passage would still require a paid quantitative argument even if U were known.

No exact duplicate was identified in this bounded audit; that observation cannot certify priority. The remainders and Hodge estimate are technical source/classical deductions. The radial theorem is a supporting test-class result. The substantive general bridges—heavy-direction compatibility, normalized coefficient extraction, and global algebra/orientation recovery—are still open in this report. No MathDB score, accepted-count increment, or worldwide priority claim is made.

## 10. Evidence, limitations, and handoff

Only the assigned I59 report/source/experiment paths were written. Twelve inputs are frozen, including the four mutable ledgers; their live drift is informational. Fifteen source blobs are checked against the complete tree at the pinned revision. The existing 254 I53/I55/I56 evidence files are hash-referenced without recursive archive duplication or old seal refresh. Proof passages, read ranges and the precise prior objections/dispositions are retained in the I59 source directory. The source search result counts are 5, 39 and 46 for the three explicitly stored patterns; their limited breadth is visible, and the full corpus inventory is checked independently.

From the project root:

```bash
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i59_dimension_uniform_entropy_stability/diagnostics.py
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i59_dimension_uniform_entropy_stability/verify.py
```

Both commands are offline and read-only. The verifier checks the I59 seal, frozen inputs, all corpus hashes/Git blobs and inventory, the 15 selected source blobs, search line multisets, old evidence hashes, captured responses, PDF text replays, passage slices and deterministic independent diagnostics. It prints mutable-ledger drift separately. It does not re-audit pinned proofs, refresh old seals, or turn floating diagnostics into analytic certification. Network capture helpers are separate one-shot tools and refuse to overwrite their original manifests.

The strongest immediate continuation is to attack (CE) using the **integrated** bound (3.3), while separately seeking an actual-compatible replacement for the failed cross-slot deletion (4.4). A result on either one alone would still need the other interfaces before proving U. The probabilistic alternative must choose a global basis while controlling the negative conditional log-variance correction in (6.2); the rotated equality example prevents treating that correction as negligible a priori. No completed dimension-uniform deficit modulus or realized counterexample is available for parent integration.
