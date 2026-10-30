# Independent adversarial proof review — matrix disk rigidity

**Verdict: PASS on the full original scope, relative to the explicitly credited inputs. No mathematical repair is required.** This is a written proof review, not a theorem-acceptance, novelty, publication, or formalization decision.

The frozen candidate reviewed is `../matrix-disk-discovery/analysis.md`, SHA-256 `e74dda6b866d7780b57911aef30a2bfb99589e7036864b1da6a302072ab462b6`, 18,601 bytes. The stronger fixed-subspace channel, rational exterior inverse, and full determinant lemniscate conclusions were reviewed along with the final disk conclusion. The input has not been edited.

## 1. Exact quantifiers and dependencies

For all finite integers $n,m\geq1$, every $A\in M_n(\mathbb C)$, and every finite $M_m(\mathbb C)$-valued polynomial $F(z)=\sum_{k=0}^D z^k C_k$, use Euclidean operator norms and base-first evaluation $F[A]=\sum A^k\otimes C_k$. If

\[
M=\max_{z\in W(A)}\|F(z)\|>0,
\qquad \|F[A]\|=2M,
\]

then $W(A)$ is a closed disk of positive radius. There is no upper bound on $n,m,D$, no boundary regularity assumption, no simple-support-spectrum assumption, no initial irreducibility assumption, and no scalar coefficient-channel assertion.

The stipulated OpenAI mathematics at revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is accepted as true, as instructed. I read the actual direct manuscript operations used below and the companion interfaces; I have not audited the truth of the stipulated upstream theorems. The external geometric inputs are Jin v2 Lemma 8 and Proposition 6, read at their actual source, with Proposition 5 and the relevant regularity proof interfaces. These external results are credited, not claimed as new deductions here. The geometric input is a premise of this PASS, as identified in the task; it is not replaced by Jin's scalar extremality theorem.

I read the full inherited I245 analytic check. Only its dimension-independent exterior-map convergence and equality residual extraction are inherited. Its later simple-support rank argument is not imported into arbitrary dimension. R016's historical dimension bound and the parent's dimension-five supporting note are antecedents, not proofs of the present arbitrary-dimensional claim. R019 is an essential rank-two compatibility control, not an obstruction to this disk theorem.

## 2. Irreducible reduction and spectral separation

Normalize $M=1$. Finite-dimensional reducing decomposition gives $A\simeq\bigoplus B_\ell$ with each block unitarily irreducible. The tensor evaluation is the corresponding direct sum, after its fixed unitary tensor permutation. Some block $B$ therefore has $\|F[B]\|=2$. The credited complete bound and $W(B)\subset W(A)$ yield

\[
2\leq 2\max_{W(B)}\|F\|\leq2.
\]

Thus its own polynomial maximum is one. A scalar block cannot attain two. If $K=W(B)$ had empty planar interior, a translation and complex rotation would make every quadratic form of $B$ real. Polarization then makes the transformed matrix Hermitian, incompatible with a nonscalar irreducible block.

If $Bv=\lambda v$ for a boundary eigenvalue and unit $v$, choose a supporting normal $\nu$. The positive supporting Hermitian slack has zero quadratic form at $v$, so annihilates $v$. Combining this equality with $Bv=\lambda v$ gives $B^*v=\bar\lambda v$. Its line reduces $B$, a contradiction. Consequently $\sigma(B)\subset\operatorname{int}K$. This argument permits repeated ordinary eigenvalues and repeated maximal support eigenvalues.

Choose a fixed top singular pair for the original $F[B]$: $F[B]x=2y$, $F[B]^*y=2x$, with unit $x,y$. Write $x=\sum Xe_i\otimes e_i$, $y=\sum Ye_i\otimes e_i$. Thus $X,Y$ are $d\times m$, with Hilbert–Schmidt norms one. They do not vary with the outer domains.

## 3. Reconstructed dimension-independent outer limit

After translating an interior point to zero, choose analytic convex outer approximations with

\[
r\overline{\mathbb D}\subset K\subset\Omega_j\subset R\mathbb D,
\qquad h_j(\lambda)=c_j\lambda+c_{0j}+O(\lambda^{-1}),\quad c_j>0.
\]

The source supplies such outer domains; their Hausdorff approach to $K$ is sufficient, and nestedness is unnecessary. Exterior Schwarz estimates give $r\leq c_j\leq R$. Convexity makes $\operatorname{Re}(1+\lambda h_j''/h_j')\geq0$. The normalized exterior Herglotz representation gives probability measures $\mu_j$ with

\[
L_j(\lambda):=\log(h_j'(\lambda)/c_j)
 =2\int\log(1-\xi/\lambda)\,d\mu_j(\xi),
\qquad \operatorname{Re}L_j\leq\log4.
\]

The logarithm is the branch zero at infinity. Its coefficient of $\lambda^{-k}$ is $-2\int\xi^k d\mu_j/k$. Thus the squared $L^2$ tails are uniformly bounded by $4\sum_{k>N}k^{-2}$. Weak subsequential convergence of the probability measures, together with this tail estimate, gives strong boundary $L^2$ convergence of $L_j$. Exponentiation is 4-Lipschitz on the half-plane $\operatorname{Re}z\leq\log4$, by integration along the straight segment between the arguments. It follows that $h_j'$ and $q_j=\lambda h_j'$ converge strongly in boundary $L^2$, and $|q_j|\leq4R$. The limiting logarithm is finite almost everywhere; hence its exponential, and $q$, are nonzero almost everywhere.

The uniform derivative bound makes the boundary maps equi-Lipschitz. Subsequences give a uniform boundary limit $h$, consistent with the holomorphic exterior limit. Here the inverse-map argument in I245 is necessary: using $|h_j-c_j\lambda|\leq2R$, the inverses form a locally bounded family on $\mathbb C\setminus K$. Their nonconstant limit is inverse to $h$. Therefore $h$ maps the exterior disk onto $\mathbb C\setminus K$, and Jordan-boundary extension makes $h|_{\mathbb T}$ a homeomorphism onto $\partial K$. There is no inference of boundary injectivity from uniform convergence alone. Hardy coefficient identification gives the asserted derivative boundary values. Passing supporting inequalities along an almost-everywhere convergent subsequence shows that $q(\lambda)$ is a nonzero outward normal almost everywhere. To do this simultaneously for all $w\in K$, first pass on a countable dense subset of $K$, then use continuity in $w$.

The fixed interior spectrum means the resolvent is uniformly bounded on a neighborhood of $\partial K$. Uniform convergence of $h_j$, strong $L^2$ convergence of $q_j$, and their common $L^\infty$ bounds imply

\[
R_j=q_j(h_jI-B)^{-1}\longrightarrow R=q(hI-B)^{-1}
\quad\text{strongly in }L^2,
\]

with a common $L^\infty$ bound. The same holds for $H_j=R_j+R_j^*\to H$, with $H\succeq0$ almost everywhere. This bound is for the actual fixed nonnormal matrix resolvent; no false estimate by inverse spectral distance is used.

Define $S=X^*X,T=Y^*Y$, and let $A_j=X^*R_jX$, $B_j=Y^*R_jY$, $M_j=Y^*R_jX$, $L_j=X^*R_jY$. All four fields converge strongly in $L^2$, hence their Fourier arrays converge in $\ell^2$. Put $t_j=\max_{\overline\Omega_j}\|F\|\to1$, $\gamma_j=2/t_j\to2$, and $a_j^2=\|M_j\|_2^2\to a^2$. The same fixed singular pair is a pair for $F/t_j$.

Set $D_{Xj}=\|A_j+A_j^*\|_2^2$ and $D_{Yj}=\|B_j+B_j^*\|_2^2$. From the actual source's two ordered tests, reciprocal-weight duality, and positive-block trace comparison one gets the nonnegative residuals

\[
\begin{split}
E_{Xj}&=4a_j^2/\gamma_j^2-D_{Xj},\\
E_{Yj}&=4a_j^2/\gamma_j^2-D_{Yj},\\
E_{Bj}&=D_{Xj}+D_{Yj}-2\|M_j+L_j^*\|_2^2,\\
Z_j&=3\|Y^*X\|_{HS}^2+\sum_{k\geq1}\|X^*b_{kj}(B)Y\|_{HS}^2,
\end{split}
\]

and their exact sum

\[
E_{Xj}+E_{Yj}+E_{Bj}+2Z_j
 =2(4/\gamma_j^2-1)a_j^2\longrightarrow0.
\]

The coefficient three in $Z_j$ is correct: the cross constant coefficient is $2Y^*X$, whose squared norm is four times its contribution to $a_j^2$. Every residual tends to zero. In particular $Y^*X=0$, $L=0$, and $a>0$, since the reciprocal diagonal bound gives $a_j^2/\gamma_j^2\geq\|S\|_{HS}^2>0$.

Writing $\Delta_j=[X\ Y]^*H_j[X\ Y]$ and $J_0=\operatorname{diag}(I_m,-I_m)$, the pointwise nonnegative slack is

\[
\operatorname{tr}(\Delta_jJ_0\Delta_jJ_0)
 =\|\Delta_j^{1/2}J_0\Delta_j^{1/2}\|_{HS}^2.
\]

Strong $L^2$ convergence passes its expanded quadratic trace in $L^1$. Its limiting integral is zero, so $\Delta^{1/2}J_0\Delta^{1/2}=0$, and hence $\Delta J_0\Delta=0$, almost everywhere. No square-root convergence, rank-one conclusion, or simple-support input is present in this passage.

## 4. The new Jensen-defect argument

At fixed $j$, the direct source defines the nonnegative kernel

\[
K_j(\lambda,\mu)
 =2\operatorname{Re}\frac{q_j(\lambda)}{h_j(\lambda)-h_j(\mu)}
\]

off the diagonal, with a continuous diagonal extension. Both angular marginals equal one. Its operator $T_ju(\mu)=\int K_j(\lambda,\mu)u(\lambda)d\tau(\lambda)$ is a contraction on any finite-dimensional Hilbert-valued $L^2$.

Let $A_{kj}=X^*b_{kj}(B)X$. For a finite $N$, use the exact test coefficients

\[
C_0=\overline S,\qquad C_k=\overline{A_{kj}}/2\ (1\leq k\leq N),
\]

and set $u_{jN}=\sum_{k=1}^N C_k\lambda^k$,
$d_{jN}=\|S\|_{HS}^2+\tfrac12\sum_{k=1}^N\|A_{kj}\|_{HS}^2$.
The polynomial $G_{jN}=\sum b_{kj}C_k$ has boundary decomposition $C_0+u_{jN}+T_ju_{jN}$ into disjoint constant, positive, and negative Fourier supports. Therefore

\[
\|G_{jN}\circ h_j\|_2^2
 =d_{jN}-\delta_{jN},\qquad
\delta_{jN}=\|u_{jN}\|_2^2-\|T_ju_{jN}\|_2^2\geq0.
\]

Its diagonal paired value is exactly $d_{jN}$, a nonnegative real number. The first ordered source identity and the lower Faber coefficient bound give

\[
\gamma_j d_{jN}\leq a_j\sqrt{d_{jN}-\delta_{jN}}.
\]

At fixed $j$, the reciprocal coefficient estimate makes $u_{jN}\to u_j$ in $L^2$. Contractivity permits $N\to\infty$, including convergence of the defects. Thus

\[
0\leq\delta_j\leq d_j-\gamma_j^2d_j^2/a_j^2.
\]

Since $D_{Xj}=4d_j$, the vanished residual $E_{Xj}$ gives $d_j\to a^2/4$. The right side consequently tends to zero. No infinite polynomial is inserted into the source tests: only an inequality for finite tests is first passed to its $L^2$ completion, at fixed domain.

For any Hilbert-valued $u_j$, expanding the squared difference and using the two unit marginals gives

\[
2\delta_j=\iiint K_j(\lambda,\mu)K_j(\nu,\mu)
 \|u_j(\lambda)-u_j(\nu)\|_{HS}^2\,d\tau^3.
\]

This formula is exact, including the factor two. Strong convergence of $A_j$ implies strong convergence of $u_j=\tfrac12\overline{A_j-S}$. Choose a common subsequence with $u_j\to u$ and $q_j\to q$ almost everywhere. Uniform convergence of $h_j$, together with injectivity of $h|_{\mathbb T}$, gives pointwise kernel convergence outside the two null diagonals and derivative exceptional sets. The limiting kernel is finite there. Fatou now gives

\[
K(\lambda,\mu)K(\nu,\mu)
 \|u(\lambda)-u(\nu)\|_{HS}^2=0
\quad\text{for almost every triple.}
\]

There is no use of an operator-norm kernel limit, a limit kernel marginal identity, or a uniform strict-contraction constant.

Jin's Lemma 8 applies because $K=W(B)$ has interior and its spectrum is interior. It supplies a curved regular exposed arc. The boundary homeomorphism gives a nonempty open preimage interval $I$, of positive angular measure. For $\mu\in I$, $h(\mu)$ lies on no nontrivial boundary segment. For almost every $\lambda\ne\mu$, the nonzero outward normal $q(\lambda)$ has strictly positive support gap against $h(\mu)$. A zero gap would put both boundary points on the same support line, so their segment would be a boundary segment containing $h(\mu)$. Hence $K(\lambda,\mu)>0$.

Fubini permits a choice of $\mu\in I$ for which the almost-everywhere triple identity holds for almost every pair $(\lambda,\nu)$. Strict positivity forces $u(\lambda)=u(\nu)$ almost everywhere. Its mean is zero, so $u=0$. Therefore $X^*RX=S$ almost everywhere. Repeating the finite-test and variance argument using the second ordered test gives $Y^*RY=T$. Neither argument forces the common coefficient rank to be one; the disk kernel $K=1$ is fully compatible.

## 5. Rational cross field and fixed Gram data

Define in the physical plane

\[
C(z)=Y^*(zI-B)^{-1}X,
\qquad r(z)=\operatorname{tr}[X^*(zI-B)^{-1}X].
\]

Since $\operatorname{tr}S=1$, the constant diagonal identity gives $q\,r\circ h=1$ almost everywhere. The exterior compressed resolvent is bounded and holomorphic, including its finite value at infinity; coefficientwise Hardy uniqueness extends the constant diagonal identity throughout the exterior. On the boundary the cross field is therefore

\[
M(\lambda)=\mathcal M(h(\lambda)),\qquad \mathcal M(z)=C(z)/r(z).
\]

The phase in the nonvanishing argument is correct. For $z\notin K$, choose unit $\nu$ strictly separating $z$ from $K$, and put $D=\bar\nu(zI-B)$. Then $\operatorname{Re}D\succ0$ and

\[
\operatorname{Re}D^{-1}=D^{-*}(\operatorname{Re}D)D^{-1}\succ0,
\qquad D^{-1}=\nu(zI-B)^{-1}.
\]

Consequently $\operatorname{Re}(\nu r(z))=\operatorname{tr}(XX^*\operatorname{Re}D^{-1})>0$. Thus $r$ has no exterior zero. On the boundary $r$ is continuous because the spectrum is separated. The identity $qr=1$, with $|q|\leq4R$, gives $|r|\geq(4R)^{-1}$ almost everywhere. The continuous function $r\circ h$ satisfies this bound everywhere, because every nonempty circle interval has positive measure. Thus no boundary zero is possible either.

It follows that $\mathcal M$ is rational, holomorphic on $\mathbb C\setminus K$ and a neighborhood of the boundary, and continuous up to the boundary. Since $Y^*X=0$, $C(z)=O(z^{-2})$, while $r(z)=z^{-1}+O(z^{-2})$. Thus $\mathcal M(z)=O(z^{-1})$.

The now constant diagonal blocks make

\[
\Delta=\begin{pmatrix}2S&M^*\\M&2T\end{pmatrix},
\qquad
M^*M=4S^2,\quad MM^*=4T^2,\quad MS=TM.
\]

The displayed relations follow by direct block multiplication of $\Delta J_0\Delta=0$. They imply equal positive ranks $r_0\geq1$ and fixed input/output spaces: $\ker M=\ker S$, $\operatorname{ran}M=\operatorname{ran}T$ almost everywhere. Nonzero eigenvalues of $S,T$ agree by the two squared Gram relations and positive square roots. This is compatible with R019's rank two.

## 6. Ordered constant test, Parseval, and the polynomial channel

Write $s=\|S\|_{HS}>0$. Constancy of the diagonal field makes all its nonconstant Fourier coefficients zero. Strong coefficient convergence gives $D_{Xj}\to4s^2$, and $E_{Xj}\to0$ then gives $a=2s$.

Apply the first ordered identity to the constant polynomial $G=\overline S$. For each finite $j$, the product $(F/t_j)\overline S$ has a finite Faber expansion of degree at most $D$. Its coefficients converge to the nonnegative Fourier coefficients $U_k$ of $F(h)\overline S$. One may see this either from the triangular Faber basis or directly from uniform convergence of the boundary polynomial values. In particular $U_k=0$ for $k>D$. Passing the finite source pairing gives the positive real identity

\[
2s^2=\sum_{k,i,j}(M_k)_{ij}(U_k)_{ij}.
\]

The Cauchy–Schwarz, Parseval, and boundary multiplication inequalities form the closed chain

\[
2s^2\leq a\Big(\sum_{k\geq0}\|U_k\|_{HS}^2\Big)^{1/2}
\leq a\|F(h)\overline S\|_2\leq as=2s^2.
\]

Equality in the bilinear coefficient Cauchy–Schwarz inequality, with the displayed positive real phase and $a=2s$, gives $U_k=\overline{M_k}/2$ for every $k$. In particular $M_k=0$ for $k>D$. Equality in Parseval says that the entire negative Fourier part of $F(h)\overline S$ vanishes. Combining the positive, zero, and negative Fourier parts gives

\[
F(h)\overline S=\tfrac12\overline M
\quad\text{almost everywhere.}
\]

Here $M_0=Y^*X=0$. An equality argument that omitted Parseval would not justify this complete boundary identity; the candidate includes it. The conjugation is entrywise, not adjoint. The multiplication is $F\overline S$, not $\overline S F$. These follow directly from the base-first bilinear pairing in the actual source.

Set $E=\operatorname{ran}\overline S$, $G=\operatorname{ran}\overline T$, and choose fixed isometries $U:\mathbb C^{r_0}\to E$, $V:\mathbb C^{r_0}\to G$. The conjugated Gram identities yield

\[
(F\overline S)^*(F\overline S)
 =\tfrac14 M^{\mathsf T}\overline M=\overline S^{,2}.
\]

Thus $F$ is isometric on $E$ at almost every boundary point and maps $E$ into $G$. The unwanted polynomial component $(I-VV^*)F(z)U$ vanishes at infinitely many boundary points and therefore identically. Define the square polynomial $J(z)=V^*F(z)U$. It is unitary almost everywhere on the boundary, hence everywhere by continuity and full support of angular measure.

Put $S_E=U^*\overline S U\succ0$. Restricting the constant-test identity gives

\[
J(h)S_E=\tfrac12V^*\overline M U,
\qquad
J(h)^*=\tfrac12 S_E^{-1}U^*M^{\mathsf T}V.
\]

Consequently

\[
Q(z)=\tfrac12 S_E^{-1}U^*\mathcal M(z)^{\mathsf T}V
\]

is rational, analytic outside $K$, continuous at its boundary, and $Q(\infty)=0$. The ordinary transpose is essential: it comes from taking the adjoint of an entrywise conjugate. On the boundary $Q=J^*$ and $JQ=I$. Rational identity uniqueness on infinitely many boundary points gives $JQ=I$ identically as rational functions. Thus $Q=J^{-1}$ wherever defined. In particular $J$ is invertible throughout the exterior, with this prescribed decaying inverse.

## 7. Full determinant level and final geometry

For fixed unit vectors $u,v$, the scalar $u^*Qv$ is holomorphic in the exterior including infinity, continuous to its boundary, bounded there by one, and zero at infinity. The exterior maximum principle gives $\|Q(z)\|\leq1$. If equality held at an exterior point, choose its norming $u,v$; scalar equality in the maximum principle would make $u^*Qv$ constant of modulus one, contradicting its zero value at infinity. Hence $\|Q(z)\|<1$ throughout the exterior.

Let $f=\det J$. It is a nonconstant polynomial: $JQ=I$ and $Q(\infty)=0$ are incompatible with a nonzero constant determinant. Equivalently, all singular values of $J$ grow without bound when $\|J^{-1}\|\to0$. In the interior of $K$, the matrix maximum principle gives $\|J\|\leq1$, so $|f|\leq1$, and nonconstancy gives strict inequality. On the boundary $|f|=1$. In the exterior, $J^{-1}=Q$ with norm below one means every singular value of $J$ exceeds one, so $|f|>1$. Therefore

\[
\{|f|<1\}=\operatorname{int}K,
\qquad \{|f|=1\}=\partial K.
\]

This is the full level identity; no extra exterior components, interior level islands, or holes have been left unexamined.

If $f'$ vanished at a boundary point $z_0$, let its first nonzero local difference term have order $k\geq2$. There is a direction $\alpha$ for which the leading variation of $|f|^2$ is negative along all $k$ directions $\alpha e^{2\pi i j/k}$. For sufficiently small positive $t$, the $k$ points $z_0+t\alpha e^{2\pi i j/k}$ would all lie in $\{|f|<1\}=\operatorname{int}K$. Their average is $z_0$, contradicting convexity of the interior. Thus $f'\ne0$ on the boundary, which is smooth real analytic by the implicit function theorem. A boundary segment would force the real polynomial $|f(z_0+t\xi)|^2-1$ to vanish for all real $t$, putting an unbounded line in the full level. This contradicts compactness, so $K$ is strictly convex.

The exact Jin Proposition 6 interface is paid with numerator $f$, denominator one, and Hermitian matrices $\operatorname{Re}B,\operatorname{Im}B$. Every support line, with coordinates $s+uX+vY=0$, can be oriented so its Hermitian matrix pencil is positive semidefinite. A unit vector attaining the support point has zero quadratic form and lies in its kernel. Thus every tangent to any open boundary arc lies in

\[
\det(sI+u\operatorname{Re}B+v\operatorname{Im}B)=0.
\]

The full level, strict degree difference, strict convexity, and noncriticality established above meet the remaining geometric hypotheses. The credited circle criterion gives a circle, and $K$ is its filled disk of positive radius. This application uses the Hermitian tangent condition; a convex polynomial lemniscate alone is not being asserted to be a circle.

Finally write $K=a+\rho\overline{\mathbb D}$, $\rho>0$. The polynomial $g(z)=f(a+\rho z)$ has modulus one on the unit circle. The Laurent identity $g(z)\overline{g(1/\bar z)}=1$ shows that $g$ has no nonzero root: evaluating at such a root would give zero on the left and one on the right. Thus $g(z)=\eta z^k$, $|\eta|=1$, $k\geq1$. On the full $W(A)$, $\|J(z)\|\leq\|F(z)\|\leq1$, so $|f(z)|\leq1$. The monomial forces $W(A)\subset a+\rho\overline{\mathbb D}$, while $W(B)\subset W(A)$ supplies the reverse inclusion. The full numerical range, including all other reducing blocks, is the disk. Rescaling restores arbitrary $M>0$.

## 8. Computation audit and adversarial controls

I inspected the complete frozen `check.py` before running a byte-identical copy in this review directory. Its 17 checks pass. The arithmetic is exact Fraction arithmetic in the eight-dimensional basis of $\mathbb Q(\sqrt2,\sqrt7,i)$. Basis multiplication uses the shared-bit square factors $2,7,-1$; conjugation flips exactly the basis elements containing $i$. The adjoint is transpose after this conjugation, while the inverse test uses ordinary transpose. The R019 nilpotent resolvent coefficients are recomputed by successive matrix multiplication. The complex basis change satisfies the required transformed conjugation orientation. The variance check uses normalized counting measure and correctly obtains the factor two.

The copied checker's missing-half mutation, adjoint-for-transpose mutation, and variance-factor mutation are genuine rejected identities, not cached baseline success values. Its rectangular multiplication helper silently uses `zip`, but every tested matrix dimension in this frozen file matches; no shape truncation affects its present results. The existing R019 Gram is a scalar multiple of identity, so that certificate alone would not pressure the placement of $S_E^{-1}$ in the general formula.

I therefore wrote `supplemental-check.py` independently using a separate exact rational Gaussian field implementation. It has 16 passing checks. It constructs proper rank-two coefficient subspaces of $\mathbb C^3$, non-real rectangular isometries, and a positive Hermitian Gram matrix with unequal eigenvalues which does not commute with the chosen unitary coefficient matrix. It verifies the constant-test identity, both squared Gram identities, intertwining, restricted channel, and the displayed inverse. It detects an adjoint substituted for the transpose, a missing half, and moving $S_E^{-1}$ to the wrong side. A nonsymmetric bistochastic kernel with complex-valued input independently verifies the variance factor. These controls address cases the scalar-Gram R019 example cannot distinguish.

The tests are supporting finite algebra only. They do not prove the general analytic limit, Fatou argument, exterior conformal theorem, circle criterion, or full theorem. Their PASS is not used as a substitute for Sections 2–7 of this written derivation.

Reproduce from repository root:

```sh
python frontier/campaigns/2026-10-14/matrix-disk-proof-r1/check-copied.py
python frontier/campaigns/2026-10-14/matrix-disk-proof-r1/supplemental-check.py
```

## 9. Repairs, presentation requests, and scope limits

**Required mathematical repairs: none found.** The original full theorem and its stronger rank-$r_0$ intermediate conclusions pass. The conclusion has not been narrowed to a bounded dimension, smooth initial boundary, scalar coefficients, irreducible initial matrix, or simple support spectrum.

Optional presentation requests for a standalone paper, separate from mathematical repairs:

1. Display the finite-test Parseval identity $d_{jN}-\delta_{jN}$ and the expanded Hilbert-valued triple variance formula as separate lemmas, so the two limit orders remain visible.
2. Spell out that the boundary lower bound on $|r|$ extends everywhere through the boundary homeomorphism, rather than through an unstated equivalence of angular and arclength measures.
3. Include the three-line restriction calculation $JS_E=V^*\overline M U/2$ before defining $Q$, to make the transpose, factor, and order independently checkable.
4. Keep the full-level identity and the Hermitian tangent determinant explicit when citing the circle criterion. A boundary constant-modulus statement would be a materially weaker theorem.

No Lean full-proof certificate exists in this package, and none is claimed. No finite supporting formalization would by itself certify this complete analysis. This review does not cover rational or arbitrary holomorphic witnesses, nonattained complete-supremum rigidity, stability, a uniform deficit, classification of all witnesses, or novelty. It does not change antecedent counts or declare a new accepted theorem.

## 10. Sources, reading boundaries, and provenance

- [Pinned direct manuscript](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/build/main.tex): freshly retrieved bytes match the frozen `direct.tex` exactly. Read lines 160–535: exterior Faber theorem/proof, coefficient estimate/proof, original positive resolvent/proof, analytic-domain proof including both ordered tests, and outer approximation/proof. Used labels: `lem:faber`, `prop:coefficients`, `lem:resolvent`, `thm:domain`, `lem:approx`, and their displayed pairing, kernel, coefficient, diagonal, and cross formulas. The source's whole complete inequality is stipulated, not independently reproved as an upstream audit.
- [Pinned structural companion](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-complete-Crouzeix-theorem-September-23-2026/build/main.tex): freshly retrieved bytes match frozen `structural.tex`. Read lines 90–150 and 831–1066 to check the original mass-two field versus the similar-matrix mass-one density, tensor partial trace conventions, and the ordered comparison. It supplies no extra equality or scalarization premise for this review.
- [Jin v2](https://www.preprints.org/manuscript/202609.0079/v2): actual web rendering identified Version 2, posted 15 September 2026. Read Lemma 8 and proof (web lines 451–470), Proposition 4 regularity argument (556–595), and Propositions 5–6 with proofs (605–706). The credited inputs are the curved-arc existence and circle criterion. The proof of the geometric criterion and its projective contact interface were read, not independently rebuilt as a new theorem. The source redirects its versioned URL to the current page, which visibly identifies v2. No complete HTML/PDF byte hash is claimed from the web tool. The archived local excerpt is hashed for provenance but is not represented as a fresh full-source retrieval. No scalar extremality theorem is applied here.
- Full I245 `analytic-check.md`, R016, R019, and the parent's dimension-five supporting note were read. Their mathematical roles are limited as stated above. The original LSS paper is not a dependency of the new derivation and was not retrieved. No ACV literature review or comprehensive duplicate search is claimed in this proof gate; contribution review is separate.
- `sources/upstream.json` was read. The relevant Crouzeix entries of `sources/CONTENTS.md` were inspected as catalogue pointers; the actual source statements, rather than the catalogue summaries, support the used interfaces. Root `AGENTS.md` and `frontier/NEW-TEN-2026-10-14.md` were read.

`inputs.json` records exact local input hashes, `retrieval.json` records the two fresh pinned source matches, and `outputs.json` records the completed output hashes. All writes were confined to this assigned review directory. No shared index, candidate, staging area, commit, or count was changed; no subagent was used.
