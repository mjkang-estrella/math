# I286 analytical validation

## 1. Balls, normalization, and attainment

Fix (n\ge2), a complete simply connected smooth (M^n) with (\operatorname{Sec}\le0), and volume (V>0). Write (\mu=\operatorname{vol}_g), (C_n=n\omega_n^{1/n}), (\theta=(n-1)/n), and (R_V=(V/\omega_n)^{1/n}).

By the pinned master, `lem:distance-comparison`, the global exponential map is a diffeomorphism and its pullback metric dominates the Euclidean metric. Thus its smooth volume density (J_p(v)) is at least one. Hopf–Rinow makes closed bounded balls compact, so
\[
b(p,r)=\mu(B(p,r))=\int_{|v|<r}J_p(v)\,dv
\]
is finite at every finite (r), continuous and strictly increasing in (r\ge0), has value zero at zero, and is at least (\omega_nr^n). It consequently tends to infinity. There is exactly one (r_p(V)>0) with (b(p,r_p(V))=V), and (r_p(V)\le R_V). No finite-total-volume manifold occurs under these hypotheses. The case (V=0) is excluded because both candidate ratios are undefined.

The function (b(p,r)) is jointly continuous: use a smooth local orthonormal trivialization of tangent spaces and the smooth exponential Jacobian, with integration over a fixed Euclidean ball. This also proves continuity of (p\mapsto r_p(V)) by strict monotonicity of the inverse. One can alternatively obtain this by squeezing the limiting radius between two fixed radii on either side of (r_p(V)).

If (p_j\to p), then (r_{p_j}\to r_p). The distance functions converge uniformly, since (|d(p_j,x)-d(p,x)|\le d(p_j,p)). Indicators of the associated balls converge at every point off the limiting distance sphere, which is a smooth hypersurface and has ambient measure zero. For finite-volume (E), dominated convergence therefore gives continuity of
\[
f(p)=\mu(E\cap B(p,r_p(V))).
\]
For any basepoint (o) and any (L>0), if (d(o,p)>L+R_V), then (B(p,r_p)\cap B(o,L)=\varnothing). Hence (f(p)\le\mu(E\setminus B(o,L))), proving (f(p)\to0) as (p\to\infty). At a density point (p_0) of (E), the positive-radius ball (B(p_0,r_{p_0})) intersects (E) in positive volume. Thus (f(p_0)>0). Outside a sufficiently large compact ball (f<f(p_0)/2), and continuity gives a maximum inside that compact ball. Since
\[
\mu(E\triangle B(p,r_p))=2V-2f(p),
\]
the asymmetry infimum is attained and lies in ([0,2)). Vanishing asymmetry means equality a.e. with the maximizing ball. This proves the definition is meaningful without connectedness or boundedness of (E).

The pinned bounded equality theorem implies (\alpha_{\rm geo}=0) when (\delta=0) and (E) is bounded: its isometric ball region is an ambient ball by the exponential-map argument at the end of Section 08. Conversely, a general geodesic ball need not have zero Euclidean deficit. Thus asymmetry zero is not an equality characterization of the Euclidean comparison in a curved ambient space.

If Q286 were proved, it would additionally classify unbounded finite-volume zero-deficit sets as balls. That implication is not silently included in the pinned bounded rigidity theorem.

## 2. L1 continuity and strict finite-volume reduction

For a set (E) of volume (V>0) define (A(E)=\inf_p\mu(E\triangle B(p,r_p(V)))). Let (F) have volume (W>0), and set (d=\mu(E\triangle F)). At each fixed center the balls of volumes (V,W) are nested, so their symmetric difference has volume exactly (|V-W|). The symmetric-difference triangle inequality gives
\[
|\mu(E\triangle B(p,r_p(V)))-\mu(F\triangle B(p,r_p(W)))|
\le d+|V-W|.
\]
Taking infima in both directions proves
\[
|A(E)-A(F)|\le d+|V-W|\le2d.
\]
Since (A(F)\le2W),
\[
|\alpha(E)-\alpha(F)|
\le\frac{2d}{V}+\frac{A(F)|V-W|}{VW}
\le\frac{4d}{V}.
\tag{2.1}
\]
This proof never restricts centers to a compact set common to (E,F).

For an arbitrary (E\in BV(M)) of volume (V\in(0,\infty)), use the cutoff in the pinned `lem:finite-volume-cutoff`: (\varphi_R=1) on (B_R(o)), zero off (B_{R+1}(o)), and (|\nabla\varphi_R|\le1). Its product with (\chi_E) has variation at most (P(E)+t_R), where (t_R=\mu(E\setminus B_R(o))\to0). Coarea supplies some level (s_R\in(0,1)) of finite perimeter such that
\[
F_R=\{\varphi_R\chi_E>s_R\},\qquad
P(F_R)\le P(E)+t_R+1/R.
\]
Every such level contains (E\cap B_R(o)) and is contained in (E\cap B_{R+1}(o)), up to null sets. Therefore (\mu(F_R\triangle E)\le t_R). Lower semicontinuity yields (P(F_R)\to P(E)), and volumes converge to (V).

Apply the pinned `lem:smooth-bv-approximation` to each bounded (F_R), and take a diagonal sequence of bounded smooth domains (G_j) with (\mu(G_j\triangle E)\to0) and (P(G_j)\to P(E)). No connectedness requirement is inserted. Their volumes tend to (V>0), so their deficits converge to (\delta(E)), while (2.1) gives (\alpha(G_j)\to\alpha(E)). A universal inequality for bounded smooth domains would pass to the limit with exactly the same constant.

This is a routine reduction, not an independent substantial result. A connected-domain-only theorem would require a further argument; the reduction proved here retains disconnected sets.

## 3. Radial excess controls symmetric difference

Fix (p\in M) and (r_0=r_p(V)>0). Put (r=d(p,\cdot)) and
\[
X=(r-r_0)_+\nabla r.
\]
This field vanishes near the pole and is locally Lipschitz across (r=r_0). There is no distributional jump there because the field is continuous. The pinned Hessian comparison gives (\Delta r\ge(n-1)/r\ge0). Thus a.e.
\[
\operatorname{div}X=1+(r-r_0)\Delta r\ge1
\quad\hbox{on }\{r>r_0\},
\]
and the divergence is zero in the ball.

For unbounded (E), take a Lipschitz cutoff (\eta_T) equal to one for (r\le T), zero for (r\ge2T), with (|\nabla\eta_T|\le1/T), where (T>r_0). Since (|X|\le2T) on its support,
\[
\int_E\operatorname{div}(\eta_TX)\,d\mu
\ge \mu(E\cap\{r_0<r<T\})-2\mu(E\setminus B_T(p)).
\]
Gauss–Green for the compactly supported locally Lipschitz field gives an upper bound
\[
\int_{\partial^*E}\eta_T(r-r_0)_+\langle\nabla r,\nu_E\rangle\,dP
\le\int_{\partial^*E}(r-r_0)_+\,dP.
\]
Local smoothing justifies Lipschitz test fields in BV Gauss–Green. Let (T\to\infty). The volume tail vanishes. Therefore
\[
\mu(E\setminus B(p,r_0))\le\int_{\partial^*E}(r-r_0)_+\,dP.
\tag{3.1}
\]
If the boundary integral is infinite the estimate is trivially valid. The two sets have equal volume, so their symmetric difference is twice the exterior volume. This proves R286 in the report. The step still needed is an appropriate center with a dimension-only bound for its right side in terms of perimeter deficit. Nothing above supplies that bound.

## 4. Why exact equality regularity does not give positive-deficit stability

Let (V=|E|>0). The sharp comparison for a competitor (F) with volume (W) gives
\[
P(E)-P(F)\le C_n(V^\theta-W^\theta)+C_nV^\theta\delta(E)
\le C_nV^{\theta-1}|E\triangle F|+C_nV^\theta\delta(E).
\tag{4.1}
\]
For the last inequality use (z^\theta\ge\min(z,1)), exactly as the source does at zero deficit. At zero deficit, locality cancels exterior perimeter and leaves the local almost-minimality bound used in `prop:equality-boundary`. At positive deficit (4.1) retains a fixed error independent of the radius or volume of the modification. It is not the local almost-minimality statement in that proposition.

Likewise, for a smooth boundary variation (E_t), nonnegativity of (D(t)=P(E_t)-C_n|E_t|^\theta) only implies (D'(0)=0) when (D(0)=0). Small (D(0)>0) is not stationarity. The source's constant curvature (H_0=(n-1)/R_V) uses precisely that vanishing derivative, on both signs of every patch variation.

Even if one separately selected a compact constant-mean-curvature hypersurface of area (A) and normalized curvature (h), the sharp hypersurface Sobolev inequality alone would not pay a spectral-gap estimate from small positive slack. For (m=n-1\ge3), let (q=2m/(m-2)), (c=4/(m-2)), and (\int\phi=0). Substitution of (1+t\phi) gives
\[
s+t^2\left[c\int|\nabla\phi|^2+
\{mh^2-ms_m^{2/m}(q-1)A^{2/q-1}\}\int\phi^2\right]+o(t^2)\ge0,
\]
where (s=mh^2A-ms_m^{2/m}A^{2/q}\ge0). For fixed (s>0), division by (t^2) and (t\to0) gives no bound on the bracket. The source cancels (s=0) exactly in `eq:equality-spectral-gap`. Bounding finite-amplitude Taylor remainders and obtaining an appropriate selected surface would be new work; neither is assumed.

The filling companion has a different applicability obstruction. Its `prop:radial` and `lem:opposite-average` use a cycle maximizing (V(B)-c\mathbf M(B)^{(k+1)/k}) with *positive* value, under a supposed failure of the inequality. Once the sharp theorem is stipulated, no such positive extremizer exists for its sharp coefficient. A given boundary with small nonnegative domain deficit is not that extremizer. The weighted test-function construction and its Euler equation are not available for it.

## 5. Explicit smooth Euclidean obstruction to the curvature-energy route

For every (n\ge2) there are bounded smooth connected domains (E_k\subset\mathbb R^n) such that
\[
|E_k|=\omega_n,\quad 0\le\delta(E_k)\le C/k,\quad
\int_{\partial E_k} h_k^2\,d\mathcal H^{n-1}\ge c k
\quad\hbox{for all sufficiently large integers }k.
\tag{5.1}
\]
Here (h_k=H_k/(n-1)) is normalized scalar mean curvature; constants may depend on a fixed chosen patch and (n). This is a fully explicit *auxiliary* counterexample and not a counterexample to Q286.

Let (m=n-1), (D=B_{1/4}^m\subset\mathbb R^m), and use the upper unit-sphere graph (u_0(y)=\sqrt{1-|y|^2}). Set
\[
\phi(y)=\psi(y)=
\begin{cases}\exp(-1/(1-64|y|^2)),& |y|<1/8,\\0,&|y|\ge1/8.
\end{cases}
\]
These are smooth compactly supported nonzero functions in (D), and (\int\psi>0). For each positive integer (k), define
\[
c_k=\frac{\int_D\phi(y)\sin(ky_1)\,dy}{\int_D\psi(y)\,dy},\qquad
f_k(y)=k^{-3/2}\{\phi(y)\sin(ky_1)-c_k\psi(y)\},
\quad u_k=u_0+f_k.
\]
Replace that patch of the upper hemisphere by the graph of (u_k), leaving every other part of the sphere unchanged. For all sufficiently large (k) the graph remains well above the lower hemisphere, matches the original graph near (\partial D), and defines a smooth embedded boundary of a bounded connected domain (E_k). Its volume difference from the unit ball is exactly (\int_D f_k\,dy=0); this is vertical graph volume, with no approximate correction.

Integration by parts in (y_1), using compact support, shows (c_k=O_N(k^{-N})) for each fixed (N). Uniformly,
\[
\|f_k\|_\infty=O(k^{-3/2}),\quad
\|Df_k\|_\infty=O(k^{-1/2}),\quad
\partial_{11}f_k=-k^{1/2}\phi\sin(ky_1)+O(k^{-1/2}),
\]
and the other second derivatives are (O(k^{-1/2})). Let (L(z)=\sqrt{1+|z|^2}). Taylor's formula for the graph area, with (Du_0,Du_k) uniformly bounded, gives
\[
P(E_k)-n\omega_n
=\int_D DL(Du_0)\cdot Df_k\,dy+O\left(\int_D|Df_k|^2dy\right).
\]
For this outward-oriented sphere graph, (-\operatorname{div}DL(Du_0)=m). Thus the linear term is (m\int f_k=0), and the quadratic error is (O(k^{-1})). The Euclidean sharp comparison, also included in the stipulated source, gives the nonnegative sign. Since volume is exactly (\omega_n), this proves the deficit bound in (5.1).

The trace mean curvature of the graph is
\[
H_k=-A_{ij}(Du_k)\partial_{ij}u_k,
\qquad
A(z)=D^2L(z)=\frac{I}{\sqrt{1+|z|^2}}-
\frac{z\otimes z}{(1+|z|^2)^{3/2}}.
\]
On the bounded slope range (A) is uniformly positive definite and Lipschitz. Therefore, using the derivative estimates,
\[
H_k=m+k^{1/2}a(y)\phi(y)\sin(ky_1)+O(1)
\quad\hbox{uniformly on }D,
\qquad a(y)=A_{11}(Du_0(y))>0.
\]
The error (O(1)) includes the coefficient change (O(k^{-1/2})) multiplied by the leading second derivative (O(k^{1/2})). The other terms are uniformly bounded. Since (a\phi\) is a fixed nonzero smooth compactly supported function,
\[
\int_D a^2\phi^2\sin^2(ky_1)\,dy
\longrightarrow\tfrac12\int_Da^2\phi^2\,dy>0,
\]
by writing (\sin^2=(1-\cos(2ky_1))/2) and integrating the oscillatory term by parts. The leading term has (L^2) norm bounded below by (c\sqrt{k}), whereas the remainder has bounded (L^2) norm. The triangle inequality then gives (\int_DH_k^2dy\ge c'k) for large (k). The graph area density is at least one; division by (m^2) proves the last assertion in (5.1).

In dimension three the pinned puncture calculation, for an arbitrary smooth embedded closed boundary and (p\in\partial E), gives
\[
\int_{\partial E}\left(t-\tfrac12h(x)\right)^2d\sigma
\le\tfrac14\int_{\partial E}h(x)^2d\sigma-\pi,
\qquad t=\frac{\langle\nabla r,N\rangle}{r},\quad r=d(p,\cdot).
\tag{5.2}
\]
Indeed (\operatorname{div}_{T\Sigma}(\nabla r/r)\ge2t^2), first variation has factor (2h(x)t), and the puncture contributes (2\pi). Complete the square (2ht-2t^2=h^2/2-2(t-h/2)^2). On a smooth embedded boundary the integrands are bounded near the pole, so the source's cutoff limit applies. At the source's equality set (h=1/R) and area (4\pi R^2), the right side vanishes. For the sequence (5.1) it diverges while perimeter deficit tends to zero. This rules out the proposed direct passage from small perimeter deficit to a small right side of (5.2). It does not rule out selection, flow, transport, or Q286 itself. The underlying Willmore comparison is prior art, not a new target.

In fact (\alpha_{\rm geo}(E_k)\le |E_k\triangle B_1|/\omega_n=O(k^{-3/2})\to0). The construction is therefore entirely compatible with Q286.

## 6. The logarithm-coordinate attempt and disconnected sets

For any center, (\log_p) is a global smooth 1-Lipschitz diffeomorphism. For bounded smooth (E), it contracts hypersurface area and its volume density, so if (F=\log_pE) and (W=|F|_{\mathbb R^n}>0),
\[
W\le V,\quad P_{\mathbb R^n}(F)\le P_g(E),\quad
\delta_{\mathbb R^n}(F)\le (1+\delta_g(E))(V/W)^\theta-1.
\]
The inequality has the wrong uncontrolled normalization for invoking Euclidean stability. In addition, a translated Euclidean comparison ball in (T_pM) is not generally an ambient geodesic ball after exponentiation, and small unweighted difference does not bound the difference measured with the varying exponential Jacobian. Obtaining a suitable center, controlling its volume distortion, and transferring the comparison set are unpaid. Neither the source's metric domination nor its exact determinant-one equality argument pays finite-deficit versions of these operations.

Disconnectedness cannot be ignored in a transport argument: even in Euclidean space a disconnected domain has no domain Poincaré estimate for independent constants on components. FMP2010's actual Theorem 3.4 removes a quantitatively controlled exceptional subset before using its trace argument. Simply assuming a good trace estimate on the original (E) would omit existing essential work, as well as the ambient nonlinear bridge.

The elementary two-ball test does not refute Q286. For two far-separated Euclidean balls with volume fractions (1-\varepsilon,\varepsilon),
\[
\delta=(1-\varepsilon)^\theta+\varepsilon^\theta-1
=\varepsilon^\theta-\theta\varepsilon+O(\varepsilon^2),\qquad
\alpha\le2\varepsilon.
\]
Thus the disappearing satellite has ample perimeter cost relative to its squared volume asymmetry. Long thin tentacles may obstruct Hausdorff estimates, but small-volume tentacles alone do not furnish a positive lower bound on the volume asymmetry. Hyperbolic balls have asymmetry zero; high-curvature balls are not counterexamples either. None of these analytical checks is a numerical scan.

## 7. Disposition

The paid parts above validate the question, reduce its finite-volume scope, and reject specific faulty bridges. They do not produce a dimension-only stability constant or an explicit Cartan–Hadamard counterexample to Q286. No dimension-three theorem is obtained. No fixed-manifold compactness modulus, conditional transport hypothesis, or scaling argument is nominated as progress toward the requested twenty findings. The single global candidate remains unpaid.
