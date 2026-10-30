# Arithmetic162h — independent full correctness review

**Verdict: PASS**, conditional only on the stipulated true source and operative upstream inputs at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

This verdict covers **both entire frozen claims**, with the unchanged statement SHA256 `1d2799dba1c5bffca37724769974e56dc0e6c6ec2ac0196a01c3f15039ce6133` and unchanged author proof SHA256 `92fe6bd2f718c85e558861588c3828dfdc039cff22f5e19fabcc67daa211db01`. No necessary mathematical repair, counterexample, or essential unverified dependency remains in that scope. The explanations below reconstruct and check the author's arguments; they do not amend the statement, substitute a weaker theorem, or supply a different hypothesis. No contribution, acceptance, or count decision is made.

Provenance: independent first correctness review, authorized Codex / GPT-6 Astra / high / default service tier. No other review or its status was consulted. Full reading and isolation details, including limits, are in `private/READING-AND-DEPENDENCIES.md`.

## 1. Exact scope and dependency boundary

The state space is the entire compact normalized injective holomorphic class

\[
\mathcal K=\{F:\mathbb H\to\mathbb C:\ F\text{ injective and holomorphic},\ F(i)=0,\ F'(i)=1\}.
\]

For each \(\beta\in[3/4,1]\), the probability \(P\) is assumed to obey the exact inverse-square covariance at **every** \(x\in\mathbb R,y>0\), for **every** nonnegative Borel test, including tests with infinite expectation. The proof preserves these quantifiers. It produces one Borel selection \(A\) on all of \(\mathcal K\), independent of \(P,\beta,E,m\), and proves the stated expected **squared** compact \(C^m\) error bound with exponent \(1/4\), for each nonempty compact \(E\subset\mathbb H\) and each finite integer \(m\). Constants depend on \(E,m\), not on the law or exponent. At \(\beta=1\), it identifies the whole probability measure, removes the affine atom, and verifies covariance for all the specified tests.

The operative stipulated source dependencies are the compact-family bounds, classical univalence estimates, local differential/area operations, and the geometric framework in the two complete Source072 textual proofs. Their stated \(\rho>2\) inverse-square law construction is **not** used to produce the hypothesized law here. The original persistence operation is the finite oldest-component rule in Edelsbrunner–Letscher–Zomorodian (2002), Sections 2–4, specifically the union-find rule on printed p.523. I read the actual operation and independently check its smooth infinite-fiber extension below. No unexamined theorem of infinite persistence, measurable selection, or quantitative stability is assumed. Hedenmalm–Shimorin v1 is a comparison read, not an additional premise.

## 2. Covariance, moments, and the parameter range

Write \(Q=1/F'\), \(\eta=1-\beta\), \(k=(\beta+3)/4\), and

\[
q=-iyF''/F'=a+ib,\qquad G_k=F-iyF'/k,\qquad J_k=\det DG_k/|F'|^2.
\]

Then \(15/16\le k\le1\). Compactness of \(\mathcal K\), local convergence of all holomorphic derivatives, and nonvanishing of \(F'\) give uniform bounds for all local jets of both \(F\) and \(Q\). They also give positive lower bounds for \(|F'|\) and \(|Q|\) on each fixed compact source set. These statements concern the full class, without boundary or image restrictions.

Direct differentiation gives the real derivative columns

\[
(G_k)_x=(F'/k)(k+q),\qquad (G_k)_y=(iF'/k)(k-1+q).
\]

Their real determinant is

\[
k^2J_k=k(k-1)+(2k-1)a+|q|^2. \tag{R1}
\]

The constant covariance test gives \(\mathbb E|Q(x+iy)|^2=y^{-\beta}\). Its first real derivatives and Laplacian may be differentiated under expectation by the local uniform bounds. Since \(Q(i)=1\),

\[
\mathbb Ea(i)=-\beta/2,\qquad \mathbb Eb(i)=0,\qquad
\mathbb E|q(i)|^2=\beta(\beta+1)/4.
\]

In particular, \(2k-1=(\beta+1)/2\) cancels the last two expected terms in (R1), and

\[
\mathbb EJ_k(i)=\frac{k-1}{k}=-\frac{\eta}{\beta+3}. \tag{R2}
\]

The sign and denominator are correct, including at \(\beta=1\). The normalized variables \(q,J_k\) are affine-equivariant; their root values are bounded uniformly over \(\mathcal K\) and the whole parameter interval.

## 3. Escape and good targets at \(\beta\le1\)

The needed escape statement follows from the assumed law, not from extending the source eigenmeasure theorem past its hypothesis.

Let \(S_0=\{|(z-i)/(z+i)|\ge1/2\}\). Applying covariance at \(z=x+iy\ne i\) to \(|F(z^\#)|^{-4}\), where \(z^\#=(-x+i)/y\), gives

\[
\mathbb E[|F'(z)|^2|F(z)|^{-4}]
=y^{-\beta-4}\mathbb E|F(z^\#)|^{-4}.
\]

This uses \((T_zF)(z^\#)=-F(z)Q_F(z)/y\). The inversion preserves \(S_0\), reverses the height, and has absolute Jacobian \(y^{-3}\). Injectivity and the source bound \(|F|\ge1/16\) on \(S_0\) give

\[
\mathbb E I(F)\le\int_{|w|\ge1/16}|w|^{-4}\,dA(w)=256\pi,
\quad I(F)=\int_{S_0}y^{\beta+1}|F(z)|^{-4}\,dA(z).
\]

All integrands are nonnegative Borel, so Tonelli applies without a prior integrability assumption. Thus \(I(F)<\infty\) on a single full-measure set.

For such \(F\), disks \(B(z,y/2)\) escape every bounded \(|x|+y\) region when their centers do, and eventually lie in \(S_0\). Submean and \(4k=\beta+3\) imply

\[
(y^k/|F(z)|)^4\le C_\beta\int_{B(z,y/2)}(\Im w)^{\beta+1}|F(w)|^{-4}\,dA(w)\longrightarrow0.
\]

This uniform tail excludes source infinity at heights bounded below, and bounds the heights of preimages of any fixed compact target set. For a compactly supported smooth nonnegative target function \(\psi\), the function \(h(s)=\int\psi(F(x+is))\,dx\) has compact support on every strip bounded away from zero. Consequently the integrations by parts in author §2 are justified and give

\[
h(s)=\int_{y>s}(y-s)|F'|^2(\Delta\psi)(F)\,dA,
\qquad 0\le h(s)\le Y_\psi\|\Delta\psi\|_1.
\]

The second inequality bounds the absolute value of the signed integral. Conformal change of variables is legitimate by injectivity. It supplies a height-uniform horizontal preimage-length bound, with a map-dependent constant; no uniformity in \(F\) is needed here.

For omitted targets of bounded modulus at a scale \(h\), a witness with \(h\le y\le2h\) and \(V_\xi=y^k/|F-\xi|\ge\delta\) satisfies \(y|F'|\le4|F-\xi|\). Rebasing puts the entire horizontal cell at height \(h\) in a fixed source compact, so its image is within \(C_\delta h^k\) of every target witnessed by that cell. The horizontal-length bound permits at most \(C_{F,R,\delta}/h\) cells. Hence finitely many target disks cover all such witnesses with total area \(O(h^{2k-1})\). The dyadic sum converges because \(2k-1\ge7/8>0\). Taking the countable choices of target radius and threshold proves the uniform small-height decay for almost every omitted target. Interior targets have a small closed disk with compact inverse image; below its minimum height the denominator is bounded away from zero. These arguments cover simultaneous horizontal escape and small height as well as fixed horizontal locations.

Thus for almost every \(F\) and almost every target, every positive closed superlevel is compact. Relative closedness is expressed by \(|F(z)-\xi|\le y^k/\delta\), so the possible pole is included correctly.

The additional regularity and distinct-critical-value conditions are also valid. Singular values of a smooth plane map have area zero by the stipulated source's local covering argument. On two distinct nonsingular branches over a fixed target neighborhood, the difference of critical log values has target differential

\[
v\longmapsto\Re\left[v\left((F(z_1)-\xi)^{-1}-(F(z_2)-\xi)^{-1}\right)\right].
\]

It is nonzero because \(F\) is injective. The tie locus is locally a smooth curve. A countable branch cover makes all such ties an area-null set.

Goodness is Borel: compact-superlevel containment is tested at rational points outside compact boxes; singular roots and separated tied pairs are projected from closed sets with compact source coordinates. Critical values can be tested continuously as \(ky^{k-1}|Q|\), avoiding the pole. The affine target similarity preserves goodness in both directions. Nothing in this step asserts unweighted almost-sure goodness of the fixed root target \(-i/k\).

## 4. Topology, oldest representatives, and infinite exhaustion

For a good pair, put \(\ell=\log V_\xi\) away from its possible pole. Independently differentiating yields

\[
\Delta\ell=-k/y^2,\quad
\operatorname{Hess}\ell=\frac{k}{y^2}
\begin{pmatrix}-(k+a)&b\\b&k-1+a\end{pmatrix},\quad
\det\operatorname{Hess}\ell=-k^4J_k/y^4
\]

at \(G_k(z)=\xi\). Its trace is \(-k/y^2\). Thus positive \(J_k\) gives a saddle, negative \(J_k\) a finite maximum. A pole is never a root of \(G_k-\xi\). The root fiber is closed and discrete, so its intersection with any positive closed superlevel is finite, including when that compact set contains the pole.

At a regular positive level, the compact smooth boundary has finitely many components, each a simple closed curve. The bounded Jordan interior lies in \(\mathbb H\). The minimum principle, with a small high-valued circle removed if there is a pole, shows that this interior lies strictly above the boundary level. Therefore the curves are not nested and their interiors are precisely the superlevel components. This uses only \(k>0\), not \(k>1\).

The critical point in author §3 is that a saddle's two rising germs are in different components of its strict upper set. The local Morse form asserted there follows from solving the derivative in a negative Hessian direction, completing the square by Taylor's integral remainder, and rescaling the remaining positive quadratic term. If the germs were connected in the strict upper set, a simple path there, joined through the saddle along the two rising germs, would give a Jordan curve. The path is compact and avoids the saddle, so its near-saddle ends can be chosen to meet only the two prescribed local sectors. One of the descending sectors lies inside this curve. The curve has \(\ell\ge\ell(s)\), while an interior point has lower value. The minimum principle contradicts this. A pole cannot prevent the argument: excise a sufficiently small circle on which \(\ell\) exceeds the boundary minimum. The author has therefore proved a genuine merger of different components, not a handle attachment inside one component.

Each rising component has a unique oldest representative, namely its pole if present, otherwise its maximum of largest value. Its closure is contained in the compact closed superlevel at the saddle value. If the pole is in its closure, a whole neighborhood of the pole is in the same strict upper component. Otherwise the maximum is attained away from the pole and away from the lower boundary, hence is a finite critical maximum. Distinct critical values make it unique. The smaller of the two representatives is always finite because there is at most one pole.

The finite primary operation is exactly applicable with levels decreasing: the higher maximum is older, the lower representative is paired with the merger, and the higher one survives. To check the infinite extension, fix any positive regular cutoff below the finitely many saddles being compared. There are only finitely many critical points above this cutoff. The normalized gradient field \(\nabla\ell/|\nabla\ell|^2\) has a complete flow across each closed slab between regular levels without critical points; the slab is compact and excludes the pole. Near a pole, \(\ell=-\log|z-z_0|+\text{smooth}\), so sufficiently high levels have one pole component. Maxima create components, and the already established saddle topology merges two components. The representative of a merged component is always the larger one. A representative killed at one merger cannot later reappear.

The rule at a given saddle uses only its strict upper components. It is consequently unchanged by lowering the cutoff. Any two saddles can be compared in one such finite truncation. This proves injectivity on the entire possibly infinite fiber, without requiring a lowest critical value or globally finite critical set. Different target fibers cannot share a partner. The original ELZ finite algorithm by itself would not prove this extension; the preceding argument in the submitted proof does.

## 5. Uniform local gain and measurable affine pairing

Rebase at a saddle to put it at \(i\) with target \(-i/k\). On one fixed disk, chosen small enough that \(|F(w)|\le1/2\) for every normalized map, the denominator of

\[
\ell_{F,k}(w)=k\log\Im w-\log|F(w)+i/k|
\]

is uniformly separated from zero. All third real derivatives are uniformly bounded, jointly over the full class and \(k\in[15/16,1]\). At the saddle the Hessian eigenvalues are \(\lambda>0\) and \(-k-\lambda\), so

\[
\lambda(\lambda+k)=k^4j,\qquad j=J_k(i)>0.
\]

Both \(\lambda\) and \(j\) are uniformly bounded; hence \(\lambda\ge c_0j\). If \(M\) bounds the third-order Taylor remainder coefficient, choose a single \(d>0\) such that \(d\lambda\) stays in the fixed disk and \(Md\le1/4\). In both positive eigendirections and for \(0<t\le d\lambda\),

\[
\ell(i\pm te)-\ell(i)\ge\lambda t^2/4.
\]

The whole punctured segment stays in the strict upper set and originates in the corresponding rising germ. At its endpoint the gain is at least \(d^2\lambda^3/4\ge c_1j^3\). Both component representatives dominate their respective endpoints. Thus the smaller finite representative also satisfies

\[
\log(V(R(s))/V(s))\ge c_1J_k(s)^3,\qquad
c_F(s):=(V(R(s))/V(s))^4\ge1+c_2J_k(s)^3. \tag{R3}
\]

These constants are universal. This estimate remains valid for arbitrarily small positive eigenvalues and needs no separation of other critical points.

The measurable-selection argument is adequate. The nonzero-J root graph has countably many continuous partial branches: a uniform local contraction in the source coordinate provides each branch, and second countability provides a countable cover. Discarding repeats gives a Borel enumeration. The possible pole has an analogous local branch and is unique. A Borel unit eigenvector for the simple positive eigenvalue gives Borel witnesses on the two rising germs.

For varying points in a strict superlevel, connectivity is a Borel relation. A path in the open set can be replaced by a polygon with rational intermediate vertices while retaining the prescribed endpoints. On each segment the two continuous quantities \(\Im z\) and \((\Im z)^k/h-|F(z)-\xi|\) have positive minima. Existence of rational positive margins can be tested at rational segment parameters; continuity extends the inequalities to the whole segment. The converse gives containment in the open set. Countably many polygons and margins therefore give exactly connectivity, even through a pole. Component membership, pole presence, comparison of all enumerated maxima, and selection of the unique largest representative are consequently Borel.

These coordinate choices establish measurability, but do not define the geometric partner ambiguously. A positive affine source change preserves the two rising germs, their components, and all comparisons of critical values; the target potential is multiplied by one positive constant throughout the fiber. Thus the selected partner and \(c_F\) are equivariant. No equivariance of an arbitrary enumeration, and no globally continuous eigenvector, is assumed.

## 6. Exact weights, exceptional targets, and fourth moment

With \(\omega_F=y^{\beta-1}|Q_F|^2\), local change of variables on disjointified diffeomorphism charts gives

\[
\int h\omega_FJ_{k,\pm}\,dA
=\int_{\mathbb C}\sum_{G_k(z)=\xi,\ \pm J_k(z)>0}
 h(z)y^{\beta-1}|Q_F(z)|^4\,dA(\xi).
\]

The second factor \(|Q|^2\) comes from division by \(|\det DG_k|=|F'|^2|J_k|\). At a critical point,

\[
y^{\beta-1}|Q(z)|^4=(V_\xi(z)/k)^4
\]

because \(4(k-1)=\beta-1\). Multiplying the saddle weight by \(c_F\) therefore gives the partner's weight **exactly**. Fiberwise injectivity justifies comparison of the entire countable nonnegative sums.

The exceptional-target transfer is also correctly weighted. Area-null bad targets give a zero positive-J spatial integral on \(\{|x|\le1,1\le y\le2\}\). Equivariance and covariance turn its expectation into

\[
2\log2\;\mathbb E[J_{k,+}(i)\mathbf1_{\mathrm{bad}}]=0.
\]

This is sufficient; the fixed target \(G_k(i)=-i/k\) need not itself be area-generic. Moreover \(J_{k,+}\) is uniformly bounded, so its fourth power also has zero expectation on this exceptional set.

Restrict partners by \(N^{-1}\le y'/y\le N\) and \(|x'-x|\le Ny\). These increasing domains are Borel and equivariant, and exhaust every good saddle since its partner is a finite point of \(\mathbb H\). The spatial boxes in author §5 then give

\[
2S\log Y\;\mathbb E[J_{k,+}(i)c_F(i)\mathbf1_{D_N}]
\le2(S+NY)(\log Y+2\log N)\;\mathbb EJ_{k,-}(i).
\]

The expected density is \(dx\,dy/y\), not hyperbolic area. For fixed \(N,Y\), first send \(S\to\infty\); then send \(Y\to\infty\) with \(N\) fixed; finally increase \(N\) by monotone convergence. The bounded negative root Jacobian makes the right side finite. No bound on total displacement or on the ratios \(c_F\) is needed in advance; the finite right side supplies the requisite integrability of the selected product. Undefined pairing products outside the domain are understood as zero, equivalently by integrating only on that domain.

Using (R3) and the weighted exceptional-set identity gives

\[
\mathbb EJ_{k,+}+c_2\mathbb E J_{k,+}^4\le\mathbb EJ_{k,-}.
\]

Combining with (R2),

\[
\mathbb EJ_{k,+}^4\le\frac{\eta}{c_2(\beta+3)},\qquad
\mathbb E|J_k|=2\mathbb EJ_{k,+}+\frac{\eta}{\beta+3}
\le C\eta^{1/4}. \tag{R4}
\]

The latter uses the probability-measure fourth-moment inequality, and \(\eta\le1/4\). The endpoint \(\eta=0\) is included in these same nonnegative inequalities. No unspecified compactness modulus replaces this rate.

## 7. Determinant identity and expected compact suprema

On each fixed compact, (R1) and the parameter interval give \(|J_1-J_k|\le C\eta\). Apply covariance to \(|J_k(i)|\), use its equivariance and the uniform positive lower bound for \(|Q|\) on that compact, and then use (R4). This proves

\[
\sup_{z\in E_1}\mathbb E|J_1(z)|\le C_{E_1}\eta^{1/4}. \tag{R5}
\]

For an independent sign check, set \(g=F'\). At \(k=1\),

\[
(G_1)_x=g-iyg',\qquad (G_1)_y=yg',
\]

so

\[
D:=\det DG_1=y^2|g'|^2+y\Im(g'\overline g),\qquad H=D/y.
\]

Consequently

\[
2iH=(z-\bar z)g'\overline{g'}+g'\overline g-g\overline{g'},
\quad
\partial_z(2iH)=g''[(z-\bar z)\overline{g'}+\overline g].
\]

The two unwanted \(\bar z\)-derivative terms cancel, leaving

\[
\partial_{\bar z}\partial_z(2iH)=(z-\bar z)|g''|^2,
\qquad \Delta H=4y|F'''|^2. \tag{R6}
\]

This establishes the sign and factor without finite-polynomial extrapolation. It is an identity for arbitrary holomorphic \(F\), and says nothing about the sign of \(J_1\).

For nonnegative \(\chi\in C_c^\infty(\mathbb H)\), two integrations by parts give

\[
4\int\chi y|F'''|^2\,dA=\int H\Delta\chi\,dA.
\]

The right side is bounded in absolute value using \(H=|F'|^2J_1/y\), local jet bounds, positive minimum height on the support, and (R5). This proves an expected local squared-integral bound \(C_\chi\eta^{1/4}\). There are no boundary terms at \(y=0\) or infinity because the cutoff support is compact in \(\mathbb H\).

The passage to suprema is deterministic before averaging. Choose a compact neighborhood of the desired compact and a fixed positive disk radius inside the region where \(\chi=1\). Holomorphic submean bounds \(|F'''(z)|^2\), uniformly for all points of that neighborhood, by a fixed multiple of the same integral. Cauchy's estimate on a further neighborhood then bounds every fixed higher derivative. Thus

\[
\mathbb E\sup_{E_2}|F^{(j)}|^2\le C_{E_2,j}\eta^{1/4},\qquad j\ge3.
\]

No interchange of expectation and supremum is used. Compact sets with empty interior are allowed by taking neighborhoods. The convex hull of \(E\cup\{i\}\) remains compact in \(\mathbb H\), since its minimum height is positive. Integrating \(F'''\) along its segments gives the Taylor remainder bounds for orders 0, 1, and 2. For orders at least 3, the quadratic Taylor polynomial has zero derivative. Taking a finite maximum, or bounding its square by the finite sum of the squared bounds, proves author (14) for all finite \(m\).

## 8. One model choice, including the center

Write \(c=F''(i)\). The model coefficient circle is

\[
\mathcal C_0=\{c_0:|c_0+i/2|=1/2\}.
\]

The author's radial projection is Borel on the whole plane, with the fixed value zero at its center. If \(r=|c+i/2|\), its distance formula and estimate are

\[
|c-\pi(c)|=|r-1/2|\le2|r^2-1/4|
=2\big||c|^2+\Im c\big|=2|J_1(i)|.
\]

At the exceptional center \(c=-i/2\), the chosen value \(\pi(c)=0\) gives distance \(1/2\) and the right side is also \(1/2\). Thus the estimate is correct there, despite the projection being discontinuous. Everywhere else it follows by dividing \(|r^2-1/4|\) by \(r+1/2\ge1/2\).

For a nonzero circle coefficient, \(\Im(1/c_0)=1\), so \(a=i-1/c_0\) is real. Expanding the normalized quadratic gives

\[
F_a(z)=(z-i)+\frac{1}{2(i-a)}(z-i)^2.
\]

The zero coefficient gives the affine model. This circle-to-parameter map is continuous into the one-point compactification, and its inverse is \(a\mapsto1/(i-a)\), extended by zero at infinity. Each finite model is injective because equality of two values with distinct arguments would force \(z+w=2a\), impossible in \(\mathbb H\). All models therefore belong to the same full state space.

Define \(A\) by applying these fixed formulas to \(F''(i)\). This is a Borel map on all of \(\mathcal K\), with no law or exponent in its definition. The boundedness of \(J_1(i)\) and (R5) imply

\[
\mathbb E|c-\pi(c)|^2\le C\mathbb E|J_1(i)|\le C\eta^{1/4}.
\]

The compact \(C^m\) distance between the two quadratic polynomials is bounded by \(C_{E,m}|c-\pi(c)|\). Combining this with the Taylor remainder and \((u+v)^2\le2u^2+2v^2\) proves **Claim A exactly as frozen**. Measurability of the error follows as well from Borel \(A\), continuity of model derivatives in the compactified parameter, and the compact sup norm.

## 9. Complete endpoint law and nonvacuity

At \(\beta=1\), Claim A has zero right side. Apply its order-zero version to a countable compact exhaustion of \(\mathbb H\) and intersect the full-measure sets. Almost every map is exactly its selected model on the whole half-plane. The model image is compact and the parameterization is a homeomorphism onto it, so it defines a Borel parameter law \(\mu\).

The affine map is fixed under every rebasing, and a non-affine map cannot rebase to an affine one (differentiate twice and invert the source affine map). Testing the Borel affine singleton gives \(\mu\{\infty\}=y^{-1}\mu\{\infty\}\), hence zero mass.

For finite parameters,

\[
T_{x+iy}F_a=F_{(a-x)/y},\qquad
|Q_{F_a}(x+iy)|^2=\frac{1+a^2}{(a-x)^2+y^2}.
\]

Horizontal covariance with \(\phi(b)=(1+b^2)\psi(b)\), for nonnegative compactly supported Borel \(\psi\), shows that the locally finite measure \(\sigma(da)=(1+a^2)\mu(da)\) is translation invariant. These are permitted Borel tests on \(\mathcal K\): define them on the compact Borel model image via its inverse parameterization and extend by zero outside it. Compact support makes the displayed integrals finite.

For completeness, translation invariance and local finiteness force all atoms to vanish. The measure of a half-open interval depends only on length; additivity and monotonicity identify it as \(c\) times length first at rational lengths and then at every real length. Such intervals determine a locally finite Borel measure on \(\mathbb R\). Therefore \(\sigma=c\,da\) and probability normalization gives

\[
\mu(da)=\frac{da}{\pi(1+a^2)}.
\]

Conversely, for every nonnegative Borel parameter test, the substitution \(a=x+yb\) gives

\[
\int\frac{1+a^2}{(a-x)^2+y^2}\phi((a-x)/y)\frac{da}{\pi(1+a^2)}
=y^{-1}\int\phi(b)\frac{db}{\pi(1+b^2)}.
\]

Taking \(\phi(a)=\Phi(F_a)\) proves the original all-Borel covariance, including infinite integrals, at every \(x,y\). This proves existence as well as uniqueness, hence **Claim B in full**.

The theorem is not vacuous below the endpoint. In the author's nonvacuity note, let \(\alpha=(\beta+3)/2\in[15/8,2]\), use the branch \(\arg(z-a)\in(0,\pi)\), and normalize \((z-a)^\alpha\) at \(i\). Equality of two powers would require argument difference \(2\pi/\alpha\ge\pi\), impossible for distinct points in the open half-plane with equal modulus. These maps are normalized and injective. Their parameter density proportional to \((1+a^2)^{-(\alpha-1)}\) is integrable, and its cancellation with the inverse-square derivative weight followed by \(a=x+yb\) gives multiplier \(y^{1-2(\alpha-1)}=y^{-\beta}\). The argument applies to every nonnegative Borel test. It realizes the entire frozen interval, without assuming that arbitrary covariant laws are power laws.

## 10. Disposition and limits

The unchanged proof establishes the full quantitative interface and the complete endpoint law, with all local compact orders, weighted exceptional-set handling, infinite-fiber compatibility, and Borel quantifiers checked. There is no identified necessary repair and no unresolved essential verification. The finite algebra check supplied by the author is not used as a theorem certificate; (R6) was independently derived for general holomorphic maps, and the topology and measure arguments were checked separately.

This review does not infer a critical law from the \(\rho=2\) operator, a conclusion for finite-scale extremizers, stability for approximate covariance, or any radial/weak/Lorentz/Orlicz endpoint theorem. The original i135 \(E_\gamma/W2\), subpower-gauge, boundary-measure, and finite-tail scopes remain unchanged. Those unclaimed applications are neither hidden premises nor repair requirements for the frozen theorem.

Authentication and the final seal concern exact bytes, membership, and modes only. They do not strengthen the mathematical verdict or assign any later gate. The parent alone decides subsequent adoption or work.
