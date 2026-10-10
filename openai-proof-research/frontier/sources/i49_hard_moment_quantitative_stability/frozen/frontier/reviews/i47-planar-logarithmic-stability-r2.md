# I47 — independent full-proof review of planar P10

**P10: PASS ORIGINAL WITHOUT REPAIRS.** The original I46 argument proves the stated exponent-10 estimate for every full-dimensional origin-symmetric planar pair between the prescribed balls, uniformly over the indicated interpolation parameters. No change of hypotheses, comparison class, exponent, mechanism, or approximation order is needed. The detailed derivations below expand the original proof; they are not replacements for failed steps.

**Construction A: its stated approximation, finite-soft-defect, hard-target coordinate, and conditional field/matrix budgets pass, with their original conditional boundaries.** This does not prove existence of the finite-defect hard fields, a quantitative conversion from position tests to normal tests, or compatible product-factor reconstruction. The full higher-dimensional finite-power target remains unproved by this work. This review makes no substantiality, acceptance, count, or priority determination.

Only this report and the assigned I47 source/experiment directories were written. No author or shared file was edited, and no agents, staging, commits, or publication were used.

## 1. Exact statement, inputs, and premise boundary

Fix \(0<r<R\), \(0<\tau<1/2\). For all full-dimensional origin-symmetric \(K,L\subset\mathbb R^2\) with \(rB\subset K,L\subset RB\), and every \(\lambda\in[\tau,1-\tau]\), set

\[
P_t=\mathcal W[h_K^{1-t}h_L^t],\qquad
\Delta_\lambda=\log|P_\lambda|-(1-\lambda)\log|K|-\lambda\log|L|.
\]

The conclusion is \(\Delta_\lambda\ge c(r,R,\tau)d_{\mathcal E}(K,L)^{10}\). Here distance uses the maximum of the two Hausdorff distances, and \(\mathcal E\) is the entire common complementary-block dilation class. In dimension two its members are homothetic pairs of arbitrary symmetric bodies or pairs of parallelograms with common edge directions and independent positive side dilations. Comparison bodies need not satisfy the original ball bounds; oblique subspaces are allowed. No smoothness, extra reflection, common fan, facet bound, or minimum facet mass is assumed.

I read the complete I46 report and brief, the I47 brief and parent objections, the relevant I44/I45 tensor, boundary, equality, and obstruction arguments, and the actual source passages recorded in `read-passages.json`. The source and experiment directory freezes all four previous sealed artifact sets, reports, briefs, source bytes, and the parent reproduction records. The four shared ledgers are mutable observations, not immutable proof premises.

The accepted OpenAI pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. I read the actual symmetric inequality, finite-slab/soft-concavity proof, moment construction, adjunctions, dense-test proof, tensor calculation, and variance proof. These pinned operations are assumed true as directed; this is an audit of their new uses. The complete tree contains 13,223 entries and 749 manuscripts; all 9,340 ignored corpus files are enumerated with `rg --files --no-ignore` and rehashed against it.

For P10 the only nonclassical premise invoked is the accepted inequality/concavity. P10 does **not** invoke I45's new equality necessity theorem E. It constructs a comparison pair directly. I45's E,C,B,Q verdict and LSX attribution are preserved, but neither the external nonsymmetric theorem nor any quantitative consequence of E is assumed.

Actual primary reading includes [Xi v4, §3](https://arxiv.org/abs/2307.04266v4), the [van Handel planar generating-measure/Bochner argument](https://web.math.princeton.edu/~rvan/logzon221121.pdf), and all three planar proof steps of [Xi's September note v1](https://arxiv.org/abs/2609.08495v1). They establish relevant antecedents and context; the September note is not substituted for the proof under review. For construction A I checked the hypotheses and relevant proof passages of [Klartag, Theorem 1](https://www.math.tau.ac.il/~klartagb/papers/lc_moment.pdf), [Berman–Berndtsson, Theorem 1.1 and §§2.9, 2.12](https://afst.centre-mersenne.org/item/10.5802/afst.1386.pdf), and [Liu–Sun–Xiong v2, (3.10)–(3.16)](https://arxiv.org/abs/2610.10152v2). Credit for retaining the full derivative remainder and homogeneous square completion belongs to LSX. The fresh primary PDFs match the prior audited bytes. This is an analytic dependency check, not a renewed significance search.

## 2. Mixed area and the inclusion cap

### 2.1 Fourier normalization and signed functions

For a symmetric planar support function, antipodal evenness means \(\pi\)-periodicity, not reflection-evenness in the angular variable. Write

\[
f(\theta)=a_0+\sum_{k\ge1}(a_k\cos2k\theta+b_k\sin2k\theta).
\]

The support functions are Lipschitz and hence in \(H^1\). Their mixed area is

\[
V(f,g)=\tfrac12\int_0^{2\pi}(fg-f'g'),\qquad
V(f,f)=\pi a_0^2-\tfrac\pi2\sum_{k\ge1}(4k^2-1)(a_k^2+b_k^2).
\]

The formula holds for polygons by integration against the distributional curvature measure, and for general supports by smoothing or \(H^1\) approximation. It defines a bilinear form on all \(\pi\)-periodic \(H^1\) functions, including nonconvex signed functions.

Put \(h_A=a_0+u\), \(e=h_B-ah_A=b_0+v\), \(a=V(A,B)/|A|\). Orthogonality gives \(\pi a_0b_0=\langle u,v\rangle_*\). Therefore

\[
-V(e,e)\ge\left(1-\frac{\|u\|_*^2}{\pi a_0^2}\right)\|v\|_*^2
=\frac{|A|}{\pi a_0^2}\|v\|_*^2
\ge(r/R)^2\|v\|_*^2.
\]

Also \(\pi b_0^2\le\|v\|_*^2\), since \(|A|>0\). Cauchy–Schwarz in the Fourier series, using \(\sum_{k\ge1}(4k^2-1)^{-1}<\infty\), bounds \(\|v\|_\infty\le C\|v\|_*\). Thus

\[
d_H(B,aA)^2=\|e\|_\infty^2
\le C(r,R)\bigl[V(A,B)^2/|A|-|B|\bigr].
\]

For the later spectral use, precisely the same calculation applies to **any** signed \(g\in H^1\) with \(V(h_A,g)=0\). It gives \(V(g,g)<0\) unless \(g=0\). No claim that such a \(g\) is itself a support function is needed. In the distance application \(B\) is a convex body and \(a>0\), so \(aA\) is a legitimate comparison body.

### 2.2 The cap bound

If \(rB\subset A\subset B\subset R_1B\), choose a direction with support difference \(\eta=d_H(A,B)\) and a point \(x\in B\) with height \(H=h_B(u)=h_A(u)+\eta\le R_1\). The triangle joining \(x\) to the radius-\(r\) segment through zero perpendicular to \(u\) lies in \(B\). At depth \(z\) below \(x\) its section has length (2rz/H), regardless of the tangential coordinate of \(x\). The part at depths \(0<z<\eta\) is above \(A\)'s supporting line and has area

\[
\int_0^\eta 2rz/H\,dz=r\eta^2/H\ge r\eta^2/R_1.
\]

This proves I46 (4.3), including its uniformity and validity at nonsmooth points.

## 3. The paired sine operator and curvature

### 3.1 Reconstruction and invertibility

Take one unit normal \(u_i\) per true antipodal facet pair, and let \(s_i\) be the **sum** of the two edge lengths. Each actual edge has length \(s_i/2\). Since

\[
(\partial_\theta^2+1)|\sin(\theta-u_i)|=2\sum_{k\in\mathbb Z}\delta_{u_i+k\pi},
\]

the support reconstruction is \(h(\theta)=\frac14\sum_i s_i|\sin(\theta-u_i)|\). At each signed normal its curvature mass is \(s_i/2\), exactly as required. There is no nonzero \(\pi\)-periodic solution of \(f''+f=0\). Consequently the reconstruction has no translation ambiguity. Integrating \(h\) against its curvature gives \(|P|=\frac12\sum_i h_is_i\).

Let \(A_{ij}=|\sin(u_i-u_j)|/4\), so \(h=As\). This matrix is invertible for distinct projective normals of a full-dimensional polygon. Indeed, if \(Az=0\), the reconstructed signed function vanishes at every listed normal. Between successive projective normals it solves \(f''+f=0\); both endpoint values vanish and each gap is strictly between zero and \(\pi\). The interval solution is zero. Its derivative jumps then vanish, so every \(z_i=0\). This includes the two-direction case. Repeated antipodal representatives would invalidate this setup and are excluded by the definition of the list, not by a genericity assumption.

### 3.2 Reversibility and the strictly negative mean-zero spectrum

Write \(V=|P|\) and

\[
\nu_i=\frac{h_is_i}{2V},\quad T_{ij}=\frac{A_{ij}s_j}{h_i},\quad
\pi_{ij}=\nu_iT_{ij}=\frac{s_is_j|\sin(u_i-u_j)|}{8V}.
\]

These formulas give \(T1=1\), \(\sum\nu_i=1\), detailed balance, and hence invariance of \(\nu\) and its mean-zero subspace. Reversible Markov contraction bounds all eigenvalues in ([-1,1]).

For \(\langle y,1\rangle_\nu=0\), reconstruct \(g\) with signed paired masses \(s_i y_i\). Then \(g_i=h_i(Ty)_i\),

\[
V(h,g)=V\langle1,y\rangle_\nu=0,\qquad
V(g,g)=\tfrac12\sum_i g_is_iy_i=V\langle y,Ty\rangle_\nu.
\]

The strict signed Fourier result applies, and invertibility ensures \(g\ne0\) for \(y\ne0\). Thus the restriction of \(T\) has spectrum in ([-1,0)). In particular its inverse exists and preserves that subspace; no uniform lower bound on the absolute values of the eigenvalues is asserted or needed.

### 3.3 Every factor in the logarithmic Hessian

On an interval with fixed true facets, \(h_i'=b_i h_i\), \(h_i''=b_i^2h_i\), and \(y_i=s_i'/s_i\) satisfy \(Ty=b\). Since \(V=\frac12h^TA^{-1}h\),

\[
V'/V=2\langle b,1\rangle_\nu=2c,\qquad
V''/V=2\langle b,b\rangle_\nu+2\langle b,y\rangle_\nu.
\]

For \(q=b-c\), stationarity gives \(y=c+T^{-1}q\). Subtracting \((V'/V)^2\) yields exactly

\[
D=-(\log V)''=2\langle q,(-T^{-1}-I)q\rangle_\nu.
\]

At eigenvalue \(-a\), \(0<a\le1\), \(a^{-1}-1\ge1-a\). Therefore

\[
D\ge2\langle q,(I+T)q\rangle_\nu
=\sum_{i,j}\pi_{ij}(q_i+q_j)^2.
\]

The double sum counts both ordered orientations and is correct with this coefficient. For two normal directions \(T\) is the exchange matrix, \(\nu=(1/2,1/2)\), and the mean-zero eigenvalue is \(-1\). Both curvature and the sum form vanish, as they must for arbitrary independent parallelogram side dilations. Signed \(b,y,g\) cause no positivity issue.

## 4. The three-region argument with arbitrary mass clustering

Use projective distance \(d\in[0,\pi/2]\). Put \(M=\sum s_i\), \(\sigma=\sum(s_i/M)\delta_{u_i}\). Cauchy's perimeter formula and the ball bounds give \(2\pi r\le M\le2\pi R\). Moreover

\[
\frac{d\nu}{d\sigma}(u_i)=\frac{Mh_i}{2V}\asymp_{r,R}1,
\qquad \int|\sin(u-v)|\,d\sigma(v)=4h(u)/M\ge\kappa=2r/(\pi R).
\]

These are bounds for the whole measure, with no lower bound on any atom.

Partition the projective circle into half-open arcs of length at most (s/10), using at most (C/s) arcs. Half-open conventions allocate boundary atoms once. A largest arc \(A_1\) has mass \(m_1\ge cs\); select an actual atom \(a\in A_1\). If \(F=\{v:d(v,a)\ge\kappa/2\}\), the preceding integral is at most \(\kappa/2+\sigma(F)\), so \(\sigma(F)\ge\kappa/2\). One restricted arc \(A_2=F\cap I\) has mass \(m_2\ge c s\). Select an actual atom \(b\in A_2\). For sufficiently small \(s=s(r,R)\), all points of \(A_1,A_2\) are uniformly separated in projective distance. The cut at zero and a possible wrap around \(\pi\) do not change this metric argument.

Suppose mass outside the closed \(4s\)-neighborhoods of \(a,b\) exceeds \(s\). One restricted partition arc \(A_3\) in that set has \(m_3\ge cs^2\). Its distance from all of \(A_1,A_2\) is at least \(3s\). Thus kernels between \(A_3\) and those two sets are at least (c s), while the \(A_1,A_2\) kernel is at least a fixed positive constant.

For any real \(q\) on the finite normal set, let \(Q_i=m_i^{-1}\int_{A_i}q^2d\sigma\) and

\[
J=\iint|\sin(u-v)|(q(u)+q(v))^2d\sigma(u)d\sigma(v).
\]

For three independent samples from the normalized restrictions, use

\[
2q(u)=(q(u)+q(v))+(q(u)+q(w))-(q(v)+q(w)).
\]

Squaring and integrating bounds each \(Q_i\) by three normalized edge integrals. The worst denominator is \((cs)(cs)(cs^2)=cs^4\), namely the sine bound and two masses for a cross edge to \(A_3\). Thus all \(Q_i\le Cs^{-4}J\).

For any other \(u\), at least one of the distances to \(a,b\) is at least half their separation. Every point of the corresponding small arc then has sine distance at least a fixed positive constant. Choose \(A_1\) or \(A_2\) measurably, breaking ties in favor of the first. Averaging

\[
q(u)^2\le2(q(u)+q(v))^2+2q(v)^2
\]

over that arc and then integrating in \(u\) gives

\[
\|q\|_{L^2(\sigma)}^2\le C J/\min(m_1,m_2)+2(Q_1+Q_2)\le Cs^{-4}J.
\]

Comparability transfers this to \(\nu\). These operations use squared integrals only; they do not use a supremum bound on \(q\). Large values on arbitrarily small clusters are covered.

In the other case, assign mass in each neighborhood to its center and exceptional mass to \(a\). The neighborhoods are disjoint for small \(s\). The sine kernel is Lipschitz for projective distance, so the reconstructed two-segment support \(h_0\) differs from \(h_P\) by at most \(C M s\le Cs\). The exceptional mass contributes at most (Ms/4). The two-segment body has normals \(a,b\), and \(h_0\ge r/2\) once \(s\) is small. Their separation bounds the inverse of the coordinate map \(x\mapsto(a\cdot x,b\cdot x)\). Replacing its two supports by \(h_P(a),h_P(b)\) moves its vertices by at most \(Cs\). The resulting parallelogram \(Q\) contains \(P\), by the supporting-halfspace inequalities, and satisfies \(d_H(P,Q)\le Cs\).

The selected \(a,b\) are actual true facet normals of \(P\), not merely centers of a fitted shape. This distinction is what makes endpoint reconstruction below valid. Both alternatives of I46 §4.3 pass with facet-independent constants.

## 5. Full Wulff interpolation, active transitions, and time selection

For polygon endpoints, use the union of their **signed** facet normals. Between adjacent directions \(u,v\) of the union, any intermediate direction is \(w=\alpha u+\beta v\), with \(\alpha,\beta\ge0\). The union refines the two endpoint normal fans, so

\[
h_K(w)=\alpha h_K(u)+\beta h_K(v),\quad
h_L(w)=\alpha h_L(u)+\beta h_L(v).
\]

A point satisfying the union constraints at time \(t\) satisfies

\[
x\cdot w\le\alpha h_K(u)^{1-t}h_L(u)^t+\beta h_K(v)^{1-t}h_L(v)^t
\le h_K(w)^{1-t}h_L(w)^t
\]

by Hölder. Conversely the full Wulff body satisfies the union constraints. Thus this finite description is exact even if the endpoint fans differ.

For each independent pair of signed normals, its candidate vertex is linear in their exponential widths. Testing it against any listed constraint produces a finite real exponential sum. A nonzero sum has finitely many zeros, including on the closed time interval: dividing by its lowest exponential and applying Rolle inductively bounds the number of zeros by the number of remaining rates. Identically zero events are retained. Therefore feasibility and the true active list are fixed on finitely many open intervals. An inactive constraint may touch a vertex identically; it is not a true edge and is not included in the positive \(s_i\) list. On each interval the curvature calculation of §3 applies. No derivative through a fan transition is taken.

Concavity of \(F(t)=\log|P_t|\) follows from the accepted inequality: the logarithmic interpolation of \(P_s,P_t\) is contained in \(P_{(1-\theta)s+\theta t}\). Define \(g(t)=F(t)-\ell(t)\), where \(\ell(t)=(1-t)\log|K|+t\log|L|\). Then \(g\ge0\), \(g(0)=g(1)=0\), and \(g(\lambda)=\delta\). Concavity gives \(g(t)\le\delta/\tau\): compare \(\lambda\) to the chord from \(t\) to the appropriate endpoint. At differentiable \(t\in[1/4,3/4]\), the two endpoint secants give \(|g'(t)|\le4\delta/\tau\).

For the nonnegative distributional curvature measure \(\mu=-g''\),

\[
\delta=\int_0^1G_\lambda(t)\,d\mu(t),\quad
G_\lambda(t)=\min\{(1-\lambda)t,\lambda(1-t)\}.
\]

The kernel is at least \(\tau/3\) on ([1/3,2/3]). The absolutely continuous part has density (D(t)) on the smooth intervals. Singular curvature, if present at events, is nonnegative and can be dropped in the upper bound for \(\int D\). Thus there is a nonexceptional \(t\in[1/3,2/3]\) with \(D(t)\le C_\tau\delta\). The estimates on (g,g') hold at this same time.

All \(P_t\) lie between \(rB,RB\). At every current true facet, its defining union constraint is active, so

\[
h_P(u_i)=h_K(u_i)^{1-t}h_L(u_i)^t,
\quad b_i=\log(h_L(u_i)/h_K(u_i)),\quad |b_i|\le\log(R/r).
\]

This remains true when \(u_i\) is a facet of only one endpoint. The support of the other endpoint at \(u_i\) is its actual support value. The proof never substitutes its nearby facet width. Finally

\[
2c=\ell'+g',\qquad
\log(|K|/|P|)+2tc=-g+tg',\qquad
\log(|L|/|P|)-2(1-t)c=-g-(1-t)g'.
\]

These identities retain the possibly nonzero endpoint log-volume slope.

## 6. Endpoint reconstruction and the power

### 6.1 The small-variance alternative

The relation \(\pi_{ij}=M^2\sigma_i\sigma_j|\sin(u_i-u_j)|/(8V)\) and the bounds on \(M,V\) show \(J(q)\le CD\). Taking \(q=b-c\), §4 gives \(v=\operatorname{Var}_\nu b\le C\delta s^{-4}\).

The mixed-area formula uses only the current surface-area normals of \(P\), so

\[
a_K:=V(P,K)/V=E_\nu e^{-tb}
=e^{-tc}E_\nu e^{-tq}.
\]

Here \(q\) is uniformly bounded, because it is the centered endpoint log-support ratio. Taylor's formula, \(E q=0\), and the bounded interval for \(q\) imply \(E e^{-tq}\le1+C v\). This boundedness is used **here**, not in the general three-region inequality. Also \(v\le C(r,R)\). Combining with the exact identity above,

\[
\frac{V(P,K)^2}{V}-|K|
=Ve^{-2tc}\left[(E e^{-tq})^2-e^{-g+tg'}\right]
\le C(v+\delta).
\]

The left side is nonnegative by the mixed-area form already proved. For \(L\) the same calculation uses \(E e^{(1-t)q}\) and \(e^{-g-(1-t)g'}\). The coefficients \(a_K,a_L\) are positive and lie between (r/R) and (R/r), since they average the respective support ratios. Applying §2.1 to both endpoints gives

\[
\max\{d_H(K,a_KP),d_H(L,a_LP)\}\le C\sqrt{\delta+\delta s^{-4}}.
\]

The pair \((a_KP,a_LP)\) is a member of the one-block part of \(\mathcal E\). This calculation pays the proportionality constants and the endpoint area terms explicitly.

### 6.2 The two-normal alternative

Use the actual selected normals \(a,b\), and let \(Q_0,Q_1\) be the two-slab bodies with endpoint widths \(h_K(a),h_K(b)\) and \(h_L(a),h_L(b)\). They contain \(K,L\). Their angle separation and bounded widths give an outer radius \(R_1(r,R)\). At the selected time their logarithmic width interpolation is exactly \(Q\), because both normals are active for \(P\).

In the coordinates \(x\mapsto(a\cdot x,b\cdot x)\), a two-slab body's area is \(4AB/|\det(a,b)|\). Consequently

\[
\log|Q|=(1-t)\log|Q_0|+t\log|Q_1|.
\]

The inclusion \(Q\subset P+CsB\subset(1+Cs/r)P\) yields \(\log(|Q|/|P|)\le Cs\). Hence

\[
(1-t)\log(|Q_0|/|K|)+t\log(|Q_1|/|L|)
=g(t)+\log(|Q|/|P|)\le C(\delta+s).
\]

Both logarithms are nonnegative. Since \(t,1-t\ge1/3\), each is at most \(C(\delta+s)\). Common outer bounds turn this into an area excess bound of the same order, and §2.2 gives

\[
\max\{d_H(K,Q_0),d_H(L,Q_1)\}\le C\sqrt{\delta+s}.
\]

The inverse coordinate map sends the two coordinate axes to common complementary edge subspaces. Thus \(Q_0,Q_1\) belong to the required class, including oblique configurations. They are allowed to extend outside \(RB\); imposing the original ball bounds on them would change the theorem and is not done.

### 6.3 Balancing, zero deficit, and approximation

For small positive \(\delta\), set \(s=\delta^{1/5}\). Both branches give \(d_{\mathcal E}\le C\delta^{1/10}\). The allowed threshold \(s_0\), and hence the small-deficit threshold, depend only on \(r,R,\tau\). For larger \(\delta\), the fixed equality pair ((rB,rB)) gives a uniformly bounded distance, so reducing the theorem's constant handles the remaining range.

If \(\delta=0\), use any positive auxiliary upper bound \(\eta\) in the same estimates and choose \(s=\eta^{1/5}\). Concavity makes \(g=0\), and the smooth-interval curvature is zero. Letting \(\eta\downarrow0\) gives \(d_{\mathcal E}=0\), which is all the inequality requires. Closedness of the comparison class is not assumed.

Approximate \(K,L\) by symmetric polygons in Hausdorff distance. Eventually the bounds are ((r/2)B,(2R)B), common to all approximants. Positive supports converge uniformly, uniformly also in their logarithmic interpolations. If two bounds satisfy \(e^{-\eta}f\le f_j\le e^\eta f\), the corresponding Wulff bodies satisfy \(e^{-\eta}\mathcal W[f]\subset\mathcal W[f_j]\subset e^\eta\mathcal W[f]\). Thus their areas and deficits converge. Distance to any fixed subset of the pair metric is 1-Lipschitz. The facet-independent polygon bound therefore passes to arbitrary bodies with the same exponent.

Scaling offers a useful check on the constants: after normalizing \(r=1\), the conclusion can be written \(\Delta\ge c(R/r,\tau)(d_{\mathcal E}/r)^{10}\). The log deficit is dimensionless and the Euclidean distance rescales linearly. There is no hidden scale-invariant claim for a dimensional constant.

This completes the full P10 audit.

## 7. Separate audit of construction A

### 7.1 Homogeneity, the Gamma factor, and finite-soft-defect selection

For the finite hard slab body \(P\), \(U_q\le N\) on \(P\), while \(U_q\le1\) implies every slab constraint. Homogeneity gives exactly \(N^{-1/q}P\subset B_q\subset P\). Layer integration gives

\[
\int e^{-U_q}dx=\Gamma(1+n/q)|B_q|,
\quad
\int |x|^2e^{-U_q}dx=\Gamma(1+(n+2)/q)\int_{B_q}|x|^2dx.
\]

Thus the normalized second moment is bounded by \(C_nR^2\): the ratio of Gamma factors is bounded for \(q\ge2\), and \(B_q\subset RB\). Jensen gives

\[
-\epsilon E_{q,0}|x|^2/2\le\log(Z_{q,\epsilon}/Z_{q,0})\le0.
\]

The volume inclusions cost \(n\log N/q\), and \(\log\Gamma(1+n/q)=O_n(1/q)\). This proves I46 (3.2), with no minimum facet mass or irredundancy requirement.

The stated direction-net error is also uniform. For mesh \(a\), the finite constraints first bound the outer radius by (R/(1-a)). The functions \(h_K^{1-t}h_L^t\) have a common Lipschitz bound under \(r,R\). Testing a nearest sampled direction therefore gives all-direction bounds with additive error \(Ca\); positivity converts this to multiplicative Wulff inclusions and (O(a)) Hausdorff and log-volume error. An \(a\)-net with \(N\le C_na^{-(n-1)}\) suffices.

For the small-deficit regime, choose \(epsilon=\delta\), direction error at most \(\delta\), and even \(q\ge C(1+\log N)/\delta\). If \(G=\log Z_{q,\epsilon}\) and \(\ell\) is the true endpoint log-volume chord, then

\[
|G-\ell|\le C\delta
\]

uniformly, by the hard deficit's concavity bounds and the approximation estimate. Secants for the smooth concave \(G-\ell\) bound its derivative by \(C\delta\) on a fixed interior interval. Integrating (-G'') and selecting a time gives \(D=-G''\le C\delta\). This does **not** imply \(G'=O(\delta)\): it implies \(G'=\ell'+O(\delta)\).

For \(F=-q\sum b_i\psi_i\), differentiation gives \(EF=-G'\). The centered score is \(U=F-EF\). In the symmetric case its linear projection vanishes by parity, but its constant projection need not vanish. I44/I45's exact LSX-attributed completion, read again in the primary, gives

\[
T(v)+\epsilon E|W|^2\le D+\|u-U\|_2^2,
\qquad \tfrac12E\mathscr D(P)\le T(v).
\]

Choose the dense-test error at most \(\delta\) at each fixed parameter. This gives \(T(v),E\mathscr D(P)\le C\delta\) and \(E|W|^2\le C\). No uniform inverse for the dense range is involved. These are finite-soft-field estimates, not already hard-field estimates.

### 7.2 Hard-target coordinate bounds

For \(d\mu=Z^{-1}1_Ce^{-\epsilon|x|^2/2}dx\), \(rB\subset C\subset RB\), \(0\le\epsilon\le1\), the density is positive and smooth on the interior, with bounded derivatives on \(C\), and has barycenter zero. Berman–Berndtsson gives a smooth entire moment potential with gradient image \(\operatorname{int}C\). Translating its minimum to zero makes it even by uniqueness. Its source density is probability-normalized.

Klartag's actual Theorem 1 assumes bounded convex support and smooth bounded target log-density, not smoothness of the boundary. Its proof first obtains the covariance estimate for smooth strictly convex targets, then removes those extra assumptions by approximation and integrated Laplacian bounds. It applies here and gives \(0<\tau=D^2\varphi\le2R^2I\). Also \(|\nabla\varphi|\le R\).

Here is the uniform coercivity argument. The preimages of the slopes \(\pm(r/2)e_i\) give some preliminary linear lower bound, enough to justify expanding cutoffs. Thus \(E_\nu[z\cdot\nabla\varphi]=n\). For \(g=\varphi-\varphi(0)\ge0\), the supporting planes at (z,-z) give

\[
g(y)\ge g(z)+|\nabla\varphi(z)\cdot y|-z\cdot\nabla\varphi(z).
\]

Integrate and drop \(E g(z)\ge0\). The target density is bounded below on \(rB\) by a constant depending only on \(n,r,R\), so \(g(y)\ge c|y|-n\). Conversely \(g(y)\le R|y|\). The identity \(e^{\varphi(0)}=\int e^{-g}\) now bounds \(\varphi(0)\) on both sides uniformly. This proves (3.4) and the exponential tail in (3.5).

The moment equation is

\[
\det\tau=Z\exp(-\varphi+\epsilon|\nabla\varphi|^2/2).
\]

On \(B_L\), \(\varphi\le C+RL\) and \(Z\ge c>0\). Thus \(\det\tau\ge c e^{-RL}\). Dividing by the upper bound \((2R^2)^{n-1}\) for the product of the other eigenvalues gives \(\tau\ge c e^{-RL}I\), while \(e^{-\varphi}\ge c e^{-RL}\). These are hard-target bounds. Using them directly for finite-\(q\) soft targets would not be justified, and I46 expressly does not do that.

### 7.3 What the conditional field and clustering estimates actually prove

Assume hard fields with \(W=P\nabla\varphi-\operatorname{div}_zP\), \(P\tau=\tau P^T\), \(E|W|^2\le C\), and \(E\mathscr D(P)\le C\delta\) have been obtained. The invariant derivative norm is bounded below by \(\lambda_{\min}(\tau)\lambda_{\max}(\tau)^{-2}|D_zP|^2\). Combining this with the lower source density gives

\[
\int_{B_L}|D_zP|^2dz\le Ce^{2RL}\delta.
\]

Let \(A\) be the Lebesgue average of \(P\) on \(B_1\). Poincaré and the formula for \(W\) give \(\|P-A\|_2+\|W-A\nabla\varphi\|_2\le C\sqrt\delta\) there. The gradient covariance is uniformly nondegenerate: the lower Hessian bound on \(B_1\) makes \(\nabla\varphi(B_1)\) contain a fixed ball, and the upper determinant bound permits a change of variables bounding \(\int_{B_1}\nabla\varphi\nabla\varphi^Tdz\) below. Hence \(|A|\le C\). Poincaré on \(B_L\) and comparison of its average with the \(B_1\) average give, for \(L\ge1\),

\[
\|P-A\|_{L^2(B_L)}+\|W-A\nabla\varphi\|_{L^2(B_L)}
\le C(1+L)^{n/2+1}e^{RL}\sqrt\delta.
\]

This is the claimed budget, under precisely the stated field hypothesis.

Set \(H=\fint_{B_1}\tau\). Its condition number is uniformly bounded. From the exact field symmetry,

\[
\|A\tau-\tau A^T\|_{L^2(B_L)}\le C\|P-A\|_{L^2(B_L)}.
\]

In particular \(AH-HA^T=O(\sqrt\delta)\). Thus \(B=H^{-1/2}AH^{1/2}\) is within \(O(\sqrt\delta)\) of its symmetric part. This constant transformation keeps the Hessian cap controlled. Replacing \(B\) by its symmetric part adds at most \(C L^{n/2}\sqrt\delta\) to the core commutator norm, absorbed by the displayed budget. Diagonalize that symmetric matrix and merge consecutive eigenvalues with gaps less than \(\gamma\). A cluster has diameter at most \((n-1)\gamma\), and eigenvalues in distinct clusters differ by at least \(\gamma\). Entrywise, the commutator is \((\lambda_i-\lambda_j)\tau_{ij}\); therefore the mixed blocks between clusters have norm at most \(\gamma^{-1}\) times the commutator error. Repeated eigenvalues and a single cluster cause no difficulty.

For \(0\le a\le r\), \((1-a/r)C+aB\subset C\), so the boundary layer has relative volume at most (na/r). Gaussian weights on \(C\) are uniformly comparable to volume; Cauchy–Schwarz then gives an \(O(\sqrt a)\|\nabla g\|_\infty\) boundary-layer flux error. This estimates position tests only.

The conditional boundary identity must keep both terms in I46 (3.9):

\[
\int_C W\cdot\nabla g\,d\mu
=-Z^{-1}\int_{\partial C}g\,b(\nu)h_C(\nu)e^{-\epsilon|x|^2/2}dS
-(EF)\int_Cg\,d\mu.
\]

For \(W=Ax\), integration by parts has bulk coefficient \(-\operatorname{tr}A+\epsilon x\cdot Ax\). Dropping either this Gaussian contribution or \(EF\approx-\ell'\) is incorrect. No such deletion occurs in I46.

These verifications audit more than the gap statement: they prove the stated conditional budgets and their constants. They do **not** construct the fields satisfying those hypotheses at finite deficit. Nor does a small mixed Hessian on \(B_L\) by itself produce a single nearby product gradient image, or identify compatible endpoint factor dilations. The normal map of a nonsmooth convex body need not have uniformly controlled Lipschitz behavior, so the position-test estimate cannot silently be used as a cone-volume normal-test estimate. I46 identifies all these unpaid steps explicitly. They remain unpaid after this review.

## 8. Evidence and independent diagnostics

The independent `check.py` starts from actual rational zonotope generators, enumerates their signed endpoint sums, takes exact convex hulls, and computes shoelace area and exposed edge lengths. It then reconstructs the support-area quadratic from intersections of consecutive facet lines. Thus its curvature check is not merely a substitution into the author's operator formula. Fifteen configurations include oblique rotations, clustered normals, and paired masses as small as \(10^{-8}\); signed test slopes reach \(10^9\). The two-direction zero-curvature case is checked separately.

Further exact cases cover a constraint true at both endpoints but inactive on an open middle interval, a union normal true at only one endpoint, full midpoint constraints in sampled directions, oblique parallelogram area affinity, the unrestricted three-number square estimate, cap geometry, homogeneous Gamma factors, nonzero score centering, matrix symmetrization, the cubic-family expansion, and the exponent balance. The diagnostic passes **1,049 exact assertions**. These finite tests do not prove arbitrary clustering, compactness, or any universal rate; §§2–7 supply the analytic verification.

The unchanged I46 verifier reproduces its 161-artifact seal, 18 frozen inputs, 12 selected pins, 21 fresh responses (20 successful and one retained failure), 27 inherited response bindings, 23 read records, 3,319 exact assertions, 16 polygon configurations, three corpus searches, and all 9,340 corpus files. The I43/I44/I45 seals remain unchanged at 125/245/495 artifacts. Its four mutable shared-ledger drifts are reported separately, not repaired or refreshed.

I47 freezes **1,043 inputs**, retains 12 successful fresh primary/raw responses, and binds the current version records and exact passage extracts. Its own verifier checks the precise sealed artifact set, every frozen input, immutable live dependencies, fresh-response and passage hashes, selected Git blobs, and the complete pinned corpus. It replays both independent diagnostics and the original I46 verifier read-only, with bytecode disabled. Later edits to the four shared ledgers or the I47 orchestration record are reported as mutable drift; they do not invalidate frozen proof bytes.

Run from the repository root:

```sh
python frontier/experiments/i47_planar_logarithmic_stability_r2/check.py
python frontier/experiments/i47_planar_logarithmic_stability_r2/verify.py
```

The analytic verdict is **P10 PASS ORIGINAL WITHOUT REPAIRS**, with construction A passing only its stated partial and conditional claims. Q remains an obstruction to exponents below three on classes containing that family, not a positive cubic estimate. The higher-dimensional target and all significance/acceptance decisions are outside this verdict.
