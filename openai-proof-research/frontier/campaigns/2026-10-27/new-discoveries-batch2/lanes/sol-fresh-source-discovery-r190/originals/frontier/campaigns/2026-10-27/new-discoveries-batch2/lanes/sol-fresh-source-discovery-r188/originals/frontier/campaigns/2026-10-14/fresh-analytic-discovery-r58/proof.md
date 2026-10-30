# T337E: sharp filling equality in a proper CAT(0) space

Myeongjin Kang. No affiliation. Original prose CC BY 4.0.

Author proof, assembled after the exact scope freeze in `original-scope.txt`. This is not an independent review or an acceptance. Source results at the recorded immutable pin are stipulated. The classical inputs and actual reading limits are identified separately. In particular, the higher-dimensional threshold argument and the final density-one rigidity theorem are credited operations. The candidate additional mechanism is the scalar-normal contraction and current-degree certificate in cycle dimension two.

## 1. Statement and compact reduction

Let n≥2, let X be proper CAT(0), and let T≠0 be a compactly supported integral n-cycle. Integral currents have finite mass and finite boundary mass. Put

\[
 V_X(T)=\inf_{\partial S=T}\mathbf M(S),\qquad
 s_n=(n+1)\omega_{n+1},\qquad
 c_n=\frac1{(n+1)s_n^{1/n}}.
\]

The infimum allows all finite-mass integral fillings, without a compact-support condition. We prove

\[
 V_X(T)=c_n\mathbf M(T)^{(n+1)/n}
\]

if and only if T is the oriented boundary, with multiplicity one, of an isometrically embedded closed Euclidean (n+1)-ball. Its radius is (M(T)/s_n)^(1/n).

Take a closed metric ball Y in X containing spt T. It is convex, compact and CAT(0). Its nearest-point projection is 1-Lipschitz, fixes T, and takes any admissible finite-mass filling to an admissible compactly supported filling. Thus V_Y(T)=V_X(T). Compact current compactness and lower semicontinuity give a minimizer in Y (equivalently use source02, `thm:current-background`). A minimizer there is also a global minimizer in X. Throughout the forward proof we may therefore work in Y; all resulting isometric balls are also isometric in X.

Rescale distances by R^−1, R=(M(T)/s_n)^(1/n), and write A for the rescaled cycle, μ=||A|| and m=s_n. Equality says V(A)=ω_(n+1). For every integral n-cycle B in Y, the pinned sharp filling theorem and filling subadditivity imply

\[
 c_n\bigl(m^q-\mathbf M(B)^q\bigr)\le V(A-B),
 \qquad q=(n+1)/n.                                      \tag{1}
\]

Indeed V(A)≤V(B)+V(A−B), and V(B)≤c_n M(B)^q. The normalization is c_n q m^(1/n)=1/n. This is exactly the normalized extremizer inequality used in source02–03. Its derivation here does not require the strict mass inequality used in the source's contradiction construction.

## 2. Source radial contract at equality

The deformation and swept-current proof of source03, Proposition `prop:radial`, uses (1) and the displayed normalization. It therefore gives, for every y∈Y and every nonnegative Lipschitz g on Y, with r=d(y,·),

\[
 \int (ng+r\,Dr\mathbin\cdot Dg)\,d\mu
 \le n\int rg\sqrt{1-|Dr|^2}\,d\mu.                    \tag{2}
\]

Here derivatives are the scalar chart derivatives in the Euclidean approximate tangent metric of A. Source02 `prop:chart-mass`, `lem:euclidean-density` and `eq:gradient-lipschitz` supply the exact mass formula, integer lower density and |Dr|≤1. They apply with arbitrary signed integer chart multiplicities. We do not assume separate chart restrictions are normal currents.

In particular, g=1 and Cauchy–Schwarz give, for every y,

\[
 \int d(y,x)^2\,d\mu(x)\ge m.                          \tag{3}
\]

## 3. Cycle dimensions n>2: the source threshold closes the radius

Set β=1/(n−2), p=2n/(n−2), S_*=n s_n^(2/n), and use the closed gradient form E constructed in source05. Define

\[
 \Lambda=\inf_{u\ne0}
 \frac{4\beta E(u)+n\|u\|_2^2}{\|u\|_p^2}.
\]

The constant test gives Λ≤S_*. The small-set isoperimetry and almost-sharp Sobolev estimates in source04 use (1), the normalization and the sharp lower-dimensional theorem; they do not use m<s_n. The gradient closure, compact L² embedding and subthreshold concentration argument in source05 consequently apply here. If Λ<S_*, that argument produces its normalized nonnegative minimizer v, with

\[
 W=\int v^p\,d\mu=(\Lambda/n)^{n/2}<s_n.
\]

For the probability measure ν=v^p μ/W, source06 then gives its chord upper bound, and source07 gives its opposite weighted average; these contradict W<s_n. Consequently Λ=S_*, and the constant function 1 is an actual minimizer.

Apply the source06 chord argument to this minimizer v=1. Its scalar comparison and estimates through the penultimate chord bound remain valid at W=s_n; the strict W<s_n is used only to replace the final upper bound by a strict inequality. At equality they give

\[
 I(y):=\int d(y,x)^2\,d\mu(x)\le2m
 \quad\text{for μ-almost every }y.                    \tag{4}
\]

Let o be the CAT(0) barycenter of μ/m. The barycenter variance inequality, integrated against μ, gives

\[
 \int I(y)\,d\mu(y)\ge2m I(o).
\]

Combining this with (3) and (4) yields I(o)=m. Formula (2), with y=o and g=1, now gives the equality chain

\[
 m\le\int r\sqrt{1-|Dr|^2}\,d\mu
   \le\int r\,d\mu\le\sqrt{m I(o)}=m.
\]

The equality condition in Cauchy–Schwarz forces r=1 μ-almost everywhere, and hence spt A lies on the sphere of radius one about o.

Let S be the cone from o over A. The usual CAT(0) cone mass bound gives M(S)≤m/(n+1)=ω_(n+1), so S is a global minimum filling. We verify that o belongs to its support. For 0≤a<b≤1 the same cone parametrization, restricted to parameters a<t<b, gives

\[
 \mathbf M\bigl(S\llcorner\{a<d(o,\cdot)<b\}\bigr)
 \le m\int_a^b t^n\,dt.
\]

The cone has no mass on a fixed parameter sphere, by its product parametrization and the exact radial identity d(o,c_t(x))=t. Since the total mass saturates the bound, each inner ball has mass ω_(n+1)b^(n+1). In particular o∈spt S. Its distance from boundary support is one. Stadler's classical density-one rigidity (Proposition A.1, stated below) gives the Euclidean unit ball with multiplicity one. All mass of S is in that ball, so A is its oriented boundary.

This section is a threshold use of the stipulated source estimates, not a separate substantial claim.

## 4. Cycle dimension two: scalar equality and unit density

Now m=4π. Fix any pole y satisfying the source's almost-everywhere integer lower-density conclusion. For eligible ε↓0 with μ{r=ε}=0, use g=max(r,ε)^−2 in (2), exactly as source03 `eq:base-cutoff-estimate`. With

\[
 b(x)=r(x)^{-1}\sqrt{1-|Dr(x)|^2},\qquad r(x)>0,
\]

retaining the completed square gives

\[
 (2-2\varepsilon)\varepsilon^{-2}\mu(B(y,\varepsilon))
 +2\int_{r>\varepsilon}(b-\tfrac12)^2\,d\mu
 \le m/2.                                               \tag{5}
\]

The integer lower density is at least π. Thus the first term tends to 2π and the nonnegative integral tends to zero. First this holds on eligible radii; monotonicity of ball masses extends the density limit to all radii, by approximating any radius from above and below by eligible radii with relative error tending to zero. Consequently

\[
 \lim_{\rho\downarrow0}\rho^{-2}\mu(B(y,\rho))=\pi,
 \qquad
 |D_xd_y|^2=1-d(x,y)^2/4
 \quad\text{for μ-almost every }x\ne y.                 \tag{6}
\]

Fubini applies to the chartwise measurable derivatives (difference-quotient versions suffice). Choose x for which (6) holds for μ-almost every y and which is a regular oriented chart point with density one, metric differential and CAT(0) geodesic-cone differential. Such points have full μ-measure by chart rectifiability, scalar differentiation and Lytchak's Rademacher theorem. In coordinates we take x=φ(0), metric differential the Euclidean norm, and signed multiplicity σ=±1 at its Lebesgue point. The selected chart itself has density π at x. The total density π in (6) therefore also implies

\[
 \mu(B(x,\rho)\setminus\phi(D))=o(\rho^2).              \tag{7}
\]

The other chart contributions are nonnegative; this deduction does not require geometric regularity of the whole support.

## 5. A geometric certificate in the tangent cone

Let C=C_xY be the completed geodesic tangent cone. It is complete CAT(0), and log_x:Y→C is 1-Lipschitz with |log_x y|=d(x,y). The differential of φ identifies its Euclidean tangent plane with a flat E≅R² through the cone vertex. Lytchak Theorem 1.6 supplies this differentiation into the actual geodesic cone, so log_x(φ(z))=z+o(|z|) in C along the chart, after identifying E. More explicitly, the strong differential has the same image in every rescaled ultralimit under the natural isometric embedding of the geodesic cone (Lytchak §7.7). The rescaled logarithms are contractions and fix this embedded cone, so their compositions with the chart converge to the differential along every rescaling sequence. If the displayed o(|z|) assertion failed, a failing sequence and a convergent subsequence of its normalized Euclidean directions would contradict that blowup identity. The chart's two-point metric differential, and the isometric cone embedding in these blowups, make the differential an isometric embedding. We give the scalar derivative identification directly below, rather than assume a first-variation chain rule. No local geodesic completeness or local compactness of C is required.

For a y satisfying (6), put v=log_x y and r=|v|. If ℓ=D_x d_y is viewed as a linear functional on E, distance contraction and the cone cosine law imply, for all z∈E,

\[
 d_C(v,z)^2=r^2+|z|^2+2r\ell(z)
             =|z-w|^2+h^2,\quad w=-r\ell^{\sharp}.
                                                               \tag{8}
\]

Here is the exact argument. For a unit e∈E set a_±=⟨v,±e⟩_C, using the cone cosine inner product. The two Busemann functions of the line te take values −a_+ and −a_− at v. Their sum is nonnegative by the triangle inequality, so a_++a_−≤0. Contraction of log_x gives d(y,φ(z))≥d_C(v,log_xφ(z)). Approach zero in the density-one chart domain with z/t→e and z/t→−e, respectively. Expanding the cone distance yields ℓ(e)≥−a_+/r and −ℓ(e)≥−a_−/r. Adding gives a_++a_−≥0. Hence equality holds throughout, ℓ(e)=−a_+/r, and homogeneity proves (8). Density one guarantees the required directional sequences; all errors are o(t). From (6),

\[
 |w|^2=r^2-r^4/4,\qquad h=r^2/2.                       \tag{9}
\]

We need the following elementary consequence of the classical parallel-set theorem.

**Parallel-set lemma.** If E is a finite-dimensional flat in a complete CAT(0) space C and a point v satisfies d(v,z)^2=|z−w|²+h² for every z∈E, then v lies in P(E). Under its splitting P(E)=E×N with E=E×{n₀}, its coordinates are (w,n) with d_N(n,n₀)=h.

To prove this, first take a line L⊂E. The displayed distance identity computes the two Busemann functions of L at v and gives b_+(v)+b_−(v)=0. Globally b_++b_−≥0 by the triangle inequality against the two far endpoints of L. In a complete CAT(0) space a ray asymptotic to either end of L starts from every point. Along the positive ray from v, b_+ decreases exactly at unit speed, while b_− increases by at most that speed. Nonnegativity of the sum forces exact increase. The analogous assertion holds on the negative ray. The 1-Lipschitz function b_+ now certifies distance s+t between points at parameters s,t on the two rays. Their concatenation is a line through v parallel to L. The flat-strip and parallel-set splitting theorem gives v∈P(L)=R×C₁. The flat E splits there as R×E₁. Subtracting the first Euclidean coordinate from the distance identity gives the same identity for the projection of v and E₁. Iterate over an orthonormal basis of E. This proves the assertion and the coordinates. Asymptotic-ray existence, flat strips and parallel-set splitting hold for complete CAT(0) spaces, without properness. The parent supplied this Busemann proof as author assistance.

Apply the lemma to (8). On all of Y define

\[
 f:Y\xrightarrow{\log_x}C
   \xrightarrow{\operatorname{proj}_{P(E)}}E\times N
   \xrightarrow{(w,n)\mapsto(w,d_N(n,n_0))}\mathbb R^3.
                                                               \tag{10}
\]

Each map is 1-Lipschitz. For μ-almost every y, (9) implies

\[
 f(y)=(w,r^2/2),\qquad |f(y)-(0,0,1)|=1,
 \qquad |f(y)|=r.                                      \tag{11}
\]

Continuity extends (11) to spt A; also f(x)=0. Thus f maps the whole cycle support into the unit sphere Σ centered at c=(0,0,1), and **preserves distance from x on that support**. Its chart differential at x is the identity E→E×{0}: log_x has chart differential E, the projection fixes E, and the normal distance coordinate is o(|z|). Equivalently,

\[
 f(\phi(z))=(z,0)+o(|z|)\quad(z\to0,\ z\in D).         \tag{12}
\]

## 6. No cancellation: the spherical pushforward has degree one

The integral cycle f#A is supported in the connected smooth sphere Σ. The constancy theorem gives f#A=k[[Σ]] for an integer k. We prove |k|=1, rather than deducing this merely from a pointwise Jacobian.

Fix a compactly supported test two-form in R³ whose support is in B_R(0), and rescale the target by ρ^−1. By (11), every contributing point of spt A lies in B_(Rρ)(x). Its part outside the selected chart has mass o(ρ²) by (7), and after pushing and rescaling contributes o(1). Within the chart, bi-Lipschitzness bounds the relevant domain by |z|≤C Rρ. The signed chart weight θ satisfies

\[
 \theta(\rho z)1_D(\rho z)\longrightarrow\sigma
 \quad\text{in }L^1(B_{CR})
\]

at its density-one Lebesgue point. Define F_ρ(z)=ρ^−1 f(φ(ρz)) on D/ρ. These maps have a common Lipschitz bound, and (12) gives uniform convergence to (z,0) on every bounded part of their domains. Extend their three coordinates by McShane to a fixed disk B_(CR), with a common Lipschitz bound. Since D has density one at zero, its rescaled complement has vanishing measure and its largest empty ball in a fixed smaller disk has radius tending to zero. The extensions therefore converge uniformly there to (z,0). One may take a larger fixed disk initially to avoid its outer boundary.

Replacing θ(ρz)1_D(ρz) by σ changes the pushed two-current by mass at most a fixed squared Lipschitz constant times the displayed L¹ error. The pushforwards of the fixed integration current σ[[B_(CR)]] converge weakly to its pushforward under z↦(z,0): uniform convergence with a common Lipschitz bound on a fixed normal current has this standard continuity property (alternatively use the straight homotopy formula in R³). Tests supported in B_R see no outer boundary of the chosen larger disk. Hence the local blowup of f#A at 0 is the plane with coefficient σ, up to the choice of its orientation.

The blowup of k[[Σ]] at 0 is the same tangent plane with coefficient k, with the corresponding spherical orientation. Therefore |k|=1. Notice exactly where remote sheets were excluded: (11) gives f^−1(B_(Rρ)(0))∩spt A=B_(Rρ)(x)∩spt A. A nonzero approximate differential by itself would not have sufficed.

## 7. A filling supplies the interior point

Let S be a compact minimum filling of A in Y. Its mass is ω₃=4π/3. By Section 6, ∂(f#S)=±[[Σ]]. Top-dimensional constancy in R³ gives

\[
 f_\#S=\pm[[B_1(c)]].                                  \tag{13}
\]

To see the normalization without any ambient-support assumption, subtract the indicated ball current: the difference is a compactly supported integral three-cycle in R³ and is zero by constancy. Since f(spt S) is compact and contains spt(f#S), some p∈spt S satisfies f(p)=c. Formula (11) and the Lipschitz bound give

\[
 d(p,\operatorname{spt}A)\ge1.                          \tag{14}
\]

Now invoke Stadler, arXiv:2212.07100v1, Proposition A.1: for a compact area-minimizing integral k-current in a locally compact CAT(0) space, at an interior point of its support the mass ratio M(S⌞B(p,r))/r^k is at least ω_k and is nondecreasing up to boundary distance; equality at a radius no greater than that distance makes the supported closed ball an isometric Euclidean ball of multiplicity one. The full proposition and proof were read; the author describes this rigidity as folklore.

Here the total mass is ω₃, while (14) and monotonicity force M(S⌞B(p,1))≥ω₃. Equality holds. The proposition yields a Euclidean unit ball of multiplicity one. There is no remaining mass outside it, so S is its integration current up to orientation, and A=∂S is its round boundary. This proves the endpoint case.

## 8. Converse and scale restoration

An isometric image K of a closed Euclidean ball in a CAT(0) space is convex: the image of each Euclidean segment is the unique ambient segment. Its nearest projection is 1-Lipschitz. If T is its oriented boundary and S is any finite-mass integral filling in X, projection to K gives a filling there. Identify K with its Euclidean model and include it in R^(n+1). Top-dimensional constancy forces this projected filling to be the ball current, so M(S)≥ω_(n+1)R^(n+1). The ball itself attains this value. This proves equality even for the infimum over noncompact finite-mass fillings. Scaling back from M(A)=s_n proves the statement with the radius in Section 1.

## 9. Dependencies and author limits

The full proof uses the stipulated sharp filling theorem and its actual radial/Sobolev/chord operations, ordinary CAT(0) tangent/parallel-set geometry, standard integral-current constancy and pushforward continuity, Lytchak differentiation into a geodesic cone, and Stadler's density-one rigidity. The scalar normal distance in (10) replaces any unavailable signed normal field; it does not assert smoothness of the original current or alignment of transverse directions. The dimension-two degree and filling certificate are the proposed additional assembly. Whether this exceeds a technical equality transfer is reserved for separate contribution assessment.

Parent author assistance: the Busemann proof in Section 5 and the suggestion to exploit exact radial preservation in Section 6. No parent check is an independent gate. The full Lytchak PDF was not acquired despite bounded attempts; the actual primary theorem statement and selected definition/proof pages were accessed through indexed primary pages. This access limitation is not disguised as a full body read. Precise ranges and retrieval receipts are in the reading ledger.
