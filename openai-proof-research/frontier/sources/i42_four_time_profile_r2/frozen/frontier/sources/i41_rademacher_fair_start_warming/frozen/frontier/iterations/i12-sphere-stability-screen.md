# Sphere-isometry stability screen

Date: 2026-10-08. **No additional substantial finding.** The strongest natural dimension-independent linear-approximation target is false, already by a classical Euclidean construction. The weaker uniform radial-defect consequence of the accepted sphere theorem is a routine ultraproduct transfer and is not counted.

## Exact corpus input

The pinned *A positive solution to Tingley's problem*, `build/main.tex`, `thm:main`, asserts that every onto isometry `f:S_X -> S_Y` of the unit spheres of arbitrary nonzero real Banach spaces extends by

`T(x)=||x|| f(x/||x||)`, `T(0)=0`,

to a surjective real-linear isometry. No separability or dimension hypothesis is required. Both TeX files in that manuscript were retrieved from pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` and verified against the complete Git tree; [manifest](../sources/i12_sphere_stability/retrieval-manifest.json). The exact theorem and its ultrapower construction in `lem:attainment` were read. The source does not state stability for approximate maps.

## 1. False target: uniform approximation by a linear map

The rejected target would give a function `eta(epsilon)->0`, independent of dimension, such that every onto additive `epsilon`-isometry of unit spheres lies within `eta(epsilon)` of a real-linear operator on the sphere. Even allowing an arbitrary operator, rather than a linear isometry, does not fix the assertion.

Here is the explicit obstruction. View `C^n` as the real Hilbert space of dimension `2n`. For `t>0` set

\[
 f_t(z)_j=z_j|z_j|^{it},\qquad f_t(z)_j=0\ \text{if }z_j=0.
\]

This map preserves Euclidean norm and has inverse `f_-t`, hence restricts to a bijection of the sphere. On one complex coordinate its polar form is `(r,theta)->(r,theta+t log r)`. In orthonormal polar frames its derivative is the shear

\[
 \begin{pmatrix}1&0\\t&1\end{pmatrix}.
\]

The derivative and inverse derivative have norm at most `1+t`. Integrating along a line segment gives that Lipschitz bound; a segment through zero is split there, using continuity at zero. Summing squared coordinate estimates gives

\[
 (1+t)^{-1}\|z-w\|\le\|f_t(z)-f_t(w)\|\le(1+t)\|z-w\|.
\]

On the unit sphere this is an additive `2t`-isometry.

Choose `t=2*pi/log n`, so `t->0` as integer `n->infty`. Let `A` be any real-linear map and put `D=sup_(||z||=1)||f_t(z)-Az||`. Average the conjugates `U^-1 A U` over the compact group of coordinate phase rotations and coordinate permutations. Since `f_t` commutes with that group, convexity preserves the error bound `D`. Commutation with all phase rotations makes the average complex-linear and diagonal; permutations make it `alpha I` for some complex scalar `alpha`.

At `e_1`, `f_t(e_1)=e_1`, so `|1-alpha|<=D`. At the unit vector `v=(1,...,1)/sqrt(n)`, `f_t(v)=-v`, so `|-1-alpha|<=D`. The triangle inequality yields `D>=1`. Conversely the zero operator has error exactly one. Therefore

\[
 \inf_{A\ \mathrm{real\ linear}}\sup_{\|z\|=1}\|f_t(z)-Az\|=1,
 \qquad t=2\pi/\log n. \tag{1}
\]

All witnesses lie on the sphere; this is not an inference from a ball example whose obstruction might occur only in the interior.

**Classical origin.** Kalton, *A remark on quasi-isometries*, Proceedings AMS 131 (2003), 1225–1231, [primary PDF](https://kaltonmemorial.missouri.edu/assets/docs/pams2002b.pdf), Section 2 and Proposition 2.1, gives this coordinate spiral and the averaging argument, crediting Matouskova. The proof explicitly allows the approximating operator to be real-linear and not orthogonal. Its two witness vectors are the same unit vectors used above. The endpoint calculation (1) is elementary within that construction, not a new mechanism. Kalton's Theorem 2.6 gives the matching logarithmic dimension scale for Euclidean ball quasi-isometries. This does not assert the same rate under every additive sphere-only hypothesis.

The [publisher entry for Vestfrid's sphere paper](https://umj.imath.kiev.ua/index.php/umj/article/view/6049) separately identifies sphere approximation results in finite-dimensional Hilbert and supremum-norm spaces. Its abstract alone was not used as a quantitative theorem. Matouskova's original preprint was accessible through web extraction, but direct retrieval returned 404; the retained primary full text used here is Kalton's paper.

## 2. A true but routine consequence: uniform radial defect

For an onto map `f:S_X->S_Y`, assume

\[
 |\|f(x)-f(y)\|-\|x-y\||\le\epsilon\quad(x,y\in S_X).
\]

There is, under the accepted Tingley theorem, a universal function `omega(epsilon)->0` as `epsilon->0` such that

\[
 \sup_{x,y\in S_X,\ 0\le q\le1}
 \left|\|f(x)-qf(y)\|-\|x-qy\|\right|\le\omega(\epsilon). \tag{2}
\]

This permits noninjective maps; onto is enough. To prove (2), suppose that a sequence `epsilon_n->0` has witnessed defects bounded below by a fixed positive number. Take Banach ultraproducts of the corresponding spaces. Unit vectors have unit representatives, and applying `f_n` termwise defines an isometry between the ultraproduct spheres: the additive errors vanish, and also ensure independence of representatives. Onto maps give a preimage sequence for every unit target sequence, hence surjectivity. The accepted theorem makes the radial extension of the resulting sphere map linear and isometric. Passing the witness parameters `q_n` to their ultralimit contradicts their positive radial defect. The change from `q_n` to its limit costs at most twice their difference. Defining `omega` as the supremum over all such maps makes the conclusion precise; the supremum is bounded by two.

This is a direct compactness consequence, close to the source's own attainment construction. It gives no explicit rate, nor a linear approximating operator in the original spaces. In particular it cannot evade (1). A genuinely additional stability result would require an explicit quantitative radial estimate, or structural restrictions that eliminate the classical dimension obstruction, together with a comparison against existing extension and quasi-isometry results. Neither is supplied here.

## Decision

Do not count (1), which is classical, or (2), which is a routine consequence of the accepted source. No proof audit is requested for a new finding from this screen. The false uniform linear-stability target is closed; an explicit general radial-defect rate remains an unproved possible direction. No corpus truth audit or claim of worldwide priority is made.
