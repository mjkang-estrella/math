# Exact tensor transition and quantitative off-diagonal bounds

Author derivations continuing the live paired route. These do not prove or disprove full hyperbolic restriction. They identify what the actual transverse geometry supplies and why a particular positive off-diagonal closure fails.

## 1. Tensorization is exact

For finite frame transitions T1,T2, the pair of arrays evolves by T1⊗T2. In coordinates,

    D'_(b1,b2)=Σ_(v1,v2) (T1)_(b1,v1)(T2)_(b2,v2)D_(v1,v2).

For a rank-one input D=d1⊗d2 this remains c1⊗c2, but every intermediate pair (v1,v2) must be retained in the identity. Restricting to pairs at the same position is an additional projection, not a frame identity. Inserting it changes the output, as the two-coordinate example in `bilinear-route-live.md` demonstrates.

## 2. A genuine transverse tensor bound

Take two fixed compact frequency squares Q1,Q2 separated in both coordinates, so |ξ1−ξ2| and |η1−η2| are bounded below by a fixed positive number on their product. For an arbitrary tensor F∈L²(Q1×Q2), define

\[
 \mathcal E F(x,y,t)=\int F(\xi_1,\eta_1,\xi_2,\eta_2)
 e\big(x(\xi_1+\xi_2)+y(\eta_1+\eta_2)
       +t(\xi_1\eta_1+\xi_2\eta_2)\big)\,d\xi_1d\eta_1d\xi_2d\eta_2.
\]

Set a=ξ1+ξ2, b=η1+η2, u=ξ1−ξ2, v=η1−η2, c=(ab+uv)/2, w=2c−ab. Then v=w/u and

\[
 d\xi_1d\eta_1d\xi_2d\eta_2
    =\frac1{2|u|}\,da\,db\,dc\,du.
\]

The original-to-(a,b,u,v) determinant has absolute value 1/4; replacing v by c contributes 2/|u|. Thus \(\mathcal EF\) is the inverse Fourier transform of

\[
 \mathcal C F(a,b,c)=\int
 F\left(\frac{a+u}2,\frac{b+w/u}2,
         \frac{a-u}2,\frac{b-w/u}2\right)\frac{du}{2|u|},
\]
with the integrand zero outside Q1×Q2. The u-interval is bounded and |u|≥c0. Cauchy–Schwarz on each fiber, followed by the displayed change of variables and Plancherel, proves

\[
 \|\mathcal EF\|_{L^2(\mathbb R^3)}^2\le C\|F\|_{L^2(Q_1\times Q_2)}^2.
\]

This is an actual bound for arbitrary tensors, including all off-diagonal intermediate positions. If the u-support of each fiber has length at most h, the same proof gives C h on the right. For rank-one F=f1⊗f2, it is the usual transverse bilinear L² estimate.

In the source's finest input frame δ=1/N, synthesis obeys ||S d_i||²≤(Dδ)^(-2)Σ|d_i|². With M_i=N^(-2)Σ|d_i|², this is ≤C N^4 M_i. Applying the tensor bound to f1⊗f2 gives a physical-space fourth-power product bound C N^8 M1M2. For output samples on the fixed physical lattice (x,y,t)∈D^(-1)Z²×Z, bounded frequency support gives Σ|E f1 E f2|²≤C||E f1 E f2||²_2. To see this without assuming exact orthogonal sampling, convolve the band-limited product with a fixed Schwartz reproducing kernel and apply Cauchy–Schwarz, then sum its uniformly bounded lattice translates. Hence

\[
 N^{-6}\sum_{\rm retained}|c_{1,b}c_{2,b}|^2
      \le C N^2 M_1M_2.
\]

Fixed terminal frequency windows can be incorporated into f_i; only finitely many coarse windows are involved. This is not the source's desired subpower propagation: it loses N² at this normalization, and has no local multiplicity k_i or geometric capacity improvement. It is nevertheless a valid off-diagonal estimate, rather than an assumed interface.

## 3. Relative positions expose a curved-fiber kernel

Modulating the two input frequencies by spatial centers x1,x2 gives on each (a,b,c)-fiber the common phase

\[
 e\left(-\tfrac12(x_1+x_2)\cdot(a,b)\right)
 e\left(-\tfrac12q_1u-\tfrac12q_2 w/u\right),\qquad q=x_1-x_2.
\]

Thus the interaction kernel of smooth fiber packets is of the form

\[
 K_w(q)=\int A(u)e\left(-\frac{q_1u+q_2w/u}{2}\right)du,
\]
with A smooth and compactly supported away from zero. This is an exact formula, not a heuristic dependence on the distance |q|. The linear form in q does not decay rapidly in every direction: it has a stationary point whenever q1=q2 w/u² on the support.

For a concrete sharp lower bound fix w=1 and choose nonnegative A supported in (1,1.3), strictly positive on [1.1,1.2]. Let

    q=(N/D)(k,l),
    N≤k≤1.1N, 1.35N≤l≤1.4N,

with integer k,l. Then u0=√(l/k) lies in a compact subinterval of (1.1,1.2). The phase has a unique stationary point there and second derivative of size N², uniformly over these pairs. One-dimensional stationary phase therefore gives

\[
 K_1(q)=e(-\sqrt{q_1q_2})e(-1/8)
       \frac{A(u_0)}{\sqrt{q_2/u_0^3}}+O(N^{-2}),
\]
where the harmless fixed convention-dependent leading constant is nonzero (with e(s)=exp(2πis), the displayed normalization is the usual one). Only its magnitude is used: |K1(q)|≥c/N for sufficiently large N, uniformly on this rectangle of indices.

For completeness, the asymptotic follows by separating a fixed neighborhood of u0, making the smooth Morse coordinate in which the phase is its value plus a nonzero quadratic, and scaling that coordinate by √|q|. The Gaussian integral supplies the nonzero leading term. Integrating by parts outside the neighborhood and Taylor-expanding the smooth transformed amplitude gives a uniform O(|q|^(-1)) remainder. Compactness of the u0-interval makes every constant uniform. Thus the lower bound is not inferred merely from an upper decay estimate.

There are ≥cN² such q-values. They lie on the *actual* input physical-position difference grid (N/D)Z², with bounded source position labels q/N². Consequently

\[
 \sum_{q\ \mathrm{in\ this\ bounded\ label\ rectangle}}|K_1(q)|\ge cN.
\]

This excludes a uniform subpower absolute Schur-row estimate for this whole-fiber relative-position kernel. A proof that discards all its oscillatory phases and then claims summability over the bounded-label off-diagonal grid necessarily loses a power. It does not exclude a signed L² bound (section 2 already supplies one), a more refined frequency-cell estimate, or a new tensor capacity with compensating geometry. In particular, this is not a counterexample to Demeter–Wu's bilinear theorem.

## 4. Exact crossing-time gain, and its limit

At input scale δ=1/N, physical packets have core width O(N) and time length O(N²). For a pair with velocities U1,U2 satisfying |U1−U2|≥c0, simultaneous core activity requires

    |q+t(U1−U2)|≤C N.

Projection onto U1−U2 shows that its set of allowed t has length at most 2CN/|U1−U2|. Projection onto the perpendicular direction also requires |q_perp|≤CN. Hence a fixed root pair meets only O(N) unit terminal-time bins, not N². This is sharp at the core scale: choose q so that the two center lines meet at an interior time; their cores then overlap for an interval of length comparable to N. With inflated counted tubes N^(1+ε), the corresponding bound is O(N^(1+ε)), not O(N).

For one pair of fixed-profile packets with coefficients d1,d2, transverse Schwartz decay yields the integrated estimate

    ∫ |F1 F2|² dx dy dt ≤ C |d1 d2|² N³/|U1−U2|.

Indeed the spatial intersection integral is at most C N²(1+|q+tΔU|/N)^(-L), and integration along the line t↦q+tΔU contributes C N/|ΔU|. This is a genuine one-power improvement over a single packet's N⁴ fourth-power cost. Summing arbitrary packet pairs is the issue: squaring the sum creates cross terms between different root pairs, precisely the curved-fiber interactions of section 3. The one-pair estimate does not justify dropping them.

## 5. What the actual primary proof does

Demeter–Wu v2, §2 Proposition 2.2, uses planar bilinear orthogonality to obtain rectangles in a direction transverse to both coordinate rulings, then curved cylindrical decoupling. Its full §3 proof was actually read for this continuation. Lemmas 3.2–3.6, Proposition 3.8, and Propositions 3.13–3.14 repeatedly decouple/recouple frequency rectangles and replace a pair by square sums of new transverse pairs. In Proposition 3.8 the original pairing is explicitly dispensed with after new transversality is encoded in g_ω; Proposition 3.13 later restores the geometric average of the two original populations.

Those operations explain why the scalar theorem can retain oscillation without a summable positive relative-position kernel. They do not preserve the source's original root-to-leaf path incidence data term by term. The source's geometric entropy/path theorem therefore cannot simply be applied to an unchanged pair genealogy throughout that proof.

## Bounded conclusion

The unchanged linear source theorem fails by `ruling-obstruction.md`. The diagonal paired iteration fails to preserve exact transitions. Exact tensorization has a valid L² estimate and a sharp transverse crossing-time gain, but the positive whole-fiber Schur closure loses at least N, and the actual primary's oscillatory repair changes pair genealogy. The attempted route through unchanged source capacities plus a positive off-diagonal summation is exhausted. A different oscillatory tensor geometry could still prove the full target; it has not been constructed here. There is no full-target nominee and no claim that the unrestricted mathematical route is impossible.
