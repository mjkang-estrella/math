# Fixed-time factorization: avoiding time-dependent de Rham claims

Author derivation, conditional on a complete smooth Kähler–Ricci flow on an open time interval with nonnegative bisectional curvature. Its purpose is to close the geometric interface, not to invoke a bounded-curvature theorem outside its hypotheses.

Fix an interior time t0. Suppose the underlying manifold is simply connected and has a smooth strictly plurisubharmonic function ψ. By de Rham at t0 the complete metric splits as a Euclidean factor and finitely many complete simply connected irreducible nonflat factors. The splitting is holomorphic: the parallel complex structure preserves each nonflat irreducible factor; on the Euclidean factor choose its constant complex coordinates. Indeed a parallel off-diagonal component between distinct factors would intertwine their independent holonomy representations, hence would supply a fixed vector in an irreducible nonflat representation. Such vectors do not exist. No assertion that this splitting is fixed for nearby times is needed.

An irreducible locally symmetric Kähler factor has parallel Ricci tensor. Its self-adjoint Ricci endomorphism has parallel eigenspaces, so irreducibility forces Ric=λh with a constant λ. Nonnegative bisectional curvature implies λ>=0. If λ=0, summing the nonnegative bisectional components shows they all vanish; polarization gives flatness, already excluded. If λ>0, completeness and Bonnet–Myers make the factor compact. This argument avoids an additional classification of symmetric-space types. A compact positive-dimensional complex factor is impossible here: restriction of ψ to that compact factor would be strictly psh, but its Laplacian has positive integral and also integral zero. Thus every remaining irreducible nonflat factor is nonsymmetric.

Berger's holonomy classification for a nonsymmetric irreducible Kähler metric leaves U(d), SU(d), or Sp(d/2). The last two are Ricci flat. In a nonnegative bisectional metric, Ricci flatness forces every bisectional component to vanish (sum nonnegative terms over a unitary basis), hence the full Kähler curvature tensor vanishes by polarization. That contradicts the nonflat factor. Each remaining factor therefore has holonomy U(d).

We show that its bisectional curvature is strictly positive at t0. Use the full bundle of ordered nonzero (1,0) vector pairs and the function u(X,Y,t)=R_t(X,bar X,Y,bar Y), with the fixed-bundle pullback convention of Cao–Chen–Zhu. Their reaction inequality, localized as in local-null-propagation.md, says the zero set is invariant under parallel transport. A loop in our fixed factor at t0 is also an ambient loop. Its full U(d) action therefore preserves every zero pair in that factor.

First, holomorphic sectional curvature H(X)=u(X,X,t0) cannot vanish for any nonzero factor vector X. Otherwise transitivity of U(d) on the unit sphere makes H identically zero at that point on the factor, and polarization makes its curvature zero there. Parallel transport along factor paths propagates that zero-pair condition and gives flat curvature everywhere, contrary to nonflatness.

Next suppose u(X,Y,t0)=0 for unit vectors. After an irrelevant phase change write Y=a X+b Z with a,b>=0, a²+b²=1, Z⊥X unit. The stabilizer U(d−1) of X sends Z through its unit sphere. Average the resulting zero identities over this sphere; the mixed terms average to zero and

    0 = a² H(X) + b²/(d−1) sum_{j=2}^d u(X,e_j,t0).

All terms are nonnegative, and H(X)>0. Thus a=0. For d=1 every pair is collinear and H>0 already proves the result. For d>=2 a hypothetical zero pair must therefore be orthogonal.

For an orthonormal zero pair e1,e2, at its interior spacetime point u>=0 gives u_t=0, horizontal second derivative >=0, and vertical second derivative >=0. In the Cao–Chen–Zhu curvature evolution

    u_t = L u + A + sum_{p,q}|R(e1,bar e2,e_p,bar e_q)|²,

A is the difference of the first two reaction terms. Their algebraic inequality gives A>=0 at this minimum. Consequently every R(e1,bar e2,e_p,bar e_q) vanishes. The first-variation identities of u at a zero pair and the Kähler symmetries eliminate the remaining mixed terms in the following two-plane rotation. Set v=(e1+e2)/sqrt(2), w=(e1−e2)/sqrt(2). Holonomy invariance says u(v,w,t0)=0, whereas direct expansion gives

    u(v,w,t0) = (H(e1)+H(e2))/4 > 0.

Contradiction. The expansion and zero-reaction mechanism are exactly the Gu/Cao–Chen–Zhu proof; the all-pair averaging above explicitly handles nonorthogonal pairs rather than equating orthogonal bisectional positivity with full positivity.

Thus every irreducible nonflat factor at t0 is complete, noncompact, and strictly positively bisectionally curved. Source338's MAIN theorem applies separately to each factor and makes it biholomorphic to C^d. Their product and the Euclidean factor give C^k. Combining with the initial Ni–Tam compact factor and the compact generalized Frankel classification would prove the original target, once the generalized flow construction is complete.

Dependencies/limits: classical de Rham, Berger holonomy, and symmetric-space type classification are used as named standard theorems, not newly proved here. Gu arXiv:0707.0035v1 has been read in full (357 extracted lines); its Theorem1.1 states compact generalized Frankel and its proof uses the same holonomy and reaction mechanism. Original Berger1955 has now been read at extracted lines1–160 and1990–2155, including ChapterIII§9 Theorem3 (the OCR is imperfect); its full classification proof has not been read. Beauville, Riemannian Holonomy and Algebraic Geometry, lines74–195, supplies a clean modern statement, explicitly permits complete in place of compact in de Rham, and explains Ricci flatness for SU holonomy. Sp is contained in SU. The original de Rham/Mok bodies were not read. No Helgason theorem is needed in the revised symmetric-factor elimination. Bonnet–Myers is used as a standard completeness theorem, not newly proved. Cao–Chen–Zhu Thm2.8 proof has been read in full, and explicitly credits Mok and Gu. No complete theorem claim follows from this note alone: the nonnegative complete flow is its standing hypothesis.
