# Prefreeze working mathematics — inverse boundary family only

No statement is frozen. A full target being tested is simultaneous exact equality of the full scalar conductivity boundary operators at zero and at a prescribed negative spectral parameter, with the same known positive bulk density 1, on B(0,3). At spectral parameter z=-tau<0, the energy is integral gamma |grad u|^2 + tau u^2, so no eigenvalue ambiguity can conceal an obstruction. Conductivities must be uniformly positive bounded scalars, equal 1 in a collar, and distinct on positive volume. This is an attempted full inverse-data operation, not a nominee or a claimed open-problem/priority designation.

The strongest available starting point is Source365's entire zero-frequency construction, including its exact two-Cauchy-pair scalarization and branching-block currents, not just thm:main. In particular source cor:localized already supplies finite independent local choices; no credit is proposed for gluing more copies. I07 section3C already identifies smoothing as routine and fractional regularity of the scalarization block as unpaid. This round does not pursue those old targets.

Write a(u,v)=int gamma grad u.grad v, P f=u_f, ell(f)=u_* (the common surface average), w the compactly supported bounded H1 source potential, rho=1+delta w, and gamma_delta=rho^2 gamma. Source weighted identity and flux computation give P_delta f = ell(f)+(P f-ell(f))/rho for smooth boundary f, then by continuity in L2 for arbitrary H1/2 data. This is an exact all-input formula at z=0, not a finite voltage approximation.

For each conductivity a, let R_a be the zero-Dirichlet inverse of -div(a grad) on L2. Spectral harmonic extension at z satisfies P_a(z)f=P_a f+z R_a P_a(z)f, hence P_a(z)=(I-z R_a)^(-1)P_a for |z| ||R_a||<1. Green's weak identity gives
  <(Lambda_a(z)-Lambda_a(0))f,g> = -z <(I-z R_a)^(-1)P_a f, P_a g>_L2.
Thus equality at zero does not discard the bulk Gram form. With a known unit density, the first frequency derivative differs by
  -int [(ell f+(u_f-ell f)/rho)(ell g+(u_g-ell g)/rho)-u_fu_g].
This is an infinite collection of product constraints, not source's measure-annihilation identity. The latter controls L_gamma w acting on (u-u_*)phi, not Lebesgue integrals of products of transformed harmonic functions.

Allowing the auxiliary density rho^2 (ONLY as a diagnostic, not as a relaxation of the target) cancels the denominators and gives a rank-at-most-two first-derivative difference:
  -delta[ell(f) int w u_g + ell(g) int w u_f] - delta^2 ||w||_2^2 ell(f)ell(g).
This is a classical Gram/resolvent computation. It does not constitute a substantial new theorem. It also exposes that even changing density in the natural way does not automatically extend zero-frequency invisibility: for f=g=1 and int w=0 the difference is -delta^2||w||_2^2, strictly nonzero.

Next mathematical work: derive all-frequency reduction at negative z without a power-series radius restriction; identify whether nested-cell charge choices can solve the exact bulk defect; compare with actual primary conformal-gauge and approximate multifrequency cloaking proofs before any freeze. Scalarization is exact for two fixed harmonic fields. It must not be silently used for an entire frequency-parametrized family or for inhomogeneous equations.
