# Family 352: full angular stability screen

Disposition: no stability theorem proved, no nominee, and no open basin or finite codimension asserted. The assigned full nonsymmetric target remains open in this screen. Source truth is stipulated. This is an exact interface diagnosis, not a negative stability result.

## Mechanism actually supplied

The source constructs one U(10)-invariant Calabi flow in the Fubini–Study class of CP^10 with finite-time scalar-curvature blowup. Its radial variable is the momentum x=Phi_l, l=log|Z|^2, and v=Phi_ll=x(1-x)+x^2(1-x)^2 H. The equation is H_t+(1+x(1-x)H)^2 A H=0. The factorization of A uses the Laplacian on S^29 in R^24 x R^6 restricted to O(24)xO(6)-invariant functions. Its flat model uses radial functions on R^24. Neither auxiliary angular space identifies with physical angular perturbations of a Kähler potential on CP^10 (real dimension 20).

In flat similarity variables the source operator is

    v_tau + (A_f/16) Delta^2 v + (zeta.grad v)/4 + (1/2+B_f)v,
    A_f=G(|zeta|^2)^2, B_f=-y G'(y)/G(y).

The coefficient differences from the constant model decay at infinity. Compactness of the time-one semigroup perturbation gives a finite Riesz subspace outside a chosen radius q in (exp(-1/2),1). The argument is applied on C_0,rad(R^24). No count of eigenvalues outside the unit circle, zero modes, or physical symmetry modes is calculated. In particular, the finite subspace outside q includes modes merely decaying slower than the selected rate; calling it unstable does not establish an unstable-mode count.

The inverse sums stable contributions from past forcing and complementary contributions from future forcing. It imposes no initial condition. Inner/outer gluing cancels the inner commutator exactly in the outer forcing, and a weighted contraction produces a single solution. Its initial value is selected by the construction. Forward short-time uniqueness implies preservation of the constructed symmetry, not stability for nearby nonsymmetric data.

## A physical angular calculation

This calculation is an elementary diagnostic, not a novel result. Let q=|Z|^2, x=Phi_l, v=Phi_ll and g_{i bar j}=partial_i partial_bar_j Phi(log q). On q>0,

    Delta_g = (q/x) Delta_C + (1/v-1/x) R barR,
    R=sum z_i partial_i, barR=sum barz_i partial_bar_i.

Let P_{a,b} be a Euclidean-harmonic bihomogeneous polynomial of bidegree (a,b). Direct differentiation gives

    Delta_C(f(q)P)=[q f''+(n+a+b)f']P,
    R barR(f(q)P)=[q^2 f''+(a+b+1)q f'+ab f]P.

Consequently the physical scalar Laplacian in this angular sector is

    D_{a,b}f = (q^2/v)f''
              +q[(n-1)/x+(a+b+1)/v]f'
              +ab(1/v-1/x)f.

It reduces to the radial expression at a=b=0. The a,b-dependent terms cannot be inferred from unrestricted auxiliary R^24 harmonics. The full potential linearization is -Delta_g^2 psi-Ric_g^{i bar j}psi_{i bar j}, with the inverse metrics in the raised Ricci tensor, modulo the chosen potential-constant normalization. Determining D_{a,b} alone therefore does not determine its spectrum. The radial Ricci potential is n log q-(n-1)log x-log v, which provides a route to its remaining coefficients.

Smoothness at the origin requires smooth physical potentials f(q)P_{a,b}; global perturbations must also extend across the projective divisor. Inner infinity is conical since v/x tends to c<1, not a Euclidean asymptotic end. The source's momentum self-similarity does not by itself fix a time-independent physical-coordinate scaling: the affine normalization of the Legendre potential is tied to u_t=K(H). The physical similarity operator and its closed weighted domain must first be derived with that normalization.

Constant potentials do not change the form. Projective automorphisms preserve the class and can move the singular point or dilate a chart; time translation changes blowup time. Whether their infinitesimal variations lie in the selected domain must be checked. Rescaling the metric changes the fixed cohomology class and cannot automatically be removed as a gauge. No kernel multiplicity or unstable count is assigned here.

## Primary comparisons and unpaid work

Chen–He, math/0603523v3, stability section: the background is a smooth compact cscK metric, with uniform metric equivalence and a small c^{3,alpha} perturbation. Nonnegative Lichnerowicz structure, removal of holomorphic-potential directions, and a positive spectral gap give energy decay and a continuation iteration. This does not calculate the singular noncompact rescaled operator above.

Huang–Zheng, 1007.4571v2: the background is a smooth compact extremal metric; modified flow and automorphisms handle its stationary drift. The long-time argument uses distance contraction, smooth compactness and local regularity; exponential convergence uses the relevant invariance and a uniform gap orthogonal to constants and holomorphic potentials. That gap comes from smooth compactness of the background family, absent from the degenerating physical singularity. Neither paper supplies the missing angular shrinking spectrum.

Required before a full-scope theorem: derive the physical rescaled fourth-order operator in every (a,b) sector; specify its origin, infinity and global matching domains; prove uniform estimates for large angular degree; classify the finitely many remaining spectrum and symmetry modes; construct the associated nonlinear forward slice/modulation and glue it to the compact exterior. The source's radial future-forcing inverse pays none of the initial-data codimension or unstable count. These are concrete new spectral/PDE tasks, not an available deduction. This screen has no mechanism that closes them.

A direct critical L^10 scalar-curvature integration suggested by the radial profile would be a technical scaling corollary; it is not substituted for the assigned nonsymmetric target and is not nominated.

## Reading limits

Actual source reads in this round: geometry.tex 1–499, flat.tex 1–585, parabolic.tex 1–536, compact.tex 1–666; profile.tex 1–150; references.bib full. The introduction was read in r30 and retained here; no fresh full read is attributed. The validated profile theorem is stipulated; the rest of profile.tex and certificate.tex were not independently read or audited. README/main/preamble/figure are retained dependencies, not semantic proof reads. Complete-tree path screening found one Calabi-flow manuscript for family 352; algebraic Calabi–Yau titles are unrelated.

Primary actual reads: Chen–He main.tex 425–482 and 960–1232 (complete stability section); Huang–Zheng main.tex 69–440 (operative introduction and long-time/exponential arguments). Their other proof operations are not certified. Primary versioned source downloads and decompressed text are retained privately. Search results were used for discovery, not as proof. This is a bounded comparison, not a literature-wide novelty certificate.

Original prose: Myeongjin Kang, CC BY 4.0. No affiliation. Third-party source bodies remain private.
