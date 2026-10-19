# Supported least-squares residual calculation

Postfreeze development for T372L127. This calculation alone is not the frozen theorem or a nominee. All spaces below are complex; use real parts in quadratic identities. It isolates the step that must be compatible with physical CGOs, moving planes, and the finite regularity class.

Let D_s compactly contained in D_R compactly contained in D_T be concentric planar disks. Let P_z=D_z+A_z(y) be a square first-order operator, with scalar principal part a nonzero complex multiple of partial_1+i partial_2. Here z is a finite-dimensional real parameter in a compact box; the principal multiple is bounded above and away from zero. Suppose P_z has no nonzero compactly supported homogeneous distribution and has the supported estimate

    ||v||H^(j+1) <= C ||P_z v||H^j,
    supp v contained in closure D_R.                       (1)

Use full-plane Sobolev norms of zero extensions and the Fourier norm with weight (1+|xi|^2)^j. The domain X_j consists of those supported H^(j+1) functions. It is closed. For f_z supported in D_s, let w_z minimize ||P_z w-f_z||H^j over X_j and set e_z=P_z w_z-f_z. Existence and uniqueness follow from (1): the range is closed and P_z is injective. Equivalently w_z=(P_z^*P_z)^(-1)P_z^* f_z, where adjoints use the X_j and H^j Hilbert structures, not an unrestricted Dirichlet inverse.

The normal equation gives

    <e_z,P_z v>H^j=0 (v in X_j),
    ||e_z||H^j^2 = -<e_z,f_z>H^j.                         (2)

With Q_j=(1-Delta_y)^j, the first identity implies

    P_z^dagger Q_j e_z=0 in D_R.                         (3)

Here dagger is the distributional L2 formal adjoint. Its principal symbol is the nonvanishing scalar conjugate of the symbol of D_z times (1+|xi|^2)^j, of order 2j+1. Interior elliptic regularity therefore bounds every fixed finite number of interior y derivatives of Q_j e_z by a finite higher coefficient bound and ||e_z||H^j. This is an interior statement only: no smoothness through the artificial support boundary is asserted.

If P,f depend C^k on z in the relevant operator norms and (1) is uniform, w and e depend C^k in their Hilbert spaces. Indeed the positive bounded operator P_z^*P_z:X_j->X_j has lower bound C^-2; differentiating its inverse uses d(B^-1)=-B^-1(dB)B^-1. After parameter differentiation, (3) is an elliptic inhomogeneous equation with previously controlled terms. Thus, on every D_s' strictly between D_s and D_R, Q_j e_z has bounded joint H^q(y,z) norms for any fixed q for which the coefficient and parameter derivatives have been supplied. Constants require only finitely many derivatives; there is no assertion uniform in q.

Now assume there are g_h in L2(y,t), supported in D_s for each transverse parameter t in a box J, with uniformly bounded L2 norm and

    ||P g_h-f||H^-2(y,t) <= epsilon_h.                  (4)

Additional direction parameters may be fixed; the bounds are uniform in them. Choose a smooth transverse cutoff psi compactly supported in J and a y cutoff chi supported in D_R and equal to one on a neighborhood of closure D_s. Let R_h=P g_h-f. Pair it with psi^2 chi Q_j e. By (3), distributional integration by parts gives

    <P g_h, psi^2 chi Q_j e> = 0.

Indeed P differentiates y only; the derivatives of chi are outside the support of g_h. Since f is supported where chi=1, (2) yields the exact identity

    integral_J psi(t)^2 ||e_t||H^j(y)^2 dt
       = Re <R_h, psi^2 chi Q_j e>.                    (5)

The test function on the right has a uniform joint H2 bound by the preceding interior elliptic and parameter estimates. Therefore

    ||psi e||L2_t H^j_y <= C epsilon_h^(1/2).           (6)

This step does not claim that the least-squares inverse maps arbitrary H^-2 errors into high Sobolev norms. It uses the normal equation of its particular residual, the strict support margin, and bounded parameter derivatives of P and f. These hypotheses must be verified in an application.

If direction parameters range in a compact patch, integrate (5) in those parameters. A uniform high-order mixed bound on e then gives, by Sobolev interpolation and embedding on a slightly smaller parameter patch,

    ||e||C^q(y,t,direction) <= C epsilon_h^b            (7)

for each fixed requested q below the supplied regularity; b>0. For example j=24, parameter derivatives through20, and the corresponding mixed bounds give a joint H20 bound in five real variables and small L2 norm. Interpolation at H16, followed by H16 -> C12 in dimension5, gives b=1/10. No sharp exponent is needed. One must work inside the transverse cutoff plateau. Finitely many plateaus can be combined with a partition of unity depending only on transverse and direction variables, since D differentiates neither. The derivative bounds of that partition enter the constant.

Uniformity of (1) over bounded finite-regularity coefficient classes is an additional issue. For a compact C1 family, a failure of the j=0 bound produces normalized supported H1 functions with P v tending to zero in L2. Rellich compactness and the ordinary elliptic estimate give a nonzero supported homogeneous limit, a contradiction. Higher j estimates then follow by elliptic regularity. To apply this to a bounded smooth class one must establish the no-supported-kernel assertion also for every finite-regularity limit, rather than invoke compactness in C-infinity. Local Cauchy-transform frames for C1 matrix coefficients and the holomorphic identity theorem do establish that assertion for this planar scalar-principal operator. This argument concerns the planar operator only, not finite-regularity global elasticity uniqueness.

The calculation explains why ordinary high-order mollification was insufficient and what the projection normal equation adds. It is not a proof of uniform physical CGO, boundary-jet, moving-conic, or coefficient-recovery estimates. Those interfaces are tracked separately.
