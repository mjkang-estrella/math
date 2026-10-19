# Finite-order boundary-layer calculation after freeze

This is postfreeze work for T372L127, not a separate nominee. Lin–Nakamura1708.00591v1 was acquired and read after the freeze: its actual localized Taylor/ODE construction, energy correction, Hardy estimates and coordinate change were examined. Tan–Liu2211.06650v1 had already been read before freezing. The argument below keeps its own normalization and the full frozen Jordan solution. It does not import the printed higher-jet limit as a quantitative estimate.

Fix a smooth boundary chart at x0, choose orthonormal tangential coordinates there, and let y3 be inward normal distance. Set t=N^(-1/2), z'=y'/t, s=y3/t^2. For a fixed compactly supported smooth eta on R2 with integral eta^2=1, use boundary displacement

    phi_N(y')=eta(y'/t) exp(i y1/t^2) a.

Its H^(1/2) norm is uniformly bounded: its L2 norm is O(t), its H1 norm is O(t^-1), and interpolation gives O(1). Boundary coordinate changes preserve this bound uniformly over the compact boundary. The tangential support area is t^2=N^-1; the normal boundary layer has width t^2=N^-1. Thus a product of two leading derivatives, each of order N, has an integral of order one. This normalization is part of the calculation.

For frozen coefficients let b=(lambda+mu)/(lambda+3mu), so 0<b<1 uniformly away from the endpoints on the fixed admissible range. On the tangential-normal two-plane the decaying solution with trace a is

    E(s)a = exp(-s)(I+b s J)a,
    J=[-1,-i; -i,1], J^2=0,

with the remaining shear component exp(-s). This follows by substituting in the constant Lamé equation, or by the explicit decaying matrix in I118/I121. In particular the boundary vector e3 gives

    u1=-i b s exp(-s), u3=(1+b s)exp(-s),
    i u1+partial_s u3=(b-1)exp(-s).

The vector e2 gives a purely shear solution with zero divergence. Omitting the sJ term would give the wrong compressional profile.

Here is a finite-order construction with uniform bounds. Write the flattened physical operator in divergence form, retaining the fixed coordinate Jacobian in the energy. Substitute exp(i y1/t^2)V(z',s), divide the operator by t^-4, and Taylor expand the coefficients at x0. A tangential monomial of degree p and a normal monomial of degree q carry t^(p+2q). Tangential envelope differentiation carries t, while normal differentiation in s carries no additional t. Thus for any fixed integer S the expansion has the form

    L0 + t L1 + ... + t^S L_S + remainder,

where L0 is the frozen normal ODE and each L_j has polynomial coefficients in z',s and differential order at most two. Taylor derivatives through S+2 suffice. On |z'|<=1 the remainder applied to a finite polynomial in s times exp(-s) is bounded by C t^(S+1)(1+s)^A exp(-s), with a possibly larger fixed A. The same bound holds for the differentiated coefficient terms. Constants depend only on finitely many coefficient derivatives, ellipticity and the fixed chart.

Take V0=eta(z')E(s)a and solve successively

    L0 V_j = -sum_(1<=l<=j) L_l V_(j-l),
    V_j(z',0)=0, V_j decays as s tends to infinity.

Every forcing is a polynomial in s times exp(-s), with smooth compactly supported z' coefficients. The solution has the same form, of possibly larger finite degree. To justify solvability without assuming diagonalizability, put the constant second-order ODE into its six-dimensional first-order system. Its two generalized eigenspaces have exponents +1 and -1, with Jordan blocks of size at most two. Variation of constants on those subspaces gives polynomial-exponential particular solutions. Eliminate the growing branch and correct the boundary value by the decaying homogeneous solution. The trace map from the decaying subspace to C3 is an isomorphism: surjectivity is the displayed E(s); injectivity also follows from the positive frozen Dirichlet energy. Its inverse and all matrices used here are uniformly bounded on the compact admissible range. This proves the required finite recurrence and its uniform bounds, including the repeated-root case. No inversion of a fictitiously scalar normal symbol is used.

Multiply the finite sum by a normal cutoff equal to one for y3<=t/2 and zero for y3>=t. Its derivatives meet exp(-s) only at s comparable to t^-1, so their errors are smaller than every fixed power of t. The Taylor remainder estimate remains valid there after polynomial factors are absorbed by exp(-s). The volume factor in the L2 norm is t^2. Restoring t^-4 gives

    ||L Phi_N||L2 <= C t^(S-1).

Phi_N has the exact boundary trace phi_N. Solve away this residual by the coercive physical Dirichlet inverse. The exact solution u_N therefore obeys

    ||u_N-Phi_N||H1 <= C t^(S-1),
    ||Phi_N||H1+||u_N||H1 <= C.

For recovering normal order m<=119, choose S=2m+8. Then the correction is O(N^(-m-7/2)), and the construction uses coefficient derivatives through 2m+10<=248. The many derivatives of the FIXED eta and finite polynomial degrees affect constants, not the number of derivatives of the unknown coefficients. Smooth fixed boundary geometry may contribute its own finite chart derivatives. All are allowed to enter constants depending on Omega.

At m=0, the physical energy limit recovers the frozen impedance matrix Z. Its difference is bounded by C delta, since the traces have bounded H^(1/2) norm and the above residual errors vanish. Tan–Liu's actual principal-symbol algebra gives mu=(f1+f2)/2 and lambda=mu(f2/f1-2), where f1=2mu^2/(lambda+3mu) and f2=2mu(lambda+2mu)/(lambda+3mu) are entries/combinations of Z. Since f1 is bounded away from zero, boundary values satisfy t0<=C delta uniformly. This is an algebraic use of the principal symbol; it makes no assumption about a smoothing remainder.

Assume all lower normal jets through order m-1 differ uniformly by at most t_(m-1). Taylor expand the coefficient difference in normal distance at each tangential point. The order-m coefficient at y'=0 changes by O(|y'|) over the support. Hence it is the desired jet at x0 plus an O(t) error. The physical energy identity for the two EXACT solutions is

    <(Lambda1-Lambda2)phi_N,phi_N>
      = integral [Delta lambda div u1 overline(div u2)
                   +2 Delta mu e(u1):overline(e(u2))].

Replace u_j by Phi_j using the preceding H1 correction. After multiplication by N^m the replacement error is O(N^-7/2). Terms from lower normal jets are bounded by C t_(m-1) N^m. Leading profiles in the two media differ by O(delta), since their boundary values differ by O(delta); replacing the second frozen profile by the first costs C delta in the scaled order-m term and can be included in the same bound. Subleading envelope terms, the order-m tangential variation, fixed coordinate factors and the Taylor remainder contribute O(N^-1/2), plus the already retained lower-jet error. These bounds follow by integrating each polynomial in s against exp(-2s); all such moments are finite, uniformly for the fixed finite recurrence.

The shear polarization a=e2 gives a positive coefficient of Delta(partial_n^m mu) and zero coefficient of Delta(partial_n^m lambda). Its coefficient is a positive fixed multiple of integral s^m exp(-2s)/m! ds. The polarization a=e3 has lambda coefficient

    (1-b)^2 / 2^(m+1) > 0.

The corresponding mu coefficient is bounded. Thus the two polarizations form a triangular invertible system uniformly on the admissible coefficient range. Curved-coordinate factors at the base point are the identity after the chosen orthonormalization. Their higher normal derivatives multiply only lower normal coefficient jets, already controlled by t_(m-1). The Jacobian in the energy is retained; it equals one at the base point and its variation contributes the same O(t) error.

Consequently

    t_m <= C_m [(delta+t_(m-1)) N^m + N^-1/2].

Choose N comparable to (delta+t_(m-1))^(-1/(m+1/2)) when this is large; otherwise use the a priori jet bound. Induction gives t_m<=C_m delta^(b_m), with b_0=1 and b_m=b_(m-1)/(2m+1)>0. Constants and exponents may be enlarged or decreased uniformly. No limit depending on an individual coefficient pair is used.

Finally interpolate each normal-jet difference on the compact boundary between this C0 bound and its uniform C101 tangential bound. Such a bound uses at most119+101=220 derivatives of the original coefficients, plus fixed geometry. This yields a positive-power bound t<=C delta^b for normal jets through119 with tangential derivatives through100. The finite-order construction above used at most248 coefficient derivatives; both fit strictly inside the frozen order1000.

For later collar matching, Taylor's formula then gives, for a=lambda or mu and a fixed cutoff chi,

    a2'=a1+chi(d/epsilon)(a2-a1),
    ||a2'-a2||C100 <= C(t epsilon^-100+epsilon^20).

Set epsilon=t^(1/200). The difference is at most C t^(1/10). The pair a2' agrees exactly with a1 in a collar and obeys the original positivity inequalities, because the replacement is pointwise convex. Only a uniform C100 bound is retained after this step; claiming a uniform C1000 bound for the modified coefficients would be unjustified. The intended common-exterior argument must use at most those100 derivatives.

The quasimode recurrence and energy extraction are classical boundary-layer operations of the type used by Lin–Nakamura, with the uniform finite-order budget, normalization and frozen profiles made explicit here. They are not claimed as a separate new mechanism or independent gate. The postfreeze primary timing and limits are retained.
