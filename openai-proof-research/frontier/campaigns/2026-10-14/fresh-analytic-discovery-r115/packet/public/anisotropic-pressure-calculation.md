# Anisotropic product kernel: feasibility calculation, not a frozen target

All calculations below preceded any freeze. There is no frozen theorem, nomination, claimed new Liouville theorem, or contribution assessment. They identify what happens when the actual stipulated source370 interval/pressure operations are applied to a different spatial kernel. They do not audit those operations.

The unfrozen question used for this test was nonexistence of positive smooth entire pairs

    L_A u=v,  L_B v=u^q,    L_C=-div(C grad),
    n>4,  1<q<(n+4)/(n-4),  A,B real constant symmetric positive definite.

No boundedness, finite energy, stability, symmetry, commutation, condition-number bound, or asymptotic hypothesis is included in this exploratory question. Constants in supporting estimates may depend on n,q,A,B (in particular their eigenvalues), not the solution or dilation radius. This is a question, not a post hoc frozen contract. The general question remains unresolved in this work; it is not asserted to be globally open in the literature.

## 1. Strongest elementary reductions first

Noncommutation is not an obstacle here. A common change of spatial variables makes A the identity and B diagonal: use A's square root and then the orthogonal spectral theorem. The remaining issue is unequal eigenvalues, not a lack of simultaneous congruence. The two constant coefficient differential operators commute regardless of whether their matrices commute under matrix multiplication. Eliminating v gives

    P u=u^q,  P=L_B L_A,
    symbol(P)(xi)=(xi^T A xi)(xi^T B xi).

This removes the two distinct marginal measures from the first, uncombined formulation. It must be tried before declaring them an obstruction.

For n>2 let G_C be the positive fundamental solution of L_C,

    G_C(z)=Gamma((n-2)/2)/(4 pi^(n/2))
           (det C)^(-1/2)(z^T C^(-1) z)^((2-n)/2).

The source's positive superharmonic representation (source370, `lem:potential`) applies after one affine change to each equation separately. It gives u=c+G_A*v and v=d+G_B*u^q, c,d>=0. These constants vanish without assuming any integrability at infinity. If c>0, the second potential dominates c^q times the integral of G_B over all space, which is infinite. If d>0, the first potential similarly diverges. Thus

    u=G_A*v,  v=G_B*u^q,  u=K_AB*u^q,
    K_AB=G_A*G_B.                                    (1)

All interchanges are Tonelli interchanges of nonnegative functions. For n>4 the kernel convolution is finite for z!=0: its two individual singularities are locally integrable, and at infinity its radial bound is a constant times r^(3-n). Formula (1) itself ensures finite values of the potential at every point for a putative solution. This supplies a single symmetric interaction f(x)f(y)K_AB(x-y), f=u^q, whose two marginals are f u. Merely saying that the initial kernels differ would miss this compatible reduction.

## 2. Exact positive mixture and linewise operation

Set C_t=tA+(1-t)B, 0<=t<=1. For positive a,b,

    1/(ab)=integral_0^1 [ta+(1-t)b]^(-2) dt.

For a!=b this is direct antidifferentiation; for a=b it is immediate. Equivalently, write 1/(ab) as the double Laplace integral and set s+t=r, s/r=theta, whose Jacobian is r. The Gaussian heat kernels then give the exact physical-space formula, with the Fourier convention exp(-i x.xi),

    K_AB(z)=c_n integral_0^1 (det C_t)^(-1/2)
                     (z^T C_t^(-1)z)^((4-n)/2) dt,
    c_n=Gamma((n-4)/2)/(16 pi^(n/2)).                (2)

To check the constant, integrate r(4 pi r)^(-n/2) exp(-d^2/(4r)) over r>0. Substitution s=d^2/(4r) gives the displayed coefficient. Each C_t stays in a compact positive definite matrix class. Thus K_AB is smooth away from zero, even, positive, homogeneous of degree 4-n, comparable with |z|^(4-n), and has first derivative bounded by a constant times |z|^(3-n).

For a fixed positive matrix M=C_t^(-1), restrict the corresponding summand to lines z_0+s e, z_1+s' e with e^T M(z_0-z_1)=0. Its longitudinal form is a positive multiple of

    (lambda^2+(s-s')^2)^(-(n-4)/2).

The actual midpoint/overlap proof of source370 `lem:interval-pair` works with n-2 replaced by n-4. Indeed its differentiated kernel is -(n-4)h/(lambda^2+h^2) times the kernel. The overlap density is symmetric and decreases away from its interval midpoint separation; pairing h and -h gives the same sign. No new theorem is claimed for this substitution.

However, the required transverse hyperplane depends on M. Different component slices give different source-level endpoints. Integrating their endpoint values over t is not an identity involving u at a single endpoint. The source's nonlinear identity `eq:weighted-layer-identity` uses the actual common potential at the endpoint, not a separately known value of every component potential K_t*f. Thus positivity and (2) alone do not complete the assembly.

A favorable case was also checked. After simultaneous congruence diagonalization, all C_t have the same coordinate axes. For e along such an axis one common transverse hyperplane works for every t. The intervals and their endpoints can be shared, and integration in t recovers the full potential u at those endpoints. This genuinely pays the axis-direction interval interface. It does not yet give the angular localization operation for arbitrary directions. In particular, the source averaged long-interval loss uses a continuum of directions and polar integration; a finite set of axes does not inherit that estimate merely from the endpoint identity.

## 3. The finite matrix obstruction for a common ellipsoidal cutoff

The source localizes X(x)=eta(|x|)x, with w=-r eta'(r)>=0. For one component metric M and an ellipsoidal radius r_H=(x^T H x)^(1/2), H positive definite, use X(x)=eta(r_H)x. Its Jacobian is

    DX=eta I-w x(Hx)^T/(x^T Hx).

For z=x-y near zero, the component virial quotient has leading term

    ((X(x)-X(y))^T Mz)/(z^T Mz)
      =eta(r_H)-w Q_H,M(x,z)+O(|z|),
    Q_H,M(x,z)=((Hx).z)((Mx).z)/[(x^T Hx)(z^T Mz)].   (3)

The error statement is at fixed x in the smooth annulus, with bounded local derivatives. It is not an integrated solution-uniform error estimate.

For nonzero vectors a,b, (a.z)(b.z)>=0 for every z if and only if b is a nonnegative multiple of a. For proof, write b=c a+d with d perpendicular to a. If d!=0, choose a.z=1 and d.z sufficiently negative. If d=0, testing z=a forces c>=0. Applying this to a=Hx,b=Mx proves that Q_H,M is nonnegative for every x,z!=0 if and only if M=cH for a scalar c>0. The last step is elementary: H^(-1)M maps every x into its own line, so basis vectors are eigenvectors and their pairwise sums force all eigenvalues equal. Positivity fixes the sign.

Consequently no fixed ellipsoidal radius yields a nonnegative directional factor for every component of (2) unless A and B are proportional. This is precisely a limitation of that common-cutoff, componentwise-positive proof operation. It is not a counterexample to the PDE question, nor a theorem forbidding other localizations or signed cancellations.

For an exact small diagnostic, take H=I, M=diag(1,4,1,...,1), x=(1,1,0,...), z=(2,-1,0,...). Then Q=-1/8. This example alone would be insufficient: even A=B with anisotropic A has this issue in Euclidean coordinates, and an affine change repairs it. The all-H argument above is needed to isolate the genuinely simultaneous restriction.

## 4. Averaging before localization does not restore this sign condition

One must also test the full kernel rather than objecting separately to its summands. Define

    G(z)=-grad log K_AB(z)/(n-4).

By homogeneity z.G(z)=1. Formula (2) expresses G as the positive, z-dependent weighted average of M_t z/(z^T M_t z), with weights equal to each summand's fraction of K_AB. For the same cutoff, the leading pressure factor becomes

    Q_H,K(x,z)=((Hx).z)(x.G(z))/(x^T Hx).          (4)

For fixed z, requiring this to be nonnegative for every x forces G(z) to be a positive multiple of Hz by the same two-vector argument. Homogeneity then fixes the multiple to 1/(z^T Hz). Thus this sign condition for all x,z is equivalent to

    grad log K_AB(z)=-(n-4)Hz/(z^T Hz),
    K_AB(z)=c (z^T Hz)^((4-n)/2).                 (5)

For the last equality, the difference of the logarithms has zero gradient on the connected punctured space (n>4). Conversely (5) plainly gives the sign condition.

Taking Fourier transforms of (5) and using (2) would make the polynomial (xi^T A xi)(xi^T B xi) a constant multiple of a squared positive quadratic form. A positive definite quadratic polynomial in n>=2 variables is irreducible over the reals: a factorization would consist of two linear forms and hence have a nonzero zero. Unique factorization therefore forces the two quadratics to be proportional. This proves that averaging the kernels first still does not pay the common-ellipsoid nonnegative-factor operation for nonproportional A,B.

The conclusion concerns pointwise nonnegativity of this leading factor. Source pressure is an integrated inequality, and a different proof could exploit its negative parts. Nothing here excludes that possibility. In particular, (4) is not a global impossibility theorem for the source method.

## 5. Why the compatible axes alone do not finish localization

In the simultaneously diagonal coordinates, a positive combination of the coordinate projectors e_i e_i^T is diagonal. The source radial projector omega_x omega_x^T has nonzero off-diagonal entries at generic x. Hence axis intervals alone cannot reproduce the source cap tensor by positive averaging.

There is also no nonzero compactly supported C^1 vector field on R^n, n>=2, whose Jacobian is diagonal everywhere. In fact partial_j X_i=0 for j!=i makes X_i depend only on x_i. Moving another coordinate to infinity leaves X_i unchanged; compact support forces it to vanish. This rules out the literal replacement by a compact separable diagonal-Jacobian vector field. It does not exclude approximate diagonalization, sums with controlled errors, noncompact fields with justified integrability, or a different pressure architecture. None of those missing global estimates was established here.

## 6. What the classical cutoff estimate actually closes

For comparison, take a nonnegative smooth solution of P u=u^q with the same constant A,B, n>4, q>1. Choose 0<=phi<=1 smooth, phi=1 on B_1, supported in B_2, and k an integer at least 4q/(q-1). Put phi_R(x)=phi(x/R). Product differentiation bounds

    |P(phi_R^k)|<=C R^(-4) phi_R^(k-4),

and all derivatives are supported in B_(2R)\B_R. Testing and applying Hölder gives, for E_R=int u^q phi_R^k,

    E_R<=C R^(-4) E_R^(1/q) R^(n/q'),
    E_R<=C R^(n-4q'),   q'=q/(q-1).              (6)

The leftover power of phi in Hölder is nonnegative by the choice of k; C depends on n,q,A,B and the one fixed cutoff. If 1<q<n/(n-4), letting R grow in (6) kills the mass on every fixed ball. At q=n/(n-4), (6) first proves int_R^n u^q<infinity. Keeping only the derivative-support annulus in the first Hölder factor then bounds E_R by C(int_(B2R\BR) u^q)^(1/q), which tends to zero. This also gives nonexistence at that endpoint. These are classical test-function operations and are not nominated.

They leave the entire interval

    n/(n-4)<q<(n+4)/(n-4)

untouched. The desired energy exponent would be n-4(q+1)/(q-1)<0 in the full subcritical range. Formula (6) controls u^q, not u^(q+1), and cannot substitute for that energy bound. A formal global homogeneous Pohozaev identity would require justified global integrations; finite energy is absent from the exploratory question and has not been supplied.

## 7. Actual source and primary comparison; exact missing step

The pinned source is [The Subcritical Henon–Lane–Emden Conjecture, September 24](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Subcritical-Henon-Lane-Emden-Conjecture-September-24-2026/build/sections/01-introduction.tex), `thm:main`. Its six retained sections were read. In addition to `lem:potential` and `prop:uniform`, the operative inputs are `eq:interaction`, `eq:virial`, `lem:localization`, `lem:interval-pair`, `prop:pressure`, `lem:layer-loss`, `eq:weighted-layer-identity`, and `prop:energy`. The source already supplies the complete unbounded-solution local-energy/scale contradiction. Proportional A,B reduce to it by coordinates and amplitudes; this is not new work.

[Lin, CMH 73 (1998), 206–231](https://ems.press/content/serial-article-files/42794?nt=1), §4 equations (4.1)–(4.4), Lemma4.1 and the proofs following it, was read through the radial classification argument near the end. Its Kelvin transform and moving-plane argument are an actual stronger classical reduction for the isotropic fourth-order equation. They do not supply that transform for a product of nonproportional quadratic symbols. The printed introduction and §4 have inconsistent exponent/sign typography; this archive does not silently repair or rely on those discrepancies as a new contract. Earlier §3 lemmas invoked there were not fully read.

I140 already treats scalar spatial coefficient variation inside the same Newton kernel, including the actual endpoint coefficient and radial-error budgets. Its §4 is not an anisotropic principal-symbol argument. I143 already warns, by a different reflected Green-kernel calculation, that positive interactions and a restricted family of line directions alone do not pay radial cap localization. Its relevant §§3.2–3.3 were read. Neither earlier archive is nominated here.

The remaining operation is a common, solution-uniform local pressure/energy estimate for K_AB retaining the nonlinear endpoint identity and the full critical energy exponent, or another complete proof avoiding it. No such estimate is proved. The calculations above support neither a full-target refutation nor a restricted replacement nomination. No freeze follows from them.
