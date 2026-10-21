# PREFREEZE calculation: local affine pressure completion and the full-box gap

No theorem is frozen and no nominee is submitted. This is a feasibility calculation within SOURCE376, after the read operative box, normal-compensation, clock and detector constructions. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and its proofs are stipulated true. The finite algebra below is not an independent mathematical or contribution grade.

## 1. The comparison actually paid

The October6 box manuscript, geometry.tex, proves a compactly supported incompressible extension of every finite list of positive diagonal determinant-one maps between separately disjoint rational solid boxes. It first expands centers with shapes fixed, then changes shapes, evacuates to parking, follows obstacle detours, delivers and contracts centers. It acts on neighborhoods of the ENTIRE closed boxes, with effective positive margins; source-target overlap is allowed. balanced.tex supplies the complete length-balanced three-stack table, inverse separation, exact radix maps and all-time cube observer. The general Euclidean residual has pressure zero; its force is not asserted solenoidal. Its own five pressure/velocity comparison classes remain distinct.

The reciprocal torus shears and the stronger sheet construction already achieve direct solenoidal forcing with zero pressure by temporal separation of transverse fields. General planar area changes are compensated in the normal coordinate. The full-box and invariant-plane alternatives are not merely assertions on an encoded orbit. In particular, a sheet may return to its plane while its surrounding thickness changes: no common invariant positive-thickness neighborhood follows.

The eventual-stationary companion supplies a full planar processor and an autonomous mean-zero spatial clock, unit speed throughout the tracked corridor. Its finite-time derivative bounds, inverse-flow bounds, compiler and all-time exclusion were read. It already pays periodic forcing from time zero, a fixed particle, and stationary forcing after startup. The logarithmic/root-clock companions preserve material reachability when the logical clock is onto, and recompute the residual at the fixed physical viscosity. These are separate force choices, not a simultaneous periodic-and-decaying claim.

The complete compact and expanding-array velocity-detector proofs were read. The compact detector uses widths b_n=10^-6(2R)^-n and burst lengths delta_n=[100(1+D_n)]^-1, D_n=2Cb_n^-2(1+nL)R^(3n). Its error is at most 2 delta_n D_n<1/50, and its old mass is controlled by heat waiting. The force's derivatives are only bounded on each finite time interval. The expanding-array detector has globally bounded force derivatives but its spatial support grows; its loss budget is nu C_*[R_0^-2+sum T_n/R_n^2]<1/24. Its scalar has diffusion tails, verified in C_0 intersect L1 and the precise Sobolev comparison class. Neither construction promises uniformly bounded all-time derivatives together with one compact support for a positive velocity threshold. Slowing a particle clock cannot simply be substituted into those scalar estimates while leaving viscosity and thresholds unchanged.

The rapid-decay companion's addressed curls, including all-address one-step lookup, retained history, unit physical steps, shrinking signal and exact nonhalt plane, were read in full. Original I80 sections3–8 already supply pressure-balanced rotation gates and compact solenoidal rapid point computation. Its full C80 statement is retained unchanged. No intersection of those old point-computation properties is being renamed here. The current question is whether compact pressure can also be made compatible with general whole-box affine instruction geometry.

Primary comparison is bounded but operative: CMPP's arXiv v2 Proposition6.1 (published numbering differs) gives shrink/transport/expand followed by Moser correction; it pays a volume/area-preserving endpoint extension, not compact pressure throughout an assigned isotopy. Brandolese–Meyer's higher-moment conditions are prior work. Gavrilov and Constantin–La–Vicol produce genuinely compact stationary Euler fields through localizability u dot grad p=0, with restricted stream-function geometry; their existence is credited. CMP's Euclidean Beltrami computation and DGMP's metric-deformed harmonic steady construction do not retain the fixed Euclidean geometry, zero initial velocity, support and control interface of the present problem. Their deeper foundations have the reading limits recorded separately.

## 2. Exact finite exterior spectrum of a radially localized affine germ

Fix a constant v in R3 and a real 3 by 3 matrix A with tr A=0. Put y=x-c, r=|y| and omega=y/r. Let chi be a smooth radial cutoff, constant one near zero and zero outside a ball. Define

    U(y)=curl{chi(r)[(v cross y)/2+((Ay) cross y)/3]}.

This is the source's affine curl potential with a radial cutoff. It is smooth, divergence free, and equals v+Ay on the inner plateau. At r>0, with q(omega)=omega dot A omega,

    U = a v + b(v dot omega)omega + c1 A omega + d q(omega)omega,
    a=chi+r chi'/2,   b=-r chi'/2,
    c1=r chi+r^2 chi'/3,   d=-r^2 chi'/3.

The identity follows from curl(G cross y)=2G-y div G+(y dot grad)G and the vector triple product. No assumption that A is symmetric is needed. Near zero the original curl formula avoids singular coordinates.

Let H_l be a homogeneous harmonic polynomial of degree l, and define

    M_U(H_l)=integral_R3 U_i U_j partial_ij H_l.

Degrees0 and1 vanish identically. For every l>4 the displayed radial decomposition gives M_U(H_l)=0. Here is the full degree argument, rather than a low-degree numerical test. The components of D^2 H_l are harmonic homogeneous polynomials of degree l-2. A homogeneous polynomial of degree k restricted to the sphere is a sum of harmonics of degrees k,k-2,..., so it pairs to zero with a harmonic of higher degree. This decomposition follows inductively by subtracting |x|^2 times a polynomial to remove the Laplacian; the coefficients in Delta(|x|^(2j)H_m)=2j(2m+2j+1)|x|^(2j-2)H_m are nonzero.

For products with no explicit omega_i or omega_j, the coefficients of D^2H_l have degrees0,1 or2, allowing only l<=4. For one such factor use

    omega_j partial_ij H_l=(l-1)partial_i H_l.

The coefficient paired with the harmonic gradient has degree at most3, again allowing l<=4. For two such factors use

    omega_i omega_j partial_ij H_l=l(l-1)H_l.

The remaining coefficients have degree at most4. Thus all terms vanish for l>4. More precisely translation squared contributes only degree2; strain/rotation squared contributes degrees2,4; their cross terms contribute degree3. Parity excludes the opposite degrees.

For the decaying Newtonian pressure p with -Delta p=partial_i partial_j(U_iU_j), the exterior harmonic expansion is determined by these moments, by two integrations by parts. The source is smooth and compactly supported. Outside any ball containing its support, the Newtonian expansion and its derivatives converge uniformly on compact exterior subsets. Consequently cancellation of the 5+7+9=21 moments in degrees2,3,4 cancels the ENTIRE exterior pressure for this restricted radial-affine class. This is not an all-order completion of an arbitrary rectangular cutoff or an arbitrary smooth core.

## 3. A finite positive-cone reduction for concentric shell corrections

For a shell cutoff chi_epsilon(r)=psi((r-1)/epsilon), with a fixed nonzero smooth bump psi in (-1,1), use the same potential with v=e1 and A=diag(1,-1,0). This field vanishes on its inner ball. Its dominant term is chi_epsilon' times

    T(omega)= [e1-omega_1 omega]/2
             +[A omega-(omega_1^2-omega_2^2)omega]/3.

For each H_l, epsilon M(H_l) tends, as epsilon decreases to zero, to

    (integral psi'^2) integral_S2 T_i T_j partial_ij H_l dS.

The lower chi and chi chi' terms vanish after multiplication by epsilon. Changing variable r=1+epsilon z proves this limit, with an effective error from the finite polynomial radial factors and a fixed compact interval. For a shell centered instead at radius1+c_j epsilon with fixed c_j, the same limit holds. Hence finitely many different radial shells can have disjoint supports and the same limiting moment vector. This is essential: rotating fields on an overlapping shell would introduce nonlinear cross terms.

The rational angular calculation in affine_moments.py uses normalized sphere measure and obtains

    H2=x^2-z^2:                 167/630,
    H3=x^3-3xy^2:               52/105,
    H4=x^4-6x^2y^2+y^4:        32/135.

Those three checks alone would NOT prove a full cone assertion. The stronger finite calculation in shell_cone.py constructs the 60 rotations obtained from the 120 unit quaternions of the 600-cell, using exact arithmetic in Q(sqrt5). It computes a rational harmonic basis in degrees2,3,4 by a Laplacian kernel calculation, all 60 rotated moment columns, and exact elimination. The 21 by 60 matrix has rank21 and its column sum is zero. The complete matrix, basis, rotations and pivot columns are retained in notes/shell-cone-certificate.json. There is no floating-point rank decision.

The precise algebraic implication is elementary. If a matrix C has full row rank and C 1=0, choose a right inverse J; every b has coefficients Jb+K 1, positive for sufficiently large K. Thus the positive cone of these angular columns is the whole 21-dimensional moment space. It also survives a sufficiently small perturbation of the columns: choose an invertible21-column block, retain its inverse as J_epsilon, and set

    lambda_epsilon = 1 - J_epsilon C_epsilon 1.

Then C_epsilon lambda_epsilon=0 and lambda_epsilon tends to1, hence is strictly positive for small epsilon. The actual normalized shell matrix C_epsilon converges to the computed matrix times the common positive radial integral. Uniform effective error bounds and an inverse-matrix bound reduce choosing a valid epsilon to finitely certifiable strict inequalities. This is a concrete finite-dimensional reduction; this round has not instantiated a shell width, the bump's integral enclosures, or an effective inverse norm for a full fluid program.

Given such a certified matrix, cancellation of a target vector m uses positive coefficients q with C_epsilon q=-m. Since C_epsilon=epsilon times the actual shell moments, the correcting shell amplitudes are sqrt(epsilon q_j). Their supports are disjoint from each other and from the affine core, so U tensor U adds without cross terms. Each field still has no moments above degree4. The moment criterion would then give compact pressure. The coefficients may be large; no small norm or uniform efficiency is asserted.

For one fixed spatial pulse V and its compact pressure P, multiplication by a smooth time amplitude a(t) gives the exact compatible expressions

    U=aV,   p=a^2 P,
    f=a'V+a^2[(V dot grad)V+grad P]-nu a Delta V.

In particular div f=0, the physical viscosity is unchanged, and flat a gives zero time collars. For a translated template, its time derivative also contains -a c'(t) dot grad V; this term is divergence free. These identities are paid residual calculations, not the missing routing operation. For variable affine data, blindly taking pointwise square roots of vanishing coefficients is not a proof of smooth time dependence; fixed-direction pulse scheduling avoids that particular issue but still needs the geometric construction below.

## 4. Attempted strongest assembly, and what remains unpaid

The source's compact box potential uses rectangular collars precisely to leave every other current box fixed. Replacing one such cutoff by a centered spherical plateau and correction shells need not preserve that property. For example two long thin parallel boxes can have a very small positive separating coordinate gap while their centered enclosing balls overlap widely. The source allows this situation. Neither its supplied padding nor the new finite angular matrix gives a sphere-and-shell clearance margin. Shifted balls and a different schedule may help; no impossibility theorem about them is asserted.

The source's outward center expansion cannot be invoked to solve this initial clearance problem for free: its implementation itself uses separate rectangular affine neighborhoods. Parking works once departure and arrival can be done without touching other occupied boxes, but that is part of the unproved extension. Normal compensation permits planar compression by expanding in the normal direction; it pays incompressibility, not the compactness of pressure after a general localized deformation. Likewise the primary Moser correction provides an endpoint area constraint and does not make the nonlinear pressure local at every intermediate time.

A simultaneous partition into ball-supported pieces reintroduces cross stresses U_i U_j in overlap regions. Sequentializing the pieces removes those instantaneous cross terms but changes the composed flow. A splitting approximation therefore needs an exact, effective smooth limiting construction, with control of every spatial/time derivative, compact support, held boxes, and all-time detector. No such limiting construction is proved here. This is not a theorem that fragmentation cannot work.

The alternate route of keeping the original full rectangular motion and canceling its pressure outside all occupied boxes retains arbitrarily high angular moments. The21-dimensional calculation does not close I80's general infinite-moment problem. One would need a convergent effective correction with all time/spatial derivative bounds, positive square-root margins, and no interference with the complete tracked geometry. The old finite-degree completion is not silently promoted to that conclusion.

The detector comparison does not repair this gap: the velocity detector's extra triangular scalar structure would itself have to survive the new pressure/force design. A slow clock preserves the material event but changes diffusion per unit logical time. Uniform boundedness, one fixed support, zero pressure, direct solenoidal force, periodicity, stationarity and rapid decay cannot all be combined merely by collecting separate source headlines.

Therefore the paid new calculation is a finite exterior-spectrum reduction for radial affine germs, together with an exact positive angular cone certificate and its perturbative disjoint-shell reduction. It does not establish an additional full forced-fluid-computation theorem. No weaker replacement of C80, no new compact-solenoidal point theorem, no unforced/robust/fixed-force/analytic bridge, and no conditional bridge is nominated. The next genuinely unpaid construction is an exact compact-pressure realization of the source's unrestricted separately-disjoint whole-box instruction geometry, with its finite compiler and every-time observer intact. Reading limits and possible other methods prevent an exhaustion or priority claim.
