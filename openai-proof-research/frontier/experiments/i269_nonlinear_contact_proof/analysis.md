# I269 independent proof review: nonlinear torus ball–tube contact

2026-10-12. **Verdict: PASS.** This is a first independent proof review of the complete prospective finding across I249/I253/I263. No author rebuttal, repair round, previous full-theorem gate, contribution verdict, or acceptance change is assumed.

The reviewed I263 analysis has exactly 280 lines and SHA256 d02db6dfe8b65bba3196baf2cd8de6eb4dec1ce13084696c9fe81ed2aee3fc95. The entire original I249 analytic note has SHA256 ef588588ace48958cc6f3fad4af84d01c52198ea4bff10a1e3a890cd86772413. Both match the task's detached identifiers. Both were fully read, together with the complete I253 recovery, I249 report and original parent disposition, and I263 report, reading log, authentication JSON and literature/excerpts. The verdict follows from the checks below, not from I263's declaration of completeness.

## 1. Exact theorem under review and dependency boundary

Let T=R^3/Z^3 have the unit cubic flat metric and De Giorgi perimeter P. Fix one R in (2/9,1/pi). For sufficiently small epsilon>0 put r=R-epsilon, a=4pi R^3/3 and b_epsilon=pi r^2. The admissible class is all finite-perimeter pairs E subset F a.e. with volumes a,b_epsilon. There is no smoothness, connectedness, axial symmetry, topology or graph restriction.

Define

    D_R(epsilon)=inf [P(E)+P(F)-4pi R^2-2pi r].

The reviewed conclusion is

    D_R(epsilon)/epsilon^2 -> K(R),
    K(R)=4pi R/(R+4G_R),
    G_R=R^2-(R/2)cot(1/(2R)).

The lower conclusion consequently holds for every admissible sequence of pairs and every epsilon_n down to zero, even when its boundaries have tentacles or extra components. This is one nonlinear asymptotic theorem, with the quadratic calculation and recovery as ingredients, not three prospective findings. Constants may depend on fixed R. Neither endpoint uniformity nor a claim about R=1/(2pi) is involved.

The actual pinned Theorem intro:main was freshly retrieved from
[the immutable paper.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/build/paper.tex)
and read in its full entry-file context. Its truth, including classification of all finite-perimeter equality cases, is stipulated. Its internal TeX inputs were not independently audited. The only advanced nonstipulated theorem used for the lower proof is the classical scalar improved-convergence theorem in AFM; its exact source and the legitimacy of its application are addressed in Section 5.

The remaining functional-analytic background is ordinary BV compactness/change of variables, trace and Rellich compactness on smooth compact surfaces, finite-dimensional inverse/implicit function arguments, and sphere/cylinder spectral decompositions. The paired comparison, scale estimate, drift argument and quadratic minimization are checked explicitly here.

## 2. Exact minimizers, volume branches, and limiting placement

I263 Sections 1–2 correctly use the strict branches. Since R<1/pi<1/3,

    a=4pi R^3/3 < 4pi/81.

For small positive epsilon, r>2/9 and r<1/pi, so

    4pi/81 < pi r^2 < 1/pi.

Both volumes are below 1/2. Thus the separate scalar perimeters are at least 4pi R^2 and 2pi r, respectively, with the stipulated ball and shortest axial tube equality classes.

An embedded ellipsoid with semiaxes r,r,R^3/r^2 inside the coaxial radius-r tube has precisely the required volumes. Its longest semiaxis tends to R<1/2. Its volume-preserving smooth deformation from a sphere has zero first perimeter derivative and bounded second derivative near epsilon=0. It therefore gives D_R(epsilon)<=C_R epsilon^2 without using the sharp upper recovery. The lower bound D_R>=0 comes from the two scalar profiles.

For each epsilon the direct method applies to the paired class: a bounded energy sequence has bounded separate BV norms; compactness gives L1 convergence of both sets; volume and a.e. inclusion persist; and the sum of perimeters is lower semicontinuous. It supplies an exact paired minimizer with the same prescribed volumes.

Along any sequence epsilon_n down to zero, exact minimizers have total deficit O(epsilon_n^2). Since each scalar deficit is nonnegative, each scalar perimeter tends to its respective limiting profile value. Any paired L1 subsequential limit has the limiting volumes, remains nested, and saturates both scalar profiles by lower semicontinuity. It is therefore a radius-R ball inside a radius-R shortest tube.

The equal-radius inclusion forces transverse centering. The transverse projection of the ball interior is an embedded radius-R disk; every point of that disk has a positive-length axial fiber in the ball. Any transverse portion outside the tube disk would violate inclusion on positive three-dimensional volume. Hence the two transverse disks are nested a.e. Their areas are equal, so they coincide a.e.; embedded circular boundaries identify their centers modulo the lattice. The axial ball center remains free.

A common translation and a signed coordinate permutation put the limit at B_R(0) subset C_R with axial coordinate z. These are genuine unit cubic torus isometries. No arbitrary rotation of the torus is required. One subsequence at a time is enough: choose a subsequence realizing the liminf of D_R/epsilon^2, and then extract the paired L1 limit.

Crucially, exact minimizing replacement is legitimate for the all-pair assertion:

    Delta_epsilon(A,B) >= D_R(epsilon)

for every admissible finite-perimeter pair. The proof need not show that an arbitrary original near-minimizer is a graph, nor smooth it while retaining nesting.

## 3. Two-volume correction: full rank persists for measurable pairs

I263 Lemma 1 is sound.

Choose X_1 with support in a small ambient ball meeting a sphere patch near its north pole and lying strictly inside the limiting tube. Positive outward sphere flux gives

    integral_B_R div X_1=c_1>0,
    integral_C_R div X_1=0.

The second identity uses compact support wholly inside the tube and zero total torus integral of a divergence; it does not require a divergence-free field. Choose X_2 on a tube boundary patch at a z-height in (R,1/2), with support disjoint from the limiting ball and positive tube flux. Then

    integral_B_R div X_2=0,
    integral_C_R div X_2=c_2>0.

Both patches exist for fixed R<1/2 and can be fixed before considering competitors. The volume separation of the limiting sets is positive.

Compose the two smooth ambient flows, with two parameters s. For any measurable A,B, their transported volume vector is

    V_A,B(s)=(integral_A J_s, integral_B J_s),
    J_s=det D Phi_s.

This map is C2 in s with uniform derivative bounds, because it integrates smooth bounded Jacobians over subsets of a compact unit-volume space. At the limiting pair its derivative at zero is diag(c_1,c_2). Each derivative differs from the limiting one by a bound proportional to the L1 distance of A,B from the limiting sets, plus a bound proportional to |s|. Thus a fixed L1 neighborhood and a fixed parameter neighborhood give uniform invertibility.

Writing the target residual q as the sum of the two volume errors, the inverse-function/contraction argument on a ball of radius Cq gives a parameter |s|<=Cq for q below a fixed threshold. This works for every measurable near-limit pair; no smooth boundary, exact free patch on the competitor, or strict pointwise gap on the competitor is needed. The clean patches determine the Jacobian at the limit only.

Applying the same diffeomorphism to both sets preserves a.e. inclusion. The finite-perimeter transformation formula and the uniform cofactor estimate give

    P(Phi_s(A))+P(Phi_s(B))
       <= (1+C|s|)[P(A)+P(B)].

For bounded total perimeter the added cost is at most C M q. Negative flow parameters pose no difficulty. This construction is independent of the regularity subsequently obtained.

There is no hidden support exclusion: the correcting flow may intersect the scalar comparison ball or move sets outside it. The corrected pair competes in the original global paired minimization problem, where such a change is permitted. The intermediate scalar competitor H alone has the local-support condition. Requiring the corrected pair to agree outside the ball would be an additional, unnecessary constraint.

## 4. Lattice comparison and every quantifier of scalar quasiminimality

I263 Lemma 2 obtains the needed unrestricted scalar property.

Perimeter submodularity

    P(A intersection B)+P(A union B)<=P(A)+P(B)

is valid on the torus for finite-perimeter sets. The supplied strict BV convolution argument proves it: for the smooth scalar approximations the gradients of min and max sum in norm to the original gradient norms a.e.; L1 convergence and lower semicontinuity then give the inequality. This is a proof of a BV lattice inequality, not pair-preserving approximation in the asymptotic problem.

Fix an arbitrary finite-perimeter H with H triangle E_n compactly contained in a comparison ball. If P(H)>=P(E_n), the desired scalar inequality already holds. Otherwise P(H)+P(F_n) is bounded by the original pair's total perimeter M. Let

    A=H intersection F_n, B=H union F_n.

They are nested and their total perimeter is at most P(H)+P(F_n). The exact pair-change identity is

    |A triangle E_n|+|B triangle F_n|=|H triangle E_n|.

Pointwise verification: at the original nested states (E,F)=(0,0),(0,1),(1,1), changing H from E changes respectively B alone, A alone, A alone; leaving H=E changes neither. Thus there is no multiplicity loss in the identity. In particular each target-volume residual is bounded by its corresponding L1 change, and the sum of volume errors is at most |H triangle E_n|.

For sufficiently small comparison radius rho, its ball volume bounds that last quantity. Combined with E_n,F_n tending in L1 to the limit, this puts A,B in the fixed correction neighborhood and below its fixed error threshold, uniformly in n,H,ball center. The common correction costs at most Lambda |H triangle E_n|. Global paired minimality and lattice submodularity yield

    P(E_n)+P(F_n)
      <=P(H)+P(F_n)+Lambda |H triangle E_n|,

and hence

    P(E_n)<=P(H)+Lambda |H triangle E_n|.

No condition H subset F_n has been imposed; H can cross F_n.

For arbitrary outer H use A=E_n intersection H, B=E_n union H. Pointwise checking the same nested states gives total pair L1 change exactly |H triangle F_n|. The high-perimeter competitor is again automatic, and otherwise the sum is bounded. Therefore the analogous scalar inequality holds for F_n with the same uniform Lambda.

Choose a fixed rho_0 below the injectivity radius and small enough for the correction neighborhood/error threshold. For rho<rho_0 the scalar inequalities imply

    P(E_n)<=P(H)+Lambda (4pi/3)rho^3

and its outer analogue. For every rho>=rho_0 use

    P(E_n)<=M<=P(H)+(M/rho_0^3)rho^3,

and similarly for F_n. Increasing one constant omega covers all balls and both interfaces. Only a tail of the sequence is needed for improved convergence. Competitors of arbitrarily large perimeter were included, since their inequalities are trivial rather than silently omitted.

This proves the precise all-ball AFM property using the global torus perimeters. It also avoids an inappropriate ordinary equal-tension cluster regularity theorem: contact in this sum counts twice, and no such cluster identification is needed.

## 5. External AFM theorem: checked contract and legitimate use

The exact [author-hosted AFM final PDF](https://cvgmt.sns.it/media/doc/paper/540/Acerbi-Fusco-Morini.FINAL.pdf) was retrieved afresh. Its full-PDF SHA256 is 7805d5a0b9daf3873a199bbfe23d4064964fc2e72701be6d45303549028d4c72. Full text extractions of PDF pages 7 and 22 match I263's recorded bytes. Definition 2.5 concerns finite-perimeter local comparisons in every ball, without a volume constraint. Theorem 4.2 assumes common omega, bounded perimeters and L1 convergence to a C2 set, and supplies eventual global normal graphs small in C^{1,alpha}, alpha<1/2.

All these hypotheses are now established independently: unit torus, N=3; the uniform all-ball inequality from Section 4; bounded scalar perimeters; and C-infinity ball and tube limits. The theorem applies separately to E_n and F_n. Tangency of their limit boundaries causes no missing hypothesis, because scalar quasiminimality has already been proved for each.

AFM states Theorem 4.2 without a proof there and attributes it to classical regularity. Using it as an established external regularity theorem is legitimate; it is not a stipulated OpenAI result or a new lemma justified solely by I263's quotation. The bibliographic attribution was read, but Almgren/Tamanini and the other underlying works themselves were not read. No claim to reprove them is made.

## 6. Whole graphs, occupied sides, and reference centering

The global graph conclusion applies to the whole regular boundary, up to choosing regular representatives. It excludes extra boundary components in the exact minimizers. A small radial graph of the sphere bounds the near-ball side; a small radial graph of the tube bounds its disk-like radial side at every z. L1 convergence selects these occupied sides, rather than their complements. The graph surfaces separate the torus into the relevant inside and outside components; no additional unobserved components can be assigned without another boundary.

Changing the reference cylinder from radius R to r_n merely adds epsilon_n to its graph height. The graph and its C1 norm still tend to zero.

For a C1-small graph, re-expressing its unchanged boundary over a nearby reference center is well-defined by the normal/radial projection. Its translation-moment map is C1 in the finitely many center parameters. At the zero graph its derivative is the negative normal-component Gram matrix:

    sphere: integral_S_R omega_i omega_j dS=(4pi R^2/3)delta_ij,
    tube: integral_Z_r (cos theta,sin theta)_i
                        (cos theta,sin theta)_j dS=pi r delta_ij.

These matrices are invertible uniformly near r=R. The implicit function argument therefore imposes the exact three sphere and two transverse cylinder orthogonalities. C1-smallness suffices for continuity of these parameter derivatives; no higher regularity of the graphs is being assumed. Axial tube translation has zero normal component and is correctly not assigned a separate moment condition.

Only the reference centers change. The actual sets are not translated independently, so actual inclusion is retained. A subsequent common torus translation makes the tube reference center transverse zero and the sphere reference center axial zero. The remaining relative transverse center h_n tends to zero, and is kept in the contact inequality. Axial tube profiles are simply reparameterized periodically under this common translation.

## 7. Exact-volume energy expansions and the epsilon scale

For the sphere graph of height psi over S_R the exact volume identity is

    integral_S_R [psi+psi^2/R+psi^3/(3R^2)]dS=0.

Its exact area density is

    (1+psi/R)^2
       sqrt(1+|grad_S psi|^2/(1+psi/R)^2).

After elimination of the linear term by the volume equation, its deficit is

    Q_B(psi)/2 + Rem_B,
    Q_B(psi)=integral_S_R (|grad psi|^2-2psi^2/R^2)dS.

The cubic volume error is bounded by C||psi||infinity integral psi^2. The square-root error is bounded by C||grad psi||infinity^2 integral |grad psi|^2. Thus |Rem_B|=o(1)||psi||H1^2. This bound does not assume a uniform bound on normalized gradients.

For the tube graph eta over Z_r the exact volume identity is

    integral_Z_r [eta+eta^2/(2r)]dS=0,

and area density is

    (1+eta/r)sqrt(1+eta_z^2+eta_theta^2/(r+eta)^2).

The same expansion gives Q_C,r(eta)/2 with potential -eta^2/r^2 and a remainder o(1)||eta||H1^2. The estimates are uniform for r near the fixed positive R; coefficient changes from Z_r to Z_R are o(1) on bounded normalized H1 functions.

The centered sphere spectrum is [l(l+1)-2]/R^2. After the mean and l=1 translations, l>=2 gives H1 coercivity. The cylinder spectrum is

    (m^2-1)/r^2+(2pi k)^2.

After the mean and m=+/-1,k=0 translations, every eigenvalue is positive uniformly near R, since R>2/9>1/(2pi). Comparing each remaining eigenvalue with one plus its Laplacian eigenvalue gives H1, rather than just L2, coercivity.

Exact volumes do not make the graph means exactly zero. They bound those means by C||graph||L2^2. The squared constant-mode contribution is therefore at most C||graph||L2^4=o(1)||graph||H1^2, using unscaled C1-smallness. Constants are orthogonal to the centered translation fields. Consequently the negative constant direction and both Taylor remainders can be absorbed into the positive spectral gaps. Each scalar deficit bounds c_R times its graph H1 norm squared.

Since total deficit is O(epsilon_n^2),

    ||psi_n||H1+||eta_n||H1=O(epsilon_n).

Set u_n=psi_n/epsilon_n and v_n=eta_n/epsilon_n on fixed reference surfaces. Weak H1 compactness and strong L2 compactness give u,v; the exact volumes imply zero means in the limit, since integral psi_n and integral eta_n are O(epsilon_n^2). Both equatorial trace maps are bounded H1 -> H^{1/2} on the circle, with compact embedding into L2. Their traces therefore converge strongly in L2 on a further subsequence.

The negative potential terms converge by full-surface strong L2, while the gradients pass by weak lower semicontinuity. The normalized remainders tend to zero by the paid scale bound. This yields

    liminf D_R(epsilon_n)/epsilon_n^2
       >= [Q_B(u)+Q_C(v)]/2.

Concentration of normalized gradient energy is permitted and can only increase the lower limit. It is not excluded by an unjustified uniform Taylor argument.

## 8. Nonlinear inclusion, drift and trace composition

At the inner graph equator its actual position is (y_n(theta),0), where

    y_n=h_n+(R+psi_n(theta,0))e_theta.

For large n this lies in an embedded transverse chart and has positive radius. Define phi_n=arg y_n. Differentiating the argument gives, with a_n=R+psi_n(theta,0),

    phi_n'=[a_n^2+a_n(h_n dot e_theta)
                    +a_n'(h_n cross e_theta)]/|y_n|^2.

In particular phi_n-id tends to zero uniformly and

    ||phi_n'-1||infinity
       <=C_R |h_n|(1+||psi_n||C1).

It is a circle diffeomorphism for large n, with uniformly controlled Jacobian. Radial variation by itself causes no angular change when h_n=0.

The regular representatives retain inclusion in the needed closed sense: if an inner interior point lay outside closure F_n, open neighborhoods would violate a.e. inclusion on positive volume. Taking closures covers inner boundary points. The occupied tube side from Section 6 gives

    |y_n|<=r_n+eta_n(phi_n(theta),0).

Since |y_n|>=y_n dot e_theta, this implies the exact inequality

    epsilon_n+h_n dot e_theta+psi_n(theta,0)
       <=eta_n(phi_n(theta),0).

Both unscaled traces are O(epsilon_n) in L2; composition with phi_n has bounded L2 norm by its controlled Jacobian. On the half-circle with h_n dot e_theta>=0, the positive left-hand affine term has L2 norm at least c|h_n|, while the right-hand trace difference is O(epsilon_n). Therefore |h_n|=O(epsilon_n). There is no guessed O(|h_n|^2) geometric error to absorb.

Extract h_n/epsilon_n -> d. If f_n is the tube trace and f_n -> f strongly in L2, then

    ||f_n composed phi_n-f||L2
       <=C||f_n-f||L2+||f composed phi_n-f||L2 ->0.

The last convergence follows by smooth approximation of the fixed L2 function f, uniform Jacobian bounds and uniform phi_n -> id. It does not require bounded derivatives of the normalized traces or a composition estimate at the critical H^{1/2} norm.

The limiting inclusion is

    v(theta,0)-u(theta,0)>=1+d dot e_theta

a.e., since the positive cone is closed in L2. Add the spherical translation field tau_d(omega)=d dot omega_transverse to u. It has zero mean and solves the sphere Jacobi equation. By weak integration by parts Q_B(tau_d,w)=0 for every H1 w. Thus u_tilde=u+tau_d has unchanged energy and

    v(theta,0)-u_tilde(theta,0)>=1.

This operation is on the limiting linearized functions; it does not independently move the actual sets. Its sign is correct. The preserved drift modes therefore enter and are removed only after actual inclusion pays their effect.

## 9. The quadratic minimum over all angular modes

The zero-mean sphere form is nonnegative, with l=1 translation kernel. The zero-mean cylinder form is nonnegative, with precisely the two transverse translation modes as kernel in the present R interval. Common angular averaging preserves the obstacle and both means. Orthogonal Fourier/spherical harmonic decomposition shows that every discarded angular block has nonnegative energy. Averaging is an operation on functions on the reference surfaces, not an assertion that arbitrary rotations are ambient torus symmetries or a nonlinear symmetrization of sets.

After averaging, u=u(t), v=v(z), with t=cos(phi). Write A=u(0), D=v(0). The obstacle becomes D-A>=1.

The spherical test function u_A=A(1-2|t|) has zero mean and

    Q_B(u_A)
      =2pi integral_-1^1 [(1-t^2)(u_A')^2-2u_A^2]dt
      =8pi A^2.

On each hemisphere its Jacobi operator equals the same constant -2A/R^2. For h=u-u_A, total mean and equatorial trace vanish. The interface boundary term and the constant interior pairing vanish, so Q_B(u_A,h)=0. Nonnegativity of Q_B(h) proves Q_B(u)/2>=4pi A^2. Axial translation is a harmless zero-energy direction with zero equatorial trace.

For mean-zero period-one cylinder functions, L=-d^2/dz^2-R^{-2} is coercive because 2pi>1/R. The displayed Green function

    g_R(z)=R^2-R cos((|z|-1/2)/R)/(2sin(1/(2R)))

has zero mean: the cosine integrates to 2R sin(1/(2R)). Its derivative is zero at both periodic endpoints, its derivative jump at zero is -1, and Lg_R=-1 away from zero. Thus Lg_R=delta_0-1 distributionally. Testing by mean-zero H1 functions gives the energy pairing w(0). In particular

    G_R=g_R(0)=energy_L(g_R)>0,

because g_R is nonzero and L is positive on the mean-zero subspace. Energy Cauchy–Schwarz yields

    Q_C(v)/2>=pi R D^2/G_R,

with equality at v=Dg_R/G_R. The circumference factor is 2pi R and the total quadratic functional includes a factor 1/2; no period-two convention is used.

Minimizing

    4pi A^2+(pi R/G_R)D^2,  D-A>=1

gives equality at D-A=1,

    A_*=-R/(R+4G_R), D_*=4G_R/(R+4G_R),

and minimum 4pi R/(R+4G_R)=K(R). These H1 profiles attain the quadratic minimum. This independently verifies I249's calculation for every angular mode, including all translation kernels, and supplies the lower bound for the limits obtained in Section 8.

## 10. Separate verification of the full I253 upper recovery

The recovery is a real available argument, not an unpaid item from the earlier I249 disposition. Both exact minimizing profiles are Lipschitz and axial. Smooth u_* only near the equator, retaining pole smoothness; smooth v_* periodically. Subtract the separate means. These particular mollifications converge uniformly and in H1, so their trace gap tends to one. For each fixed gamma>0, multiply a sufficiently good smooth approximation by the common factor that makes its trace gap exactly 1+gamma. Its energy tends to (1+gamma)^2 K(R).

Fix one such smooth U,V. The sphere radial radius R+epsilon U+s and tube radius R-epsilon+epsilon V(z)+t have volume derivatives in s,t at epsilon=0 equal to 4pi R^2,2pi R. Their zero first-order means give s,t=O(epsilon^2) via the implicit function theorem. Thus both prescribed volumes are matched exactly. Radii remain positive; the tube is below injectivity radius; the sphere fits inside an embedded chart for small epsilon.

At latitude tau on the inner graph, its actual axial coordinate is z_epsilon=(R+epsilon U(tau)+s)tau. The containment margin equals

    R[1-sqrt(1-tau^2)]
      +epsilon[-1+V(R tau)-U(tau)sqrt(1-tau^2)]
      +O(epsilon^2)

uniformly on [-1,1] for this fixed smooth pair. This follows from the bounded derivative of V and the O(epsilon^2) volume corrections. The first-order bracket is gamma at tau=0, hence positive on a fixed strip around zero. Outside that strip the zeroth-order margin is uniformly positive. Therefore the whole inner boundary is in the tube for sufficiently small epsilon.

This implies inclusion of the whole inner region: at each z the tube is a centered disk, and any maximal transverse radius of the compact inner slice is attained on its three-dimensional boundary; an interior maximizer could be increased radially. Equivalently, the small fixed smooth sphere deformation is strictly convex for sufficiently small epsilon. Thus boundary containment is sufficient here, without asserting that it suffices for arbitrary pairs.

The exact-volume expansions of Section 7 give the quadratic energy of U,V at order epsilon^2, with the cylinder reference change from r to R contributing only o(epsilon^2). For each fixed approximation this bounds the same limsup D_R/epsilon^2. One may then improve the approximation and let gamma down to zero. No estimate uniform in smoothing scale, exchange of limits or unsupported direct use of the kinked H1 graphs is needed.

Consequently limsup<=K(R). Section 9 applied to the exact paired minimizing subsequence yields liminf>=K(R). Every admissible original pair has no smaller energy than the exact minimum. The complete all-finite-perimeter asymptotic is justified.

## 11. Disposition and limits of the review

No substantive mathematical gap or required repair remains in this proof under the stipulated pin and the classical AFM input. The small occupied-side and center-map details made explicit above are consequences of the stated global graph conclusion and C1-smallness, not additional assumptions or repairs to the theorem.

The main attacks were unrestricted competitors and all-ball quantifiers; measurable-set correction without a clean actual patch; correction-flow support; extra components and complement-side choices; varying radius and negative means; reference translations versus actual motion; relative transverse drift; trace concentration and composition; nonaxial modes; periodic Green normalization; and exact-volume nonlinear recovery. They are resolved as detailed above.

This PASS is a proof verdict only. It does not assess worldwide novelty or priority, and does not change the supplied ten accepted findings toward twenty. No live I266/I268 material, other sibling work, shared index, acceptance ledger, history replay, snapshots, research code/tests/scans, subordinate agents, staging, commits or publication was used. Only the authorized I269 outputs and fully read primary excerpts were written. Exact read extents and provenance are in reading-and-failures.md and input-authentication.json; the latter's own SHA256 is detached at handoff.
