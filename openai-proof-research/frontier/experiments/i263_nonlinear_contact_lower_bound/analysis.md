# I263: nonlinear lower passage for nested ball–tube contact

2026-10-12. Research proof, without an acceptance or contribution verdict. The stipulated OpenAI pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. No upstream truth audit is undertaken. All new lemmas below are proved here. The external regularity input is the precise AFM Theorem 4.2, with its Definition 2.5, read from the author-hosted final paper; its hypotheses are checked below.

## 1. Statement and dependencies

Let T=R^3/Z^3, with unit flat metric, unit volume and De Giorgi perimeter P. Fix R in (2/9,1/pi). Set a=4pi R^3/3, r=R-epsilon and b_epsilon=pi r^2. For all sufficiently small positive epsilon, the pinned Theorem `intro:main` of family 354 gives the separate minima 4pi R^2 and 2pi r, with only embedded balls and shortest axial tubes as equality cases at these volumes.

For nested finite-perimeter sets of these exact volumes put

    Delta_epsilon(E,F)=P(E)+P(F)-4pi R^2-2pi r,
    D_R(epsilon)=inf Delta_epsilon(E,F).

**Claim proved in this note:**

    liminf_{epsilon down to 0} D_R(epsilon)/epsilon^2 >= K(R),
    K(R)=4pi R/(R+4G_R),
    G_R=R^2-(R/2)cot(1/(2R)).                         (1)

Consequently, for EVERY sequence epsilon_n down to zero and EVERY admissible finite-perimeter pair (A_n,B_n),

    liminf Delta_epsilon_n(A_n,B_n)/epsilon_n^2 >= K(R).       (2)

Combining (1) with the verified I253 recovery construction proves the full limit D_R(epsilon)/epsilon^2 -> K(R). I249's quadratic calculation and I253's recovery are checked in Sections 8–9 rather than taken as premises. This is a research proof for independent review, not an accepted-finding update or a claim of worldwide novelty.

The critical new step is an inclusion-preserving lattice comparison plus a common two-volume correction. It proves uniform scalar quasiminimality of both interfaces of EXACT paired minimizers. Only after this paired argument do we use the classical scalar improved-convergence theorem. We do not assert that arbitrary near-minimizers are smooth, and do not independently approximate two sets. Exact paired minimizers have no greater energy than any given pair, which suffices for (2).

## 2. Compactness and the exact-minimizer reduction

For each sufficiently small epsilon the admissible class is nonempty, for example by the embedded volume-preserving ellipsoid inside the radius-r axial tube from I249. The direct method on the compact torus supplies an exact minimizer (E_epsilon,F_epsilon): perimeter bounds give BV compactness; volumes and inclusion pass to L1 limits. An explicit smooth ellipsoid competitor gives D_R(epsilon)=O(epsilon^2), independently of the sharp recovery. To check that bound, use semiaxes r,r,R^3/r^2; its volume is a, it lies inside the tube, and its smooth area has zero first variation and finite second variation at r=R. Its largest semiaxis stays below 1/2 for small epsilon because R<1/2.

Consider any sequence epsilon_n down to zero and its exact minimizers. Each scalar deficit is nonnegative by the stipulated profile, and their sum is O(epsilon_n^2). Hence, after a subsequence,

    E_n -> E_0, F_n -> F_0 in L1,
    P(E_n) -> 4pi R^2, P(F_n) -> 2pi R.

Lower semicontinuity, the limiting volumes and the exact equality classification imply that E_0 is a radius-R ball and F_0 a radius-R shortest tube. They remain nested.

The ball center must lie on the tube axis. Indeed, projection to the transverse two-torus of the ball interior is an embedded radius-R disk. Inclusion in F_0 implies inclusion of this disk in the tube's transverse disk of the same radius. Equal areas imply equality a.e.; their embedded circular boundaries force equal centers modulo the lattice. Axial ball position is unrestricted. The isometries needed to put the limit in standard position are a common torus translation and a signed coordinate permutation. No arbitrary Euclidean rotation is used as a torus symmetry. Thus take

    E_0=B_R(0), F_0=C_R={x^2+y^2<R^2}, axis z,

with z periodic of length one. R<1/2 makes all transverse disk calculations local Euclidean calculations.

The rest of the proof is carried out on this subsequence. Every sequence has such a subsequence whenever one needs to realize its lower limit; this proves (1) once the lower bound is established here.

## 3. A common-flow two-volume correction, without regularity assumptions

Here is a uniform correction lemma suitable for finite-perimeter pairs.

**Lemma 1.** There are a neighborhood U of (B_R,C_R) in L1 x L1, positive constants delta,C, and smooth torus diffeomorphisms Phi_s, s in R^2 near zero, such that: if A subset B, (A,B) belongs to U, P(A)+P(B)<=M, and target volumes (a',b') satisfy

    q=||A|-a'|+||B|-b'|<delta,

then some s has |s|<=Cq, the pair (Phi_s(A),Phi_s(B)) is nested, has volumes (a',b'), and

    P(Phi_s(A))+P(Phi_s(B)) <= P(A)+P(B)+C M q.         (3)

The constants can be fixed for a prescribed finite M. There is no requirement that A or B have a smooth boundary, be clean on a correction patch, or satisfy strict inclusion there.

**Proof.** Choose a small patch of the sphere around its north pole, contained strictly inside C_R and meeting its sphere boundary. Choose a smooth vector field X_1 supported in a small ambient ball around that patch, with positive flux across the sphere. Then

    int_{B_R} div X_1 = c_1>0, int_{C_R} div X_1=0.

The latter holds because the support is entirely inside C_R and the integral of a compactly supported divergence over the torus is zero. Choose X_2 supported near the tube boundary at an axial height strictly between R and 1/2. Its support is disjoint from the ball, and its outward tube flux is positive. Thus

    int_{B_R} div X_2=0, int_{C_R} div X_2=c_2>0.

Such a height exists because R<1/pi<1/2. Let Phi_s be the composition of the two smooth flows, Phi_0=id. For any measurable A,B its volume map is

    V_{A,B}(s)=(int_A det D Phi_s, int_B det D Phi_s).

It is C2 in s, with uniformly bounded second derivatives independently of A,B. Its derivative at the limiting pair and s=0 is diag(c_1,c_2). Integrals of the smooth Jacobian and its derivatives vary uniformly continuously with A,B in L1. Choose U and a fixed parameter neighborhood so these derivatives remain uniformly close to that invertible matrix. A quantitative inverse-function argument now gives a parameter s with V_{A,B}(s)=(a',b'), |s|<=Cq: equivalently apply the contraction map s -> s+diag(c_1,c_2)^{-1}[(a',b')-V_{A,B}(s)] on a ball of radius Cq. Shrinking delta puts this ball in the parameter neighborhood.

Every Phi_s is applied to BOTH sets, so inclusion is preserved exactly. The finite-perimeter change-of-variables formula and sup|cof D Phi_s-I|<=C|s| give

    P(Phi_s(H)) <= (1+C|s|)P(H)

for either H=A,B. This proves (3). Notice that we used volume integrals of smooth Jacobians, not boundary differentiability of A,B. QED.

## 4. The paired lattice comparison pays scalar quasiminimality

**Lemma 2 (paired regularity reduction).** Let (E_n,F_n) be exact minimizers of P(E)+P(F) among nested pairs of their prescribed volumes. Suppose E_n -> B_R, F_n -> C_R in L1 and sup_n[P(E_n)+P(F_n)]<infinity. Then, for all large n, BOTH E_n and F_n are omega-minimizers in the sense of AFM Definition 2.5, with the SAME constant omega independent of n.

**Proof.** Recall the perimeter lattice inequality

    P(A intersection B)+P(A union B)<=P(A)+P(B).        (4)

For completeness, convolve the two characteristic functions on the torus, with strict BV convergence. For their smooth approximations f,g, min(f,g) and max(f,g) have sum of gradient norms equal a.e. to |grad f|+|grad g|. They converge in L1 to the two characteristic functions in (4). Lower semicontinuity proves (4). This use of convolution proves a BV identity; it does not approximate the admissible pair in the research problem.

Fix H with H triangle E_n compactly contained in a ball B_rho(x). If P(H)>=P(E_n), the desired scalar inequality is automatic. Otherwise P(H)+P(F_n) is uniformly bounded by the original paired bound. Set

    A=H intersection F_n, B=H union F_n.

Then A subset B, (4) bounds their summed perimeter by P(H)+P(F_n), and pointwise checking of the three possible nested states (0,0),(0,1),(1,1) gives the exact identity

    |A triangle E_n|+|B triangle F_n|=|H triangle E_n|.  (5)

In particular the sum of their two volume errors from the prescribed targets is at most |H triangle E_n|. Outside the comparison ball the pair is the original pair. Choose rho_0>0 sufficiently small. If rho<rho_0, the pair (A,B) is in the fixed correction neighborhood from Lemma 1 for all large n, since its L1 distance from (E_n,F_n) is at most the ball volume. Its volume errors are also below delta. Lemma 1 restores BOTH volumes, retaining inclusion and adding at most Lambda |H triangle E_n| to the energy, for a constant Lambda independent of n,H,rho. Exact paired minimality therefore yields

    P(E_n)+P(F_n)<=P(H)+P(F_n)+Lambda |H triangle E_n|,
    P(E_n)<=P(H)+Lambda |H triangle E_n|.              (6)

There is no obstacle imposed on H; it may cross F_n.

For an outer-interface competitor H with H triangle F_n compactly in the ball, instead set

    A=E_n intersection H, B=E_n union H.

The same proof uses

    |A triangle E_n|+|B triangle F_n|=|H triangle F_n|

and obtains P(F_n)<=P(H)+Lambda |H triangle F_n|. The high-perimeter-competitor case is again immediate.

For rho<rho_0 these inequalities imply the AFM bound with omega rho^3, because the symmetric difference has volume at most (4pi/3)rho^3. For rho>=rho_0 the bound follows trivially from the uniform global perimeter bound M, taking omega>=M/rho_0^3. Thus a single omega suffices for ALL balls, as demanded by AFM's definition, not just sufficiently small balls. QED.

This is the paired argument absent from separate scalar stability. The sum of two equal-weight perimeters is essential to the cancellation in (4)–(6). We are not invoking the ordinary equal-tension three-chamber cluster energy, nor transferring its regularity theorem to the doubled contact interface.

## 5. Precisely applicable scalar regularity, and centering

The external theorem used is **Acerbi–Fusco–Morini, Theorem 4.2**, author final PDF page 22: a sequence of omega-minimizers on T^N with a common omega, bounded perimeters, and L1 limit a C2 set is eventually a global C^{1,1/2} normal graph over its limit, with graph functions converging to zero in C^{1,alpha} for every alpha<1/2. Their Definition 2.5 is on page 7. This theorem is stated without a separate proof in that paper; its preceding paragraph attributes it to classical regularity sources. We use that explicit published theorem, not an unread cluster theorem or an asserted new proof of classical regularity.

Check all hypotheses individually: N=3, torus exactly unit flat; perimeters are uniformly bounded by Section 2; Lemma 2 gives the common omega and the unrestricted competitor inequality; the L1 limits are the smooth embedded sphere and the smooth closed tube. The theorem needs no positive separation between these TWO limit surfaces, because it is applied to each now-proved scalar omega-minimizer. It needs neither CMC nor a W^{2,p} convergence premise.

Consequently, up to null sets, every boundary of these exact minimizers is a single global normal graph over its reference surface, with graph C1 norm tending to zero. This rules out additional boundary components and tentacles FOR THE EXACT MINIMIZERS. We have not excluded them in arbitrary original competitors.

Represent the inner boundary as

    p_n+(R+psi_n(omega))omega, omega in S^2,

and the outer boundary as

    (q_n+(r_n+eta_n(theta,z))e_theta,z),

where q_n is a transverse axis center. A normal graph over C_R supplied by AFM becomes one over C_{r_n} simply by adding epsilon_n to its displacement. Both graph C1 norms still tend to zero.

Choose the three components of p_n and the two transverse components of q_n to impose exact translation-mode orthogonality:

    int_{S_R} psi_n omega_i dS=0 (i=1,2,3),
    int_{Z_{r_n}} eta_n cos theta dS=0,
    int_{Z_{r_n}} eta_n sin theta dS=0.                (7)

Here and below psi_n is identified with a function on S_R. To justify this centering rather than assume it, change a reference center by s and re-express the same C1-small graph. The derivative at the zero graph of its moment map is minus the Gram matrix int nu_i nu_j, invertible on the sphere's three translations and the tube's two transverse translations. The normal projections and their parameter derivatives are continuous for C1-small graphs; the finite-dimensional implicit function theorem gives centers o(1) from the old centers satisfying (7). For the tube the axial normal component is zero, so no nonexistent axial translation mode is imposed. The Gram matrices remain uniformly invertible as r_n -> R.

This is a choice of REFERENCE centers, not separate translations of the actual sets. Now make one common translation so q_n=0 transversely and the axial coordinate of p_n is zero. Write p_n=(h_n,0). Initially h_n=o(1); it will be proved to be O(epsilon_n).

## 6. Energy expansions and scale-epsilon H1 compactness

We supply the required expansions with errors controlled by H1 energy, so concentration cannot hide in a uniform Taylor assertion.

For the spherical radial graph, exact volume gives

    int_{S_R}[psi+psi^2/R+psi^3/(3R^2)] dS=0.         (8)

Its exact area density over S_R is

    (1+psi/R)^2 sqrt(1+|grad_S psi|^2/(1+psi/R)^2).

Expand the square root, using ||psi||C1 ->0, and eliminate its linear integral with (8). The result is

    P(E)-4pi R^2 = Q_B(psi)/2 + Rem_B,
    Q_B(psi)=int_{S_R}(|grad psi|^2-2psi^2/R^2)dS,
    |Rem_B|<=o(1)||psi||H1^2.                        (9)

More explicitly the cubic volume term is bounded by C||psi||infinity int psi^2; the square-root remainder is bounded by C||grad psi||infinity^2 int |grad psi|^2. Thus (9) holds even when the normalized H1 energy concentrates.

For a radial tube graph over Z_r, exact volume is

    int_{Z_r}[eta+eta^2/(2r)]dS=0,                  (10)

and the area density over Z_r is

    (1+eta/r) sqrt(1+eta_z^2+eta_theta^2/(r+eta)^2).

It follows, uniformly for r close to R, that

    P(F)-2pi r=Q_{C,r}(eta)/2+Rem_C,
    Q_{C,r}(eta)=int_{Z_r}(|grad eta|^2-eta^2/r^2)dS,
    |Rem_C|<=o(1)||eta||H1^2.                        (11)

All graph norms and integrals may be pulled back to fixed S_R and Z_R, with uniformly equivalent norms.

There are uniform positive spectral gaps for the two Jacobi forms after removing means and the translations (7). Sphere eigenvalues are [l(l+1)-2]/R^2; the first surviving degree is l=2. Tube eigenvalues are (m^2-1)/r^2+(2pi k)^2. After the constant mode and m=+/-1,k=0 are removed, all are strictly positive, uniformly for r near R, because R>2/9>1/(2pi). These eigenvalues also give H1 coercivity, not merely L2 positivity, since their ratios to 1+the Laplacian eigenvalue have a positive infimum.

Equations (8),(10) imply that the respective means have absolute value at most C times their L2 norms squared. Removing these small constant components therefore changes each form and each H1 norm by o(1) times the original H1 norm squared. Indeed mean^2<=C||graph||L2^4=o(1)||graph||H1^2. Translation orthogonality is unchanged by subtracting a constant. Absorbing the errors in (9),(11), for all large n,

    P(E_n)-4pi R^2 >= c||psi_n||H1^2,
    P(F_n)-2pi r_n >= c||eta_n||H1^2.                (12)

Since their sum is O(epsilon_n^2), we have the paid scale bound

    ||psi_n||H1+||eta_n||H1=O(epsilon_n).             (13)

Define u_n=psi_n/epsilon_n on S_R and v_n=eta_n/epsilon_n, pulled back to Z_R. Pass to weak H1 limits u,v, strongly in L2 on the full surfaces. Both limits have zero mean, by (8),(10),(13). The trace operator on the interior equatorial circle is continuous H1 -> H^{1/2}, and the latter embeds compactly into L2 on the circle. After a subsequence, the equatorial traces of u_n,v_n converge strongly in L2. No point evaluation on a two-dimensional H1 surface is asserted.

The negative L2 terms converge strongly, the gradient terms are lower semicontinuous, and changing r_n to R changes the bounded rescaled cylinder forms by o(1). From (9),(11),(13),

    liminf D_R(epsilon_n)/epsilon_n^2
       >= [Q_B(u)+Q_C(v)]/2.                        (14)

## 7. Actual inclusion controls drift and survives as a contact trace

Let e_theta=(cos theta,sin theta). At the equator of the inner radial graph the boundary point has transverse position

    y_n(theta)=h_n+(R+psi_n(theta,0))e_theta

and axial coordinate exactly zero. Put phi_n(theta)=arg y_n(theta). For large n this is an orientation-preserving circle diffeomorphism, with phi_n -> id in C1: the positive radial factor is C1-close to R and h_n=o(1). Differentiating the argument formula also shows sup|phi_n'-1|<=C|h_n|(1+||psi_n||C1); radial variation alone does not change the angle when h_n=0.

Use the regular open representatives. Inclusion a.e. implies E_n subset closure F_n pointwise, since an inner interior point outside closure F_n would contain a positive-volume ball contradicting inclusion. It therefore applies to the inner boundary by closure. The tube graph represents its disk-like occupied side in each transverse radial fiber; this side is fixed by its L1 convergence and volume. Hence

    |y_n(theta)| <= r_n+eta_n(phi_n(theta),0).

Taking its dot product with e_theta gives the exact, useful inequality

    epsilon_n+h_n dot e_theta+psi_n(theta,0)
          <= eta_n(phi_n(theta),0).                 (15)

There is no second-order center-error term to guess or discard. The L2 norms of the two unscaled traces in (15) are O(epsilon_n) by (13), and composition with phi_n has uniformly bounded L2 operator norm. On the half-circle where h_n dot e_theta is nonnegative, the L2 norm of the positive part of epsilon_n+h_n dot e_theta is at least c|h_n|. Thus (15) proves

    |h_n|=O(epsilon_n).                             (16)

After a subsequence h_n/epsilon_n -> d in R^2. Divide (15) by epsilon_n. The trace of v_n composed with phi_n has the same strong L2 limit as the trace of v_n: approximate its strong L2 limit by smooth functions, use the uniformly bounded composition operators, and phi_n -> id uniformly with controlled Jacobians. Thus pass to the limit in (15), obtaining

    v(theta,0)-u(theta,0) >= 1+d dot e_theta a.e.     (17)

Define the spherical function u_tilde(omega)=u(omega)+d dot omega_transverse. The added function is a mean-zero spherical translation Jacobi field. It has zero bilinear Jacobi pairing with every H1 test, by integration by parts and its Jacobi equation. Therefore

    int u_tilde=0, Q_B(u_tilde)=Q_B(u),
    v(theta,0)-u_tilde(theta,0)>=1.                  (18)

The outer zero mean is unchanged. Equation (18) places the limits in the exact admissible class of I249's quadratic problem. This handles the relative center, including its transverse first angular modes; an independent centering cannot erase it. An axial common translation was already permitted because the reference tube is invariant axially.

## 8. Independent check of the quadratic minimum

For clarity we recheck the calculation used after (18). On the zero-mean subspaces the forms Q_B,Q_C are nonnegative, with precisely the translation kernels specified above. Common averaging in theta preserves the obstacle and both means and discards only nonnegative angular Fourier blocks. Thus the infimum reduces to axial u(t),v(z), t=cos phi on the sphere.

For A=u(0), the mean-zero function u_A(t)=A(1-2|t|) has Q_B(u_A)/2=4pi A^2. For any other such u with this trace, h=u-u_A has mean zero and trace zero. On each hemisphere (-Delta-2/R^2)u_A is the same constant -2A/R^2, so integration by parts gives Q_B(u_A,h)=0. Nonnegativity gives the lower bound 4pi A^2. The kink is an allowed H1 trace construction, not a smooth nonlinear interface.

On mean-zero period-one functions let L=-d^2/dz^2-R^{-2}. It is positive because 2pi>1/R. The function

    g_R(z)=R^2-R cos((|z|-1/2)/R)/(2sin(1/(2R)))

on [-1/2,1/2] has matching periodic derivatives, mean zero, derivative jump -1 at zero and Lg_R=delta_0-1. Its trace G_R=g_R(0)>0 by positivity. Testing this identity with a mean-zero H1 function w gives the energy pairing w(0). Energy Cauchy–Schwarz then yields

    Q_C(v)/2 >= pi R D^2/G_R, D=v(0),

with equality for v=Dg_R/G_R. The averaged obstacle is D-A>=1. Minimizing

    4pi A^2+(pi R/G_R)D^2

under that constraint gives K(R)=4pi R/(R+4G_R), with

    A_*=-R/(R+4G_R), D_*=4G_R/(R+4G_R).

This proves the quadratic lower bound for (u_tilde,v), including all nonaxial modes. Equations (14),(18) establish (1).

For completely arbitrary admissible pairs, Delta_epsilon(A,B)>=D_R(epsilon) by definition, so (1) immediately proves (2). This comparison is why it is unnecessary, and incorrect as a general regularity claim, to require every arbitrary O(epsilon^2)-near-minimizer itself to have global C1 graphs. Small additional tentacles in such competitors cannot reduce their energy below that of the exact minimizing replacement.

## 9. Verification of I253 and the matching limit

The supplied I253 recovery is available and has been read in full. Its order of limits and inclusion argument check as follows. The axial H1 minimizers just computed are Lipschitz. Smooth them as even axial functions, maintaining smoothness at the sphere poles by smoothing only near the equator, and smooth periodically on the tube. Remove each mean. They converge uniformly and in H1, and their traces approach the gap one. Rescale a fixed sufficiently good smooth approximation to have gap 1+gamma, gamma>0. Its energy approaches (1+gamma)^2K(R) as approximation improves.

For each FIXED smooth pair U,V with this gap, take sphere radius R+epsilon U+s(epsilon), and tube radius R-epsilon+epsilon V(z)+t(epsilon). Exact volume equations have nonzero derivatives 4pi R^2 and 2pi R at zero. Their zero first-order means give s,t=O(epsilon^2). At sphere latitude tau its tube containment margin is uniformly

    R[1-sqrt(1-tau^2)]
      +epsilon[-1+V(R tau)-U(tau)sqrt(1-tau^2)]
      +O(epsilon^2).

The bracket is positive at tau=0 by gamma and stays positive on a fixed small strip. Outside the strip the strictly positive zeroth-order term dominates. The full boundary is contained in the tube. Each tube slice is a centered disk, so the entire inner region is contained as well. This gives actual nesting, rather than just the first-order contact inequality. Exact-volume perimeter expansions are precisely (9),(11) with the fixed smooth displacements, hence the recovery upper bound. First take epsilon down to zero for each fixed approximation, then improve the approximation, and then gamma down to zero. No uniform smoothing-scale Taylor remainder is required. All radii stay positive and below 1/2 and the sphere stays embedded.

Thus I253 gives limsup<=K(R), now verified against the same normalizations. Together with (1) it supplies the full limit. The contribution of I263 is the lower passage in Sections 3–7, not this already-supplied upper passage.

## 10. Scope, failure checks and unresolved issues

There is no mathematical bridge left conditional in the proposed proof: the paired correction lemma, uniform scalar quasiminimality, translation normalization, H1 energy scale, and contact-trace passage have all been supplied. The sole nonstipulated advanced input is the explicitly read classical AFM Theorem 4.2; this proof does not reprove that established regularity theorem. Independent proof/contribution review of the resulting full limit has not occurred and is not an imposed verdict of this task.

Checks that matter: exact minimizers suffice for arbitrary-pair lower bounds; both volume corrections use the same ambient diffeomorphism; the volume Jacobian has full rank because both interfaces have free patches in the LIMIT; actual correction patches need no prior regularity or pointwise separation; perimeter-bounded competitors suffice because all other scalar comparisons are trivial; AFM's all-ball omega definition is satisfied by adding the large-ball trivial bound; no CMC assumption is made at contact; translation modes are not discarded before relative drift is controlled; the varying cylinder radius retains a uniform spectral gap; negative quadratic terms are passed by strong L2 convergence; contact traces converge compactly in L2; graph Taylor errors are controlled by the actual H1 energy and small C1 norm, so concentration does not create an unpaid error.

Constants depend on fixed R. No assertion at the branch endpoints, at the Rayleigh–Plateau threshold R=1/(2pi), or of uniformity up to such endpoints is made. No assertion of worldwide novelty follows from the bounded searches. Counts, shared indexes, staging, commits, publication, snapshots, research code, numerical scans, tests and subordinate agents are untouched.
