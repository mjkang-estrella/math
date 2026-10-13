# I275: full proposed logarithmic ball–slab contact proof

Parent analytic development, 2026-10-12. **Complete proposed proof, not independently validated or accepted.** This develops I274. The full statement and every new argument below require independent proof and contribution gates. No count changes.

## 1. Statement and dependencies

On T^3=R^3/Z^3 with unit cubic metric, fix R in (1/(2pi),1/3). For epsilon>0 small define

    L_R(epsilon)=inf [P(E)+P(F)-4pi R^2-2],
    E subset F a.e., |E|=4pi R^3/3, |F|=2(R-epsilon),

where both sets have finite perimeter. The claim is

    lim_(epsilon down to 0) |log epsilon| L_R(epsilon)/epsilon^2=2pi.       (1)

There are no graph, connectedness or symmetry assumptions on competitors. R is fixed; no endpoint-uniform claim is made. The scalar profile and all equality cases in pinned family-354 Theorem intro:main are stipulated true. Read source: `frontier/sources/i269_nonlinear_contact_proof/354-paper.tex`, especially lines 54–84, SHA256 `ab75095f542adf4073a41a26a3c3ae97be7b55fa19674ec4fb4c288f7145a813`. The inner volume is strictly on the ball branch; 2R belongs to (1/pi,1-1/pi), so the outer volume is strictly on the slab branch, using complements when it exceeds 1/2. Separate deficits are nonnegative.

The external regularity input is AFM Definition 2.5 and Theorem 4.2 in the retained page-7/page-22 excerpts: uniformly quasiminimizing sets converging in L1 to a smooth set have global C1-small normal graphs. Its exact statement, not its underlying classical proof, was read. It applies on the flat torus to disconnected boundaries as well as connected ones. The full original PDF was not reread here. Its recorded SHA256 is `7805d5a0b9daf3873a199bbfe23d4064964fc2e72701be6d45303549028d4c72`.

All other ingredients below are BV compactness/lattice inequality, finite-dimensional volume correction, spectral expansion on the sphere, and the elementary radial-average calculation in Section 5. The I269 proof of the separate ball–tube theorem is not a proof of (1).

## 2. Matching upper construction

Write ell=|log epsilon|. Fix small delta>0 and eta>0. Set a=sqrt(epsilon) ell and choose a radial cutoff chi on each polar chart, equal to one up to a and zero beyond delta, logarithmic between them. Round its two corners on comparable radial intervals. The rounding can be chosen with

    integral |grad chi|^2=(2pi+o(1))/log(delta/a),
    integral chi^2=O_delta(ell^-2)+O(a^2),
    integral chi=O_delta(ell^-1)+O(a^2),
    ||grad chi||_infinity=O(1/(a ell)).

These follow by integrating 2pi rho d rho and chi'= -1/[rho log(delta/a)]; smoothing on [a,2a] and [delta/2,delta] changes the first integral by O(ell^-2). In the spherical charts use horizontal distance from the pole, whose metric differs from the plane by O(delta^2). The two polar supports are disjoint.

Put t=(1+eta)epsilon/2. Give the sphere normal displacement -t chi at both poles. Give each slab face outward displacement +t chi around its corresponding pole. Add smooth volume-correcting bumps on fixed free patches, disjoint from these supports. The inner bump has nonzero first volume derivative; an outer-face bump has nonzero outer-volume derivative. The two exact volume equations therefore have solutions with parameters O_delta(epsilon/ell) by the inverse function theorem. Their Dirichlet and squared-L2 costs are O_delta(epsilon^2/ell^2); their support is away from contact. All graphs are C1-small.

In the core |x|<=a/2, the spherical cutoff is one even after converting from normal to vertical coordinates, and the corresponding vertical inward displacement is t(1+o(1)). The slab moves outward by t. The available margin is thus (1+eta+o(1))epsilon minus the imposed thinning epsilon, which is positive. Outside this core, the unperturbed ball–face separation is at least c_R a^2 until leaving the chart, whereas all displacements are O_delta(epsilon). Since a^2/epsilon=ell^2 tends to infinity, this separation pays thinning and every correction there. On the fixed free patches the original separation is positive; shrinking epsilon preserves it. This proves that the entire inner boundary lies between the two outer graph faces. At each horizontal point any nonempty compact slice of the inner region has its minimum and maximum vertical coordinates on that boundary. The outer slice is an interval between its two faces. Therefore the full inner region is contained in the outer region; one need not assume that a radial graph has connected vertical slices.

The sphere area expansion at fixed volume is one half of its Jacobi form, with a remainder o(1) times H1 norm squared; the slab expansion is one half of the two Dirichlet integrals. These formulas hold because the unscaled C1 norms tend to zero. The spherical potential term and the correction-bump costs are o(epsilon^2/ell). Each of four patches contributes one half times t^2 times the cutoff energy. Hence

    limsup ell L_R(epsilon)/epsilon^2
      <=2pi(1+eta)^2(1+O_R(delta^2)).

First send epsilon to zero, then delta and eta to zero. This proves the proposed limsup <=2pi. The bump supports can be chosen with fixed positive gap from the other interface: for the sphere use an equatorial patch strictly inside the slab; for the slab use a patch horizontally outside the radius-R ball projection.

## 3. Exact minimizers and global graphs

BV compactness gives an exact minimizing pair for every small epsilon, because inclusion and both volumes persist under L1 limits and the sum of perimeters is lower semicontinuous. Section 2 gives L_R=O(epsilon^2/ell). Along a sequence epsilon_n down to zero, each separate scalar deficit tends to zero. Every limiting pair is therefore a radius-R ball inside a width-2R coordinate slab. Inclusion forces the ball center to be halfway between the faces in the normal direction. Common translations and signed coordinate permutations place this limit at B_R(0) inside {-R<z<R}; transverse translations of the ball are included in this common normalization. No arbitrary torus rotation is used.

Here is the regularity bridge in this geometry. Fix a free sphere patch inside the limiting slab and a free slab patch outside the limiting ball. Two ambient vector fields supported there have a diagonal, nonzero two-volume derivative at the limit. For any nearby measurable pair the derivative is the integral of smooth Jacobian derivatives; L1 closeness preserves uniform invertibility. A common ambient flow corrects two volume errors of total size q with parameter O(q) and perimeter cost O(q) for bounded-perimeter pairs. It preserves inclusion.

Given an arbitrary scalar competitor H for the inner set, the pair (H intersection F,H union F) is nested, its summed perimeter is <=P(H)+P(F), and its total L1 change is exactly |H triangle E|. The common flow corrects its volumes. For H with smaller scalar perimeter, its total perimeter is uniformly bounded, giving P(E)<=P(H)+C|H triangle E| when the symmetric difference lies in a sufficiently small ball. Larger-perimeter H gives this inequality trivially. For the outer competitor use (E intersection H,E union H) and the identical argument. Small-ball volume bounds and the trivial bounded-perimeter estimate on balls of radius at least a fixed rho_0 give a uniform omega rho^3 bound for EVERY comparison ball. Thus both sets satisfy the exact AFM scalar hypothesis.

Apply AFM separately to the sphere and to the disconnected union of two flat faces. The exact minimizing pair has global C1-small normal graphs. Choose the spherical reference center to remove its three l=1 moments. Choose the slab reference center to make both face heights have zero mean: their means sum to zero by its exact volume, and translating the reference center changes them oppositely. A common translation fixes the spherical center at zero transversely and the slab center at zero axially. The remaining relative axial center is h_n, kept throughout the contact inequalities. Changing references does not move actual sets independently.

Let psi_n be the sphere normal height and V_n^+,V_n^- the outward face heights over z=+r_n and z=-r_n, where r_n=R-epsilon_n. Exact sphere volume implies its mean is O(||psi_n||_L2^2), while each V_n has mean zero exactly. The sphere l>=2 gap, after absorbing its small mean and area remainder, and the plane Poincare inequality imply

    ||psi_n||_H1 + ||V_n^+||_H1 + ||V_n^-||_H1
          =O(epsilon_n/sqrt(ell_n)).                              (2)

All norms here are on fixed smooth reference surfaces. The sphere deficit expansion is Q_B(psi_n)/2+o(epsilon_n^2/ell_n), Q_B=integral(|grad psi|^2-2psi^2/R^2); the two faces contribute their Dirichlet energies divided by two with the same remainder control. Uniformity follows from unscaled C1-smallness and (2), not a bound on normalized derivatives.

## 4. Local vertical charts without a pointwise expansion error

Fix small delta and consider |x|<2delta at either pole. The sphere is an actual vertical graph there. Write W_n^+ for its outward vertical height relative to h_n+sqrt(R^2-|x|^2), and W_n^- for its downward height relative to -h_n+sqrt(R^2-|x|^2) measured downward. These are exact heights, not first-order replacements. Inclusion gives exactly

    V_n^+(x)-W_n^+(x)>=epsilon_n+h_n-[R-sqrt(R^2-|x|^2)],
    V_n^-(x)-W_n^-(x)>=epsilon_n-h_n-[R-sqrt(R^2-|x|^2)].       (3)

For clarity, the lower physical boundary is z=h_n-sqrt(R^2-|x|^2)-W_n^-(x), and the outer lower face is z=-r_n-V_n^-(x), which gives the second sign in (3).

Relate W to psi exactly. If F_n maps a horizontal point x to its spherical direction in the actual radial graph, then

    W_n(x)=A_n(x) psi_n(F_n(x)),
    A_n=(2R+psi_n(F_n)) /
       [sqrt((R+psi_n(F_n))^2-|x|^2)+sqrt(R^2-|x|^2)].          (4)

This holds at either pole with the respective spherical direction. For small fixed delta, F_n is a C1 diffeomorphism onto its polar patch, with metric distortion 1+O_R(delta^2)+o_n(1). Also A_n=1+O_R(delta^2)+o_n(1) and |grad A_n|<=C_R delta+o_n(1). These estimates follow by differentiating (4) and x=(R+psi)omega_transverse, using the unscaled C1-smallness. In particular no error proportional to ||psi||_infinity is declared o(epsilon_n).

Fix a spherical spectral cutoff N, and decompose psi_n=b_n+l_n+k_n into its constant mean, l=2,...,N modes, and l>N modes. The l=1 part is zero by centering. By (2), |b_n|=O(epsilon_n^2/ell_n) and ||l_n||_C1=O_N(epsilon_n/sqrt(ell_n))=o_N(epsilon_n). Define the exact transformed high part

    W_{n,high}^pm=A_n^pm k_n(F_n^pm).

Its difference from W_n^pm is o_N(epsilon_n) uniformly on the charts. The nonlinear coefficient and map remain the ACTUAL ones from the full graph; this avoids replacing their arguments with an unjustified pointwise Taylor expansion.

For any xi>0, differentiation, change of variables, and 2ab<=xi a^2+xi^-1 b^2 give

    sum_pm integral_(|x|<2delta) |grad W_{n,high}^pm|^2
      <=(1+C_R delta^2+xi+o_n(1)) integral_S |grad k_n|^2
          +C_(R,delta,xi) integral_S k_n^2.                    (5)

The two spherical patches are disjoint. The high-frequency estimate integral k_n^2<=R^2/[(N+1)(N+2)] integral|grad k_n|^2 absorbs the last term with arbitrarily small relative loss by taking N large after delta,xi are fixed. In addition Q_B(k_n)>=(1-2/[(N+1)(N+2)]) integral|grad k_n|^2. The low modes have nonnegative Jacobi energy, while the constant-mode contribution is o(epsilon_n^2/ell_n). Thus, for any prescribed zeta>0, choose delta small, xi small and N large, all fixed before n tends to infinity, to obtain

    L_R(epsilon_n)>= (1-zeta)/2 *
       sum_pm integral_(|x|<2delta)
         (|grad W_{n,high}^pm|^2+|grad V_n^pm|^2)
         +o(epsilon_n^2/ell_n)
      >=(1-zeta)/4 * sum_pm integral_(|x|<2delta)|grad Z_n^pm|^2
         +o(epsilon_n^2/ell_n),                                (6)

where Z_n^pm=V_n^pm-W_{n,high}^pm. Their local H1 norms are O_delta(epsilon_n/sqrt(ell_n)). In (6) each face uses its actual flat Dirichlet energy; discarding energy away from its polar disk is legitimate. The order of parameter choices is part of the assertion.

## 5. The elementary annular capacity inequality

For a C1 function Z on a planar disk define m(rho)=(2pi)^-1 integral Z(rho,theta)dtheta. For 0<a<b,

    integral_(a<|x|<b)|grad Z|^2
       >=2pi integral_a^b rho |m'(rho)|^2 d rho
       >=2pi [m(a)-m(b)]^2/log(b/a).                            (7)

The first inequality is Jensen; the second is weighted Cauchy–Schwarz. The same inequality holds for H1 functions at almost every radius by approximation, although the present graphs are C1. It never evaluates a two-dimensional H1 function at a point.

From the L2 norm on the annulus delta<|x|<2delta there is some b_n in [delta,2delta] with |m(b_n)|<=C_delta ||Z_n||_L2=o(epsilon_n), separately for each sign. This follows by polar integration of |Z|^2 and Jensen. The radius may depend on n; its logarithm remains uniformly bounded.

Fix c>0 small and set a_n=c sqrt(epsilon_n). On the entire circle |x|=a_n, (3), the exact decomposition in Section 4, and the elementary expansion of the fixed sphere give

    m_n^pm(a_n)>=[1-c^2/(2R)+o_n(1)]epsilon_n
                          +/-h_n-o_N(epsilon_n).

Therefore, using (7) and allowing negative lower bounds through positive parts,

    integral_(|x|<2delta)|grad Z_n^pm|^2
       >= [4pi+o_n(1)]/ell_n *
             ([1-c^2/(2R)+o_n(1)]epsilon_n +/-h_n)_+^2.        (8)

The common o_n(1) can be decreased to cover both signs. No bound on h_n/epsilon_n is assumed. The positive-part inequality

    (a+h)_+^2+(a-h)_+^2>=2a^2  for a>=0

holds for every real h, so arbitrarily drifting reference centers cannot lower the coefficient. Any needed bound on h can instead be recovered afterwards from (8) and the upper energy, but is unnecessary for the lower bound.

Combining (6) and (8) yields

    liminf ell_n L_R(epsilon_n)/epsilon_n^2
       >=2pi(1-zeta)(1-c^2/(2R))^2.

Let c and zeta decrease to zero. Since the argument applies to a subsequence realizing the liminf of exact minima, it proves the proposed liminf>=2pi. Section 2 gives the reverse inequality. Every original admissible pair has at least the exact minimum, so the scope remains all finite-perimeter pairs.

## 6. Gate status and explicit audit targets

The proposed proof pays for capacity using circle averages, not point traces; for chart changes using the exact multiplicative identity (4), not an o(epsilon) assertion about arbitrary C1 errors; and for the negative Jacobi term by spectral separation before localizing. These steps are the principal independent audit targets, alongside the four-patch upper geometry, disconnected slab centering, and parameter-order quantifiers in (5)–(8).

The previous I274 note correctly recorded those as unpaid at that time. This development proposes to close them; no external reviewer has yet certified that it succeeds. No novelty search or contribution verdict has yet been performed. No numerical evidence, theorem-prover verification or code test is offered as proof. This remains one unaccepted prospective finding, separate in mechanism from the quadratic ball–tube theorem.
