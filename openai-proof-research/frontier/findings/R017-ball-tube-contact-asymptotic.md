# R017 — Sharp nonlinear ball–tube nesting cost

**Accepted as the eleventh substantial finding.** The complete I249/I253/I263 theorem passed [I269 independent proof review](../reviews/i269-nonlinear-contact-proof.md) without substantive repairs and [I270 independent contribution review](../reviews/i270-nonlinear-contact-contribution.md) as SUBSTANTIAL. The parent read both complete reviews and analyses and checked their input/output hashes. This is written mathematical validation, not a formal proof certificate, external peer review, or a worldwide-priority claim.

## Exact theorem

Let T^3=R^3/Z^3 have the unit cubic flat metric, and let P denote De Giorgi perimeter. Fix

    2/9 < R < 1/pi.

For sufficiently small epsilon>0, define

    D_R(epsilon) = inf { P(E)+P(F)-4pi R^2-2pi(R-epsilon) :
                        E subset F a.e.,
                        |E|=4pi R^3/3,
                        |F|=pi(R-epsilon)^2 },

where the infimum is over all finite-perimeter pairs in T^3. Then

    lim_(epsilon down to 0) D_R(epsilon)/epsilon^2 = K(R),
    K(R)=4pi R/(R+4G_R),
    G_R=R^2-(R/2)cot(1/(2R)) > 0.

In particular, every admissible sequence of pairs at epsilon_n down to zero has normalized deficit with liminf at least K(R), and a sequence of smooth nested pairs attains this coefficient. No symmetry, connectedness, fixed topology, or boundary regularity is imposed on the original competitors. All constants and convergence statements may depend on fixed R.

## Dependencies and the new step

The [pinned cubic-torus theorem](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026) supplies the scalar isoperimetric profile and equality classes. It is assumed true, as requested. Here the inner volume is strictly on its ball branch and the outer volume strictly on its circular-tube branch. The separate scalar optima cannot nest at positive epsilon. Their limiting representatives touch along the equatorial circle.

The classical regularity input is Acerbi–Fusco–Morini, [Minimality via second variation for a nonlocal isoperimetric problem](https://cvgmt.sns.it/media/doc/paper/540/Acerbi-Fusco-Morini.FINAL.pdf), Definition 2.5 and Theorem 4.2. Its exact uniform quasiminimality hypotheses and global normal-graph conclusion were checked. Its original regularity proof was not reproved here.

The new conclusion is the sharp nonlinear minimum over the unrestricted pair class. Separate squared-L1 stability sees the missing belt volume at order epsilon^(3/2) and gives only an epsilon-cubed lower scale. The paired regularity reduction and the contact-trace argument identify the larger epsilon-squared cost and its coefficient. Classical lattice inequalities, volume fixing, scalar improved convergence, spectral decompositions and Green functions are credited tools, not separately claimed discoveries.

## Proof

**Minimizing replacement and limiting geometry.** A coaxial embedded ellipsoid with semiaxes r,r,R^3/r^2, where r=R-epsilon, fits in the radius-r tube, has the required inner volume, and gives deficit O_R(epsilon^2). BV compactness gives exact paired minimizers. Each separate scalar deficit is nonnegative. Along a sequence tending to zero, every paired L1 limit therefore consists of a radius-R ball inside a radius-R shortest axial tube. Their equal-area transverse projection disks must coincide. A common translation and a signed coordinate permutation place the limit at the centered ball and the z-axis tube. This uses actual torus isometries.

**Two-volume correction before regularity.** Choose one smooth ambient field on a sphere patch strictly inside the limiting tube and another on a tube patch disjoint from the limiting ball. Their two-volume derivative is diagonal with positive entries. For nearby measurable pairs the volume functions are integrals of smooth flow Jacobians; L1 proximity preserves uniform invertibility. A common ambient diffeomorphism corrects volume errors of summed magnitude q with parameter O(q), keeps inclusion, and costs O(q) in perimeter for bounded-perimeter pairs.

For an arbitrary local competitor H for the inner set, use the nested pair (H intersection F,H union F). Perimeter submodularity bounds its total perimeter by P(H)+P(F), and its total L1 change from (E,F) equals |H triangle E|. Correct both volumes by the common flow and use paired minimality. Competitors of greater scalar perimeter give the desired inequality trivially; the others have uniformly bounded total perimeter. Hence

    P(E)<=P(H)+C|H triangle E|.

The analogous construction (E intersection H,E union H) works for outer competitors. A small-ball volume bound and a trivial large-ball bound prove every-ball uniform quasiminimality for both interfaces. AFM then gives global C1-small normal graphs separately, even though the limiting interfaces touch.

**The correct scale and translation modes.** Use reference-center implicit functions to remove the sphere's three and the tube's two normal translation modes; this reexpresses unchanged sets and does not move them independently. Keep the remaining relative transverse displacement h. Let psi and eta be the sphere and tube heights. Exact-volume area expansions give

    P(E)-4piR^2 = Q_B(psi)/2 + o(1)||psi||_H1^2,
    P(F)-2pi r = Q_(C,r)(eta)/2 + o(1)||eta||_H1^2,

with

    Q_B(u)=integral_(S_R)(|grad u|^2-2u^2/R^2),
    Q_(C,r)(v)=integral_(Z_r)(|grad v|^2-v^2/r^2).

The small nonzero means from the volume equations contribute only higher-order errors. On the remaining modes the sphere and tube forms have uniform H1 gaps; for the tube this uses R>1/(2pi). Thus ||psi||_H1+||eta||_H1=O(epsilon). Divide the heights by epsilon and extract weak H1, strong L2, and strong equatorial-L2-trace limits u,v. The negative quadratic terms converge strongly and gradients are lower semicontinuous.

**Actual inclusion gives the trace obstacle.** At the inner equator put y=h+(R+psi(theta,0))e_theta and phi(theta)=arg y. Actual containment gives |y|<=r+eta(phi(theta),0), hence exactly

    epsilon+h dot e_theta+psi(theta,0)<=eta(phi(theta),0).

The angular map tends to the identity with bounded Jacobians. The unscaled trace bounds force h=O(epsilon); otherwise the positive half-circle of h dot e_theta violates the displayed inequality in L2. Compact trace convergence survives composition, by smooth approximation of a fixed L2 limit. Along a subsequence h/epsilon tends to d, giving

    v(theta,0)-u(theta,0)>=1+d dot e_theta.

Add the zero-energy spherical translation field d dot omega_transverse to u. The constraint becomes v-u>=1 and the quadratic energy is unchanged. Therefore every minimizing sequence has normalized lower limit bounded below by the minimum of (Q_B(u)+Q_C(v))/2 among zero-mean H1 functions with this trace constraint. Concentration of gradient energy is allowed and can only increase the lower bound.

**Compute the minimum.** Common angular averaging preserves the constraint and discards only nonnegative angular modes. Write A=u(0), D=v(0) for the resulting axial traces. The optimal spherical function is

    u(t)=A(1-2|t|),  t=z/R on the reference sphere,
    Q_B(u)/2=4pi A^2.

For the tube, the mean-zero period-one Green function of -d^2/dz^2-R^-2 is

    g_R(z)=R^2-R cos((|z|-1/2)/R)/(2 sin(1/(2R))),
    -1/2<=z<=1/2.

It satisfies Lg_R=delta_0-1, has zero mean, and g_R(0)=G_R>0. Positivity follows from the spectral gap on mean-zero periodic functions. Energy Cauchy–Schwarz yields Q_C(v)/2>=pi R D^2/G_R, attained by v=Dg_R/G_R. Consequently

    min_(D-A>=1) [4pi A^2+(pi R/G_R)D^2]
       =4pi R/(R+4G_R)=K(R).

The optimizing values are A=-R/(R+4G_R) and D=4G_R/(R+4G_R). This proves the lower bound.

**Nonlinear recovery.** Smooth the two optimal axial H1 profiles, remove their means, and give the trace gap a fixed buffer 1+gamma. The approximations converge in H1 and uniformly. For each fixed smooth pair, constant graph corrections of size O(epsilon^2) restore both volumes exactly. The buffer ensures inclusion near the equator; away from it the original geometric gap is positive. The inner boundary lies in every corresponding disk slice of the tube, which also gives inclusion of the whole inner region. First take epsilon to zero, then improve the approximation, then let gamma decrease to zero. The normalized energies tend to K(R), proving the matching upper bound.

The [I263 full argument](../experiments/i263_nonlinear_contact_lower_bound/analysis.md) and [I269 independent reconstruction](../experiments/i269_nonlinear_contact_proof/analysis.md) supply the complete correction, chart, spectral, trace and limit-order details.

## Validation and limits

- **Proof:** I269 PASS, no substantive repair, on I263 SHA256 `d02db6dfe8b65bba3196baf2cd8de6eb4dec1ce13084696c9fe81ed2aee3fc95`.
- **Contribution:** I270 SUBSTANTIAL for the full unrestricted nonlinear limit, not for the quadratic calculation or recovery separately.
- **Independent comparisons:** the complete [I270 source record](../sources/i270_nonlinear_contact_contribution/literature.md) distinguishes scalar and cluster improved convergence, weighted core-shell selection, periodic second variation, and the pinned slice-nesting operation from this theorem. ABLW's second Gamma-limit is Theorem 4.5. Its contact-selection result remains credited prior work.
- **Scope:** no endpoint-uniform estimates, dynamical conclusion, arbitrary near-minimizer graph theorem, general unequal-tension result, or full functional Gamma-limit is claimed. The separate logarithmic point-contact candidate I274/I275 is not included in this acceptance.
- **Provenance:** parent verified both review manifests and the associated local input/output hashes. The proof-review manifest is `598b7bd05ced836618e0a86d50b71d48ae4024c8c0d9a2105aecae1bfe93f310`; the contribution manifest is `b02aa9a13c7229f8cd60038406589f14c88b38c2d3ea0526bd8e3618ca552ca3`. The recorded source-read limits are preserved; not every cited external proof was reread.

**Eleven accepted substantial findings; nine remain toward twenty.** The original ten acceptances are preserved. This acceptance receives its own commit and verified project-only publication.
