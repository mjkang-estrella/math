# Lattice block limits and pressure-increment sandwich

Myeongjin Kang. Original prose CC BY 4.0. Author derivation for the unchanged T216A scope; not an independent review. The continuum boundary-pressure equality is a separate obligation. All references to pinned source theorems use fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

Use D=(-1,1)^2, Q_n=[-n,n]^2∩Z² and a_n as in the source. Let A>0 be its center amplitude, K=2/pi, a=8pi, and

    kappa=exp[R_D(0,0)/(2K)].

Write E_0 for the infinite-volume zero-field free-box limit; rotation invariance is retained. All comparisons can first be made in a finite free box, followed by its thermodynamic limit for a fixed observation region. Let mu_D denote ultraviolet-only imaginary chaos of the log-one zero-Dirichlet GFF at beta=1/2, and mu_* the whole-plane version with an independent uniform global phase. The last convention makes all nonneutral moments zero.

The precise conclusions proved below are, for each fixed real t,

    E_0 exp[t Re sum_(x∈Q_n) e^(i theta_x)/(n²a_n)]
       -> E exp[t kappa Re mu_*(D)],                                      (1)

    E^+_(Q_n,0) exp[t Re sum_(x∈Q_n) e^(i theta_x)/(n²a_n)]
       -> E exp[t kappa Re mu_D(D)].                                      (2)

In (2) the boundary spins are fixed to1 and included; their deterministic normalized contribution tends to zero. These are fixed-t convergence statements. No uniformity for t→infinity is claimed or used.

## 1. The finite-neutral-configuration extension

The logarithmic-correction manuscript geometry.tex proves its two-point thermodynamic comparison using: the finite affine/matching-constraint inequality; a pinned-rim trial-energy lower bound; k-nest attachment with density bound2^k; and exterior Green energies. The only extension needed here is the pinned-rim lower bound for a fixed finite neutral unit-charge configuration. We detail it rather than apply a two-hole statement silently.

Fix distinct planar points z_1,...,z_k and signs sigma_i∈{−1,1} with sum sigma_i=0. Here k is fixed; constants may depend arbitrarily on the configuration and k. Around the points take sufficiently small disjoint dyadic rectilinear holes. Pair the plus and minus points by disjoint simple polygonal arcs. One construction is a minimum-total-length bipartite matching: crossing interiors can be uncrossed to decrease length; degeneracies can instead be resolved by small planar perturbations of an optimal drawing. Alternatively, successively join an opposite-sign pair by a simple arc and work in the connected complement of that slit. Since an arc between two interior points does not separate the plane, this inductive construction leaves a path for the next pair. After choosing disjoint arcs, thicken them by sufficiently small distinct widths and perturb to dyadic rectilinear arcs with transverse exits in the interiors of hole sides. All clearances are positive at this fixed configuration. Endpoints inside the small holes are omitted, so the arcs join opposite-charge hole boundaries.

Put a thick aligned rim F outside all holes/arcs. Let vartheta=dv be a smooth closed form with periods2pi sigma_i, admitting a branch whose only jumps are2pi across the pairing arcs, and which is zero near F. Use the canonical integral connection on bonds crossing those arcs. Its support stays away from F and the outer collar. We claim the source pinned-sector lower bound extends as

    liminf_(nu→infinity) Phi_(G_nu(U), h_F=0)^tau
        >= exp[-(1/(2a)) integral_U |vartheta|²].                          (3)

To prove it, cut narrow strips surrounding all arcs. Select disjoint wider patches W_j, guard bands P_j, endpoint regions H_j around strip interfaces, and endpoint regions H'_j around the artificial boundaries of W_j. At each transverse exit the guard reaches the original hole wall between H_j and H'_j, exactly as in the source two-hole construction. The patches are disjoint from one another and F. Use one dyadic cell partition of side ell aligned with *all* these regions and every cut topology. Cells are always assigned to connected components before hard pins; none crosses a guard division.

On every topology retain F and introduce quadratic observations centered at Bv_nu in the shifted law and at0 in the centered law, with equal positive precisions. The branch is zero on F, so these constraints are compatible. Added precision decreases the ratio. After all strips are cut, each component has a single-valued lift v_V; on components meeting F its branch is zero there. Gauge by the integral potential v_nu−v_V, which vanishes on F. The exact lattice identity is grad v_nu+tau=the edge integral of vartheta. Consequently the mixed height limit and Gaussian completion give the confined ratio on V as exp[−I_(ell,V)/2], with

    I_(ell,V)=inf_{u∈H¹(V), u=0 on F∩V}
       {a^(-1) integral_V |grad u|² + sum_{cells Q⊂V}(u_Q−(v_V)_Q)²}.

An empty pin imposes no restriction. Trying u=v_V and the cell Poincare estimate in the source prove I_(ell,V)→a^(-1) integral_V |grad v_V|² as ell↓0 after the lattice limit. Thus the fully cut ratio tends, in this ordered limit, to the right side of (3).

Restore the strips one at a time. For strip j, condition on full absolute guard data u on P_j. Its restored-to-cut kernel K_j^tau(u), divided by d_j=K_j^0(0), lies in(0,1] by finite affine comparison. Conditional locality makes this exactly the patch kernel in W_j, unaffected by the rim or the other restored strips. Within W_j both cut and open geometries have a single lift, and their energies agree because cut interfaces have zero area. The source exact patch-loss identity therefore gives

    L_(W_j)^tau = Phi_(cut W_j)^tau
       −Phi_(open W_j)^tau E_(cut W_j,0)(K_j^0/d_j) ->0.                  (4)

The centered loss also tends to zero. The centered kernel expectation tends to1 by the source cell-pin localization estimate for H_j,P_j, with ell sent to0 after mesh refinement.

For completeness, passing (4) to the current whole graph uses precisely the same comparison with all other restored strips retained. Cutting the artificial boundary of W_j leaves an exterior shifted-to-centered ratio at most1; it need not admit a single-valued lift at this stage. The normalized data comparison loses at most exp[D^F(H'_j,P_j)]. Bayes' identity gives

    0<=D^F(H'_j,P_j)
       =D(H'_j∪F,P_j)−D(F,P_j)<=D(H'_j∪F,P_j).

The last interaction tends to0 by the source localization theorem on the centered *pre-pin* cut geometry with component-local observations. H'_j∪F remains positively separated from P_j. Its validity does not depend on the shifted sector outside the patch. Hence both global losses vanish. The exact restoration identity is

    Phi_open=(Phi_cut−L_tau)/(1−L_0).

There are only k/2 restorations, so this proves (3). No error is multiplied over an unbounded number of charge insertions. Every hole, arc, patch, guard and rim was fixed before the mesh limit; ell↓0 follows that limit. This is the source two-hole mechanism applied finitely many times with its constraints unchanged.

## 2. Neutral infinite-volume correlations

Take unit lattice currents connecting the opposite charges along the discretized arcs, extended through their microscopic cores. The dual connection vanishes near the outer rim. For any sufficiently large free spin box, releasing matching constraints across the outer comparison square gives the source free-height upper comparator. Adding h_F=0 before cutting gives the lower comparator; the exterior factor cancels exactly since the connection is zero there. Taking the thermodynamic limit first gives

    Phi_pinned <= E_0 exp[i sum_i sigma_i theta_(x_i)] <= Phi_free.       (5)

This is the same finite comparison as source equation geo:thermodynamic-bracket, with finitely many current paths rather than one. It holds for moving lattice points x_i/n→z_i and fixed separated limiting configurations.

The plane trial is the derivative of

    Theta(z)=sum_i sigma_i arg(z−z_i),

with jumps along the chosen pairing arcs. Neutrality gives Theta(z)=O_k(1/|z|), grad Theta=O_k(1/|z|²) outside a large fixed disk after choosing the branch tending to0 at infinity. Multiplying by a cutoff equal to1 near the points and0 near a rim of radiusR changes the energy by O_k(R^−2). On the plane with radius-t circles removed, Green's identity gives

    integral |grad Theta|²
       =2pi k log(1/t)−4pi sum_(i<j) sigma_i sigma_j log|z_i−z_j|+O_k(t). (6)

The regular harmonic pieces have zero total normal derivative at each small circle, so the error has no extra logarithm. Polygonal holes cost O_k(epsilon) via inner/outer circle bracketing. The free-height exterior energy has the same limit as R→infinity: neutrality cancels the logR term in its Green expansion. Formula (3) supplies the lower trial bound, while releasing the rim supplies its free upper bound.

Use identical annular nests at the k unit sources and at k separate copies of the center source in D. The source k-nest attachment formula is already stated for arbitrary fixed k; its propagated guard density is bounded by2^k. Choose R sufficiently large for a specified accuracy, hole scale eta and polygon error epsilon small, annular ratio lambda sufficiently large for pin loss, and finally the fixed microscopic threshold sufficiently large. The joining-ratio leading logarithms cancel between the k last annuli and their exterior. Formula (6) and the source free energies show that the remaining attachment errors are arbitrarily small. Thus exact cancellation of the common microscopic factor N_J^k against a_n^k yields

    a_n^(−k) E_0 exp[i sum_i sigma_i theta_(x_i)]
       -> kappa^k product_(i<j)|z_i−z_j|^(sigma_i sigma_j/4).              (7)

Indeed the k center energy is k[2pi log(1/t)+4pi²R_D(0,0)], and a=8pi. Its regular part contributes exp[k(2pi²/a)R_D(0,0)]=kappa^k. The cross energy in (6) contributes exponent(2pi/a)=1/4.

As in source geo:comparison, the last nest radius divided by n need not converge initially. Every subsequence has a further subsequence with positive limiting radius in[eta/lambda,eta]; moving-hole stair brackets apply on that subsequence. Arbitrary accuracy then proves the full limit. The same proof works for any sequence of separated configurations converging in a fixed compact set. Sequential compactness therefore makes (7) uniform on compact separated configuration sets. For nonneutral signed lists, the infinite free expectation is exactly zero by global rotation.

## 3. From separated correlations to block Laplace transforms

The source Lee–Yang absolute-moment bound also holds in finite free boxes: the law is already rotation invariant, so its proof needs no additional boundary vertex. For nonnegative weights W=sum lambda_x e^(i theta_x),

    ||W||_p <= C sqrt(p) (E|W|²)^(1/2),  p>=2.                          (8)

All signed spin moments are nonnegative by the Fourier-current expansion, including repetitions. Both statements pass to E_0 for each fixed finite support. For complex weights split into four nonnegative real parts as in the source.

Let E be any fixed bounded planar set. Pin a larger square of radiusCn so that nE lies in its central half. The finite comparison bounds each infinite-volume neutral two-point function by this pinned one. The source collision estimate, Green diagonal bounds on that central half and a_(Cn)/a_n→C^(-1/8) imply for every square B⊂E of side delta

    E_0 |(n²a_n)^(-1) sum_(x/n∈B) e^(i theta_x)|²
          <= C_E(delta+n^(-1))³.                                       (9)

The same estimate with a uniform constant holds on a fixed slightly larger E. To sum any fixed k-th moment over configurations with two points within delta, cover such pairs by O_E(delta^−2) squares of sideO(delta). Positivity lets us restrict two factors to each square and leave all other factors on the larger E. Holder with k equal exponents and (8) makes each contribution at most C_(E,k)(delta+n^−1)³. Consequently the total collision contribution has limsup at most C_(E,k)delta. Repeated sites are included. This is exactly the source collision-removal operation, now using (9).

Away from collisions, (7) and Riemann sums give the whole-plane neutral chaos moments. The continuum kernel has the usual integrable Onsager domination; alternatively its moments are obtained by the same bounded-domain exhaustion and moment bound. Nonneutral moments vanish. The uniform sqrt(p) bounds from (8) give moment determinacy and uniform exponential integrability for every fixed t. They therefore yield joint convergence for bounded compactly supported tests that are Riemann integrable, in particular1_D, and convergence of the exponential expectation. This proves (1). Equivalently mu_* can be realized as the whole-plane modulo-constant chaos multiplied by an independent uniform phase; its neutral moment kernel is exactly the right side of (7) without kappa^k.

For (2), the source critical spin-field theorem and Green diagonal convergence give on compact interior tests the *raw* limit kappa mu_D. Explicitly, source full-variance chaos is exp[R_D(z,z)/(2K)] mu_D(z), whereas removing its lattice Green correction multiplies by exp[−(R_D(z,z)−R_D(0,0))/(2K)]. Their product is the constant kappa. No spatial weight is left.

We must also remove a boundary collar. Whitney-decompose Q_n into lattice squares B of side r whose enlarged parent squares stay inside Q_n, with O(n/r) boxes at each dyadic scale r. For boxes in a collar of widthdelta n only scales r<=Cdelta n occur. The conditional boundary of each parent square is arbitrary; the Messager–Miracle-Sole–Pfister aligned-boundary inequality bounds its zero-field two-point functions by the parent's all-zero boundary law. Source interior collision bounds then give

    ||sum_B e^(i theta_x)||_2 <= C r²a_r.

Minkowski and a_r<=C r^(-1/8)(log(e+r))^(1/16) imply

    ||sum_(collar) e^(i theta_x)||_2
       <= C n sum_(dyadic r<=Cdelta n) r^(7/8)(log(e+r))^(1/16)+C n.

The Cn term includes lattice boundary/singleton boxes. After division by n²a_n, its limsup is bounded by C delta^(7/8). Taking all Whitney scales also gives a uniform second moment for the entire normalized block. The source absolute-moment estimate (8) applies to all its nonnegative weights, so it gives uniform exponential integrability of the whole block and all collars. For each fixed p the normalized collar Lp norm is at most C sqrt(p)delta^(7/8) in the lattice limsup. Thus one first removes the collar at fixed delta, takes n→infinity by the compact-interior theorem, and then delta↓0. This constructs the UV continuum total mass on D consistently with its ordinary L² definition and proves (2) and the fixed-t exponential convergence.

## 4. The exact increment sandwich

Let V_n=Q_n\boundary Q_n and use all-zero boundary on Q_n. For fixed h>=0, the conditional Gibbs law on V_n inside an infinite uniform-field state has arbitrary exterior phases. After combining any one-site boundary terms with h, their Fourier magnitudes are at most h plus their all-zero boundary strengths. Proposition1 of Messager–Miracle-Sole–Pfister (1978) therefore gives

    |V_n| m(h) <= E^+_(Q_n,h) sum_(x∈V_n) cos theta_x.

Integrating in h from0 to h_0 yields

    Delta p(h_0) <= |V_n|^(-1)
        log E^+_(Q_n,0) exp[h_0 sum_(x∈V_n) cos theta_x].                (10)

For the lower bound, in a finite outer free box introduce the field h only on Q_n. Ginibre's covariance inequality for cos monomials says that increasing any other nonnegative one-site field increases each expectation cos theta_x. Hence

    d/dh log E_outer,0 exp[h X_Qn]
       <= sum_(x∈Q_n) E_outer,uniform h cos theta_x.

Integrate from0 to h_0, then take the outer thermodynamic limit at this fixed Q_n. The free-boundary thermodynamic limits are translation invariant: Ginibre monotonicity of cosine-character expectations under adding ferromagnetic edges gives the nested-box limit, and translation invariance follows by squeezing translated boxes between larger and smaller centered boxes. At positive h, Lee–Yang gives differentiability of p, and the usual convex thermodynamic variational comparison forces the magnetization of every translation-invariant limit state to equal p'(h). No full Gibbs-state uniqueness is needed. Expectations are bounded by1, so dominated convergence in h suffices, including the irrelevant endpoint h=0. This gives

    |Q_n|^(-1) log E_0 exp[h_0 X_Qn] <= Delta p(h_0).                    (11)

Using V_n rather than Q_n in (10) only removes O(n) fixed boundary spins. For h_n=t/(n²a_n), n² times their per-site pressure contribution is O(h_n n)=O(t/(na_n))→0, and |V_n|/n², |Q_n|/n²→4. Consequently (1),(2),(10),(11) prove, for every fixed t>0,

    (1/4)F_*(kappa t) <= liminf n² Delta p(t/(n²a_n))
       <= limsup n² Delta p(t/(n²a_n)) <= (1/4)F_D(kappa t),              (12)

where F_*(t)=log E exp[t Re mu_*(D)] and F_D(t)=log E exp[t Re mu_D(D)]. Ordinary boundary energy estimates never enter (12).

## 5. Limits and contribution boundaries

The pinned finite comparisons, k-nest attachment, single-lift confinement, pin-localization identity, collision removal, Lee–Yang moment determinacy and field monotonicity all have explicit source/classical antecedents. The multi-arc extension in Sections1–2 is a finite adaptation of the same source operations, not a new uniform-in-k estimate. This note alone does not prove T216A: it still requires the equality

    lim_(t→infinity) F_D(t)/(4t^(16/15))
       =lim_(t→infinity) F_*(t)/(4t^(16/15)) in(0,infinity).

No comparison constant or exponent-only statement suffices. The exact equality is now proved in the separately attributed continuum-boundary-pressure.md, copied with its external parent hash in parent-provenance.json. The subsequent scale inversion and convex secant differentiation are technical bookkeeping, not the proposed substantial operation.
