# Source083 hard truncations: integrated prefreeze calculations

PREFREEZE / no nominee. No theorem has been frozen. These are author calculations relative to stipulated pinned inputs, not a full author proof, an independent correctness or contribution verdict, or a count. The old full maximal-transform question is retained; it is not renamed. The new working reductions below are credited as source/classical compositions.

## 1. The actual full question and its inherited scope

For every planar Lipschitz unit field v:R²→S¹ with Lip(v)≤1, the exploratory question is whether there are absolute a∈(0,1/2), C<∞ with

    || sup_{0<epsilon<a} | ∫_{epsilon<|t|<a} f(z-tv(z)) dt/t | ||₂
       ≤ C ||f||₂                                                  (M)

for every complex Schwartz f, with constants independent of the field and of all frequency and time cutoffs. The supremum ranges over all positive inner radii, inside the spatial norm. The lines are straight with direction frozen at the output point. Neither flow curves nor one-coordinate, analytic, finite-frequency or lacunary fields replace this scope. Scaling would supply a/Lip(v) for nonconstant fields; constant directions have the classical one-dimensional theorem.

Source083 thm:main places the supremum OUTSIDE the L² norm. Its principal-value assertion on Schwartz functions gives an L² extension; this is not (M). The original r65 flow note explicitly states (M), the diagonal note retains every finite number of cutoffs and all frequency widths, r63 pays an interval-selected coefficient bound and records a rough-mask commutator obstruction, and r67 gives the fractional short-cutoff route. These actual originals were read before consolidation. Their protected checkpoint/scope archives were not read, so no complete archive clearance is claimed. All old statements stay immutable.

The source localization reduces the calculation to

    V_t f(x,y)=f(x-t,y-tu(x,y)),   |u|≤1, Lip(u)≤L,
    H^epsilon f=∫_{epsilon<|t|<a} V_t f dt/t,            aL<1/10.

The local horizontal supports and bounded-overlap rotations are exactly those in source red:fixed-time and red:band-implies-main. For a maximal inner endpoint, the change from epsilon to epsilon v₁(z) is absorbed into the supremum itself. The variable outer endpoint lies in one fixed comparable annulus and its absolute integral is L² bounded by the source fixed-time change of variables. Thus local-to-global geometry is paid; it is not the remaining obstacle.

## 2. Diagonalize the time integrand, before selecting a cutoff

Choose the real vertical square partition P_w=p(wD_y), Σ_w P_w²=Id on L²(R²). The zero vertical-frequency line has plane Lebesgue measure zero. The source proof of red:commutator, including its Carleson estimate and low-output interaction, and red:composition-commutator gives, for every finite set of w and arbitrary signs sigma_w,

    || [Σ_w sigma_w P_w,V_t] f ||₂ ≤ C L |t| ||f||₂.                 (2.1)

Here the L factor may be retained by applying the displayed proof with Lip_y(u)≤L and aL bounded; constants depend only on the fixed multiplier seminorms and that smallness bound. No spatial cutoff multiplier occurs inside the commutator.

Averaging the squared norm over independent signs yields

    Σ_w ||[P_w,V_t]f||₂² ≤ C² L² t² ||f||₂².                        (2.2)

The synthesis map (h_w)↦Σ_w P_w h_w has norm at most one: by duality and the square partition, |Σ<h_w,P_w g>|≤||(h_w)||_{L²(l²)}||g||₂. Consequently

    R_t = Σ_w P_w[P_w,V_t]
        = V_t - Σ_w P_w V_t P_w,
    ||R_t f||₂ ≤ C L |t| ||f||₂.                                 (2.3)

Both sums converge strongly. For the second use Σ||V_tP_w f||₂²≤CΣ||P_w f||₂²; for the commutator sum use (2.2). At finite truncation the identity first contains (Σ_{w in W}P_w²)V_t, not V_t; take W↑2^Z. This distinction prevents a spurious finite-set remainder. Strong continuity of V_t follows by density from its bi-Lipschitz composition bound; the integral is well-defined as a Bochner integral for positive inner endpoints. The absolutely integrable error also has an L² limit at zero.

Put D^epsilon=∫_{epsilon<|t|<a}Σ_w P_wV_tP_w dt/t, so H^epsilon=D^epsilon+E^epsilon with E^epsilon=∫R_tdt/t. This is the original r65 off-diagonal reduction. DPGTZK Theorem1.1 is stronger in another direction: its narrow-band off-diagonal error is summable in absolute value across widths, in every 1<p<∞. Its actual Section2.5 proof integrates the Lipschitz factor against dt/|t|. The beta-number/outer-Carleson proof of that theorem was read, including the operative internal precursor proofs. These are paid operations.

## 3. The same error is controlled in total variation

For any increasing radii 0<epsilon_0<...<epsilon_N≤a, the differences of E are integrals over disjoint symmetric annuli. Pointwise,

    Σ_{j=1}^N |E^{epsilon_j}f-E^{epsilon_{j-1}}f|
       ≤ ∫_{0<|t|<a} |R_t f| dt/|t|.

An anchor at epsilon=a has value zero. Therefore both the full maximum and the total 1-variation, and hence every r-variation for r≥1, satisfy

    ||V¹_epsilon(E^epsilon f)||₂ ≤ 2 C L a ||f||₂.                  (3.1)

The right side is finite almost everywhere by Minkowski and (2.3). This justifies taking the supremum over finite rational partitions; continuous representatives in the endpoint on compact positive intervals extend it to all partitions. L² approximation then gives the error family for arbitrary L² inputs.

This calculation improves the organization of the remaining obligations, not the contribution grade: r65 already integrated the absolute time error for the maximum, and disjointness of annuli immediately supplies (3.1). No new cancellation principle is required.

## 4. The fractional hard-cutoff error is also already paid off the diagonal

Let delta_k=a 2^{-k-1}, k≥0, and 1≤s≤2. Define

    A_k(s)f=∫_1^s [V_{delta_k r}-V_{-delta_k r}]f dr/r.

Then H^{s delta_k}=H^{delta_k}-A_k(s). The original r67 route controls the maximum inside a dyadic annulus by a W^{alpha,2} norm in s for 1/2<alpha<1. Preserve that exact fractional range; an H¹ square sum fails even for a constant direction.

Use the same definition with R in place of V and call the result B_k(s). By (2.3),

    ||B_k(s)f||₂ ≤ C L delta_k (s-1)||f||₂,
    ||(B_k(s)-B_k(r))f||₂ ≤ C L delta_k |s-r| ||f||₂.               (4.1)

These are L² operator estimates, not pointwise Lipschitz assertions about f. Tonelli applied to the nonnegative fractional norm and then (4.1) gives

    ∫_{R²} ||B_k(·)f(z)||²_{W^{alpha,2}([1,2])} dz
       ≤ C_alpha L² delta_k² ||f||₂²,          0<alpha<1.           (4.2)

Indeed the double-difference contribution is bounded by a constant times

    ∫_1²∫_1² |s-r|^{1-2alpha} ds dr
       = 2/[(2-2alpha)(3-2alpha)],

which is finite precisely for alpha<1. Since Σ_{k≥0}delta_k²=a²/3,

    Σ_k ∫ ||B_k(·)f(z)||²_W dz ≤ C_alpha (La)² ||f||₂².             (4.3)

Thus the off-diagonal part of r67's short-cutoff square estimate is completely controlled. The short-cutoff square estimate for V is equivalent, up to this bounded additive error, to that for the diagonal integrand. This follows from the triangle inequality in the Hilbert direct sum L²_z(l²_k(W^{alpha,2}_s)). It does not use a pointwise vector-valued Littlewood–Paley theorem with a maximal output norm.

Together, (3.1) and (4.3) remove the off-diagonal commutator from both the long and short endpoint problems. The surviving hard-cutoff issue is diagonal. These deductions are explicit source/classical consequences and are not nominated as substantial results.

## 5. Measurable cutoff selection preserves more of the one-width proof than a bare coefficient bound

Fix exactly the finite source reference-line setting, one w, one W=mw, the original packet support/seminorm bounds, and a measurable radius rho(z). Replace each adjoint coefficient by

    a_s^rho = |R_s|^{-1}∫ 1_{rho(z)<ell_s} g(z)
                       overline{b_s(u(z)) Psi_s(z)} dz,
    ||g(z)||_H≤1_E(z).

The selected main/error split inserts the same indicator in both terms. The original r63 coefficient proof gives

    Σ_{z_s in Q, ell_s≤length(Q)} ||(a_s^rho)^main||² |R_s|
       ≤ C |Q|.                                                 (5.1)

In duality the selected scale condition is the interval

    rho(z)<ell_s≤w/|u(z)-t|.

The source separated-synthesis theorem already controls the maximum of all such intervals. Its polynomially weighted proof gives (5.1) with no regularity of rho. The source single-scale error majorant is unchanged because the extra indicator has modulus at most one:

    Σ_{ell_s=ell} ||(a_s^rho)^err|| B_{s,n}^t
       ≤ C (k_{ell,n'} *_x k_{W,n'} *_{Y_t} f_d),
    Σ_d f_d≤C(1+log B).                                         (5.2)

Now follow the actual conc:line-moments proof, which was read in full. Short-scale local means of (5.2), long-scale derivative bounds of the smooth envelope convolution, and John–Nirenberg still give the same polynomial moment bounds for the positive error sum. For the square function, (5.1) gives Σ||a_s||² ell_s≤Cr on each r×W center box; the factor W cancels exactly as in the source. Main synthesis coefficients are constants after integration. Their new dependence on rho does not multiply the synthesizing wave by a nonsmooth function of the evaluation point.

Consequently the source Fourier-annular variation comparison applies on every reference line to these selected main coefficients. Polynomial multiplication preserves frequency support, the source masks preserve the separated horizontal annuli, and deterministic packet subcollections are still fixed before evaluation. The short-scale L² variation estimate, long-scale oscillation bound, and John–Nirenberg step yield the same every-line polynomial L^b bounds for the adjoint synthesis built from a_s^rho, under these unchanged one-width packet/top-mask hypotheses. This is an explicit reuse of the source proof, not a new martingale theorem or a theorem for arbitrary nonsmooth synthesizing packets.

The ordinary scalar tree estimate is stable under the same suffix selection. In source tile:lem-tree, short terms and nonseparated/error terms only shrink in absolute value. For the separated main sum on a Whitney cell I, the length interval becomes

    max(C_W |I|,rho(z))<ell_s≤w/|u(z)-t|.

Its absolute value is bounded by the very same maximal interval synthesis used in tile:eq-cell-suprema. The cell supremum is over all deterministic interval sums before choosing rho(z); every such sum retains the source low-frequency support used for smooth reproduction. The density set E∩{u∈Omega(t,l')} and its bound are unchanged. Hence the original density-times-size tree bound survives. This observation credits the strong tree machinery already present and prevents calling ordinary tree selection wholly unpaid.

These facts do not assert that the entire single-width logarithmic-gain proof has been reassembled here. The complete popular-forest, finite-phase, hierarchy, residual and final assembly bodies were not all freshly read. Nor do the facts address all widths simultaneously or identify hard time cutoffs with smooth model scales. No theorem is frozen from them.

## 6. What the primary variation proof supplies

Guo1610.05233v1 was read through its theorem, reductions, wave-packet model, organization, and full written tree proof. Its actual operator is variation of smooth dyadic frequency-scale partial sums, localized to one annulus. It has weak (2,2) and strong p>2 bounds, uniformly in the annulus, for Lipschitz fields. It is not the hard-inner-radius maximum in (M).

Its tree proof supplies a stronger compatible operation than merely a fixed-tree Hilbert bound. It compares variable-direction packets to a horizontal reference synthesis, uses a Lipschitz direction-thickening argument to control the density on each horizontal fiber, freezes a maximizing variation partition at a reference point on that fiber, bounds the displacement error by packet derivatives, and applies one-dimensional variation after summing cells. The organization and some tail/two-tree steps are cited there to Bateman/Lacey–Li rather than fully repeated. Those original transitive bodies were not freshly read here. The source's fully written separated synthesis and reference-line variation proofs cover the precise operations used in §5; no unproved transitive variant is imported.

There are three compatibility distinctions:

1. A finite-dimensional Hilbert space of narrow bins at one width is not a Banach space of all cutoff values. The source constants are dimension-free in the first setting; this does not establish a maximal-valued reassembly theorem.
2. Single-annulus weak type cannot simply be summed over all vertical widths to get (M). The r65 sign-multiplier example shows that even fixed-operator L² bounds, perfect band diagonalization and strong individual-band maxima do not imply a full maximum for arbitrary operator families. That example is not a counterexample for actual ordered Hilbert truncations.
3. Source red:scale-truncation gives an L¹ kernel error for each FIXED pair of radii. The supremum of those errors is not bounded by the supremum of their L¹ norms. A positive line-average maximum or the actual fractional short-cutoff estimate must be supplied. The source fixed-annulus endpoint error is also different from taking all annuli at once.

## 7. A compatible transverse-frequency refinement of the flow comparison

This tests the strongest flow route without pretending that curvature is small on unrestricted L². Let Phi_t be the flow of b=(1,u). Its first coordinate is exactly x+t. Write

    F_t(z)=(x-t,y-tu(z)),
    Phi_{-t}(z)=(x-t,Y_t(z)).

Because |u|≤1 and Lip(u)≤L, |b|≤sqrt(2), and

    |Y_t(z)-(y-tu(z))|
       ≤ ∫_0^{|t|} L |Phi_{-sgn(t)s}(z)-z| ds
       ≤ (L sqrt(2)/2)t².                                      (7.1)

For La sufficiently small, F_t-Id and Phi_{-t}-Id have Lipschitz seminorms bounded respectively by L|t| and exp(L|t|)-1. Their convex interpolants G_{t,theta} are bi-Lipschitz with uniformly controlled inverse Jacobians. The horizontal coordinate is identical in the two maps. The fundamental theorem of calculus in the VERTICAL coordinate therefore gives

    ||(f∘F_t-f∘Phi_{-t})||₂ ≤ C L t² ||partial_y f||₂.              (7.2)

For h_w=P_w f, Bernstein in y and the separate composition bounds imply

    ||h_w∘F_t-h_w∘Phi_{-t}||₂
       ≤ C min(1,Lt²/w) ||h_w||₂.                                (7.3)

This is independent of horizontal frequency; the earlier all-frequency gradient estimate can be sharpened in the local slope setting. Put b_w=min(a,sqrt(w/L)) when L>0; L=0 gives zero error. Absolute integration on |t|≤b_w bounds the total variation of the comparison error by C L b_w²/w ||h_w||₂≤C||h_w||₂. On all short times the crude bound is

    C [1+log_+(a sqrt(L/w))] ||h_w||₂.                            (7.4)

The same low-time region has a controlled fractional short-cutoff square sum: on dyadic annuli with 2delta_k≤b_w, the endpoint increment bound is C L delta_k² |s-r|/w. The sum of squared bounds is O(L² b_w⁴/w²)≤C. The at most bounded number of annuli crossing b_w can be handled by the fixed-time estimate. Thus a genuinely oscillatory treatment is only needed above the parabolic time sqrt(w/L) in this bandwise flow comparison.

The flow itself has the classical maximal theorem by local transference and its bounded Jacobian, as r65 explicitly proves. But selecting b_w separately for each width and then summing is another multiwidth operator, not one common flow truncation. A spatial shear does not commute with all vertical band projections, and the maximum is outside their sum. We do not exchange these operations. The r65 unit-field curvature example already rules out a uniform O(a) smallness assertion for the complete frozen-flow error. Equations (7.1)–(7.4) do not contradict that example: its significant transverse frequency is w≈a².

This refinement is a paid geometric/first-derivative calculation, not a full variable-curvature maximal theorem. No new analytic or one-coordinate substitute is nominated.

## 8. Exact residual obligation and outcome

The exact remaining maximal estimate in the local model is

    || max_{1≤j≤N} |Σ_w P_w H^{epsilon_j} P_w f| ||₂ ≤ C||f||₂,    (D)

for every finite N, every choice 0<epsilon_j<a, every permitted u, and all widths (strong sums), with C independent of N, frequency ratio and time-scale range. By §2–3 and the paid localization, (D) is equivalent to the original full maximal question up to an absolute additive operator bound. This is an exact reduction, not a new theorem or a new name for a result.

A more structured sufficient route retains r67's decomposition: prove the diagonal dyadic endpoint maximum and, for some fixed 1/2<alpha<1, the diagonal fractional short-cutoff square estimate uniformly over all scales and widths. Section4 pays its off-diagonal complement completely. The low-time flow calculation pays only its precisely stated bandwise range. Section5 pays selected one-width coefficients, ordinary tree control and reference-line moments. These compatible pieces should not be advertised as wholly missing operations.

What is still not supplied is an estimate using the common ORDER of the actual time cutoffs that survives simultaneous frequency reassembly and hard endpoints. No complete construction satisfying (D), or both sufficient structured estimates, was obtained. No demonstrably nonroutine new operation beyond the strongest read source/primary/project composition was established. Failure of a generic Banach-valued shortcut, a common-cell choice or a positive-kernel estimate is not evidence that the intended theorem is impossible or that its proof would qualify as substantial.

There is therefore no frozen nominee. The family is distinct from r150's weighted logBM work, but actual original history shows it is not new to the project. All old scopes and dispositions, including the user's protected targets, remain unchanged. No independent grade, acceptance, count, worldwide-priority or exhaustion claim is made.
