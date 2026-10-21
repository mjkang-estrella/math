# Global character construction on a compact carrier

Prefreeze working calculation; no theorem is nominated. Use N and odd d≥3 from CARRIER.md. Suppose a faithful, jointly continuous Z_p action on N is given. This is a p-adic calculation, not a reduction of arbitrary acting groups on arbitrary ENRs to Z_p.

## Fixed test and concentration

Pass to a sufficiently small open subgroup H≅Z_p. It remains faithful. Passing through squares makes the action orientation preserving, including p=2. For the fixed nonzero-degree map f:N→S^d, uniform continuity on compact N permits H to be chosen so that all f(gx) lie uniformly close to f(x). The normalized Haar average

    x ↦ (∫_H f(gx) dg) / ||∫_H f(gx) dg||

is H-invariant, nonzero, and homotopic to f by normalized interpolation. It factors as aq for q:N→Y=N/H and a:Y→S^d. Fix this H and this a once and for all. Write G=H from now on. The coefficient μ of (aq)_*[R_N] is fixed, independently of k and of the concentration region.

For every k≥1, faithfulness and the closed-subgroup classification of Z_p give a point with stabilizer contained in p^kG. In N/(p^kG), its G/p^kG orbit has p^k distinct points. Choose disjoint neighborhoods, intersect their translates, and project. This gives a nonempty open V⊂Y and a locally constant function β:q^{-1}V→μ_{p^k} with

    β(gx)=ζ^{g mod p^k} β(x),       ζ=exp(2πi/p^k).

This construction needs no free open subset for the original infinite group.

Set F=Y\V and F_N=q^{-1}F. The restriction H^d(N;Q)→Čech H^d(F_N;Q) is zero. Indeed U=N\F_N is nonempty open. Oriented local duality identifies H_c^d(U;Q) with H_0(U;Q), and its map to H^d(N;Q)=Q takes any component generator to the orientation generator. The compact-support exact sequence for (N,F_N) now kills the restriction. The proper zero-dimensional orbit map F_N→F has injective rational Čech pullback: average locally constant functions on each orbit to split the constant-sheaf unit, exactly as in the source orbit-injectivity proof. Thus

    (a|F)*γ=0 in Čech H^d(F;Q).

The source's finite-nerve odd-sphere argument supplies s=s(k)>0 such that D_s a|F is nullhomotopic. Its sphere-valued closed-subset homotopy extends to a neighborhood by the vector extension/normalization construction; multiplying the homotopy parameter by a cutoff extends the change over Y. Therefore

    D_s a ≃ h,         h constant on Y\V.

Neither s nor the homotopy is uniform in k. This is harmless because cancellation occurs only after tensoring with Q. No geometric coordinate ball in N is used for concentration.

## Integral summands without a quotient splitting assumption

Let Λ be the union of the p-power roots of unity. For T acting on q_*C_N by pullback under -1∈G, set H_λ=ker(T-M_λ). The zero-dimensional orbit proof gives

    Rq_*C_N = q_*C_N = ⊕_{λ∈Λ} H_λ.

This is an algebraic sheaf sum, not a norm-completed representation. Compact-fiber soft cohomology gives R t_*(⊕ H_λ)=⊕R t_*H_λ for every compact test t:Y→X. Write A_t=R(tq)_*C_N. For any finite partition Λ=⊔D_i, the algebraic projectors give a finite decomposition

    A_t=⊕B_i(t),       B_i(t)=Rt_*(⊕_{λ∈D_i}H_λ).

By CARRIER.md A_t belongs to T(X); thickness puts each B_i(t) in T(X). These are global ambient summands before passage to a Verdier quotient. There is no inference that arbitrary idempotents in that quotient split.

The form α_t is the orientation pushforward with coefficient B. Orientation-preserving G acts isometrically. J=M_i satisfies J†=-J, T†=T^{-1}, and M_λ†=M_{λ^{-1}}. If λ∉E, the operator T^{-1}-M_{λ^{-1}} on H_E is invertible, by the componentwise inverse (μ^{-1}-λ^{-1})^{-1}. No boundedness of these inverses is required in this algebraic category. Adjointness kills the cross pairing from the λ summand to E; the derived coproduct property kills it from any D disjoint from E. This also handles distinct conjugate eigenvalues as real subrepresentations because the common complex scalar structure is retained. The finite blocks are consequently nondegenerate symmetric summands.

Define integral classes x_i(t)=[B_i(t),α_i(t)]∈E_d(X). Their sum is

    Σ_i x_i(t)=[A_t,α_t]=2(tq)_*[R_N].                    (1)

Proper covariance follows from composing direct images of the same eigensheaves. Homotopy invariance of x_i follows by pushing their global projectors through C_d and its homotopic projections, followed by a finite subdivision. Neither pullback invariance of T nor invariance under arbitrary homotopies of an ENR source is asserted.

## Equal parts and a fixed denominator

Choose a transversal D_0 for Λ/μ_{p^k} and D_i=ζ^iD_0, 0≤i<p^k. For concentrated h, let b be its constant value outside V. On the target complement of b, multiplication by β is a coefficient isometry and

    T M_β = M_{ζ^{-1}} M_β T.

It cyclically identifies B_i(h) with B_{i-1}(h) there. A small contractible open U_b around b is enough to view this isometry in T(S^d)/T(U_b), by the source germ theorem. The source's integral localization isomorphism E_d(S^d)→W_d(T(S^d)/T(U_b)) then implies

    x_i(h)=x_{i-1}(h) in E_d(S^d).

This uses no extension of β across the bad fiber. Covariance and homotopy give D_{s*}x_i(a)=D_{s*}x_j(a). In the rational sphere group the degree map acts by s, so all x_i(a) have the same rational image. Combining with (1),

    x_i(a)⊗Q = (2μ/p^k)u_d.                              (2)

The pinned source gives the single lattice L_d^{-1}Z u_d containing the image of E_d(S^d), with L_d=2^{3(9^d-1)/4} permitted. This denominator is fixed before k varies. Equation (2) therefore yields

    2L_d μ / p^k ∈ Z for every k≥1,

which forces μ=0: a fixed nonzero rational has finite p-adic valuation. This is the strongest integrated reduction retained here. It closes membership, orthogonality, integral lifting, concentration and degree cancellation. It does not establish μ≠0 for the full compact ENR homology-manifold scope. No partial theorem is offered in place of that missing detection operation.
