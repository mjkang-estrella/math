# Source369: boundary geometry of a double first-eigenspace map

PREFREEZE research record. No author-proof nominee is frozen. No correctness, contribution, acceptance, or count is assigned. The global eigenmap construction below is already present in the exact original I214 mathematics read in this round; it is not offered again. The positive-curvature extension is executed completely, but its decisive operation is the classical boundary Taylor argument paid by Jerison–Nadirashvili. The remaining all-domain boundary problem is not solved.

## 1. Fixed class, normalization, and paid inputs

Let Ω be a nonempty bounded simply connected planar open set with C∞ boundary, μ its first *positive* Neumann eigenvalue, and V its real eigenspace. All of Source369 at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, including its proof operations, is stipulated true. Here assume dim V=2 and fix an L²(Ω)-orthonormal real basis u,v. Write F=(u,v). An orthogonal change of basis preserves all Euclidean target distances and singular values. Reverse one basis vector when necessary so J=det DF>0 in Ω.

Source main theorem makes gradient evaluation V→R² injective at every interior point; its vector-form proof identifies the exact nullspace, with μ<λ_D eliminating the Dirichlet summand. In its boundary mechanism q=μ|Φ′|²dx, ||T||≤d=μ/λ_D<1, E≥0 has nullspace precisely Neumann gradients, and the reciprocal theorem supplies D_p=K(p,s)K(p,t)/N(s,t). Its injective Hilbert realization and multiplier identity give ΣE(b_jg)=|∇u(Φ(p))|²/2. Both the dense nonzero-gradient trace case and the open zero-gradient arc case are operative, the latter using boundary Cauchy uniqueness. All six sections and the boundary-sign figure were read before the present deductions. Extending the reciprocal theorem to bounded nonnegative subcritical potentials is already an internal source result, not a new parameter freedom.

The eligible original I214 proof establishes, at exactly the present smoothness and multiplicity, that F is an analytic diffeomorphism Ω→U, U has smooth strictly radial Jordan boundary around 0, and F is a homeomorphism of closures and a smooth diffeomorphism of their one-dimensional boundaries. In particular, if h(s)=F(γ(s)) for counterclockwise arclength on ∂Ω, then

    B(s)=det(h,h′)>0,       h′≠0.

For clarity, this does not come merely from local rank. The I214 proof first makes every zero level a single proper line using the two connected sign sets. The transverse eigenfunction is strictly monotone along that line, giving injectivity. Boundary even reflection, a half-integer Fourier Carleman estimate, and the harmonic leading Taylor polynomial establish finite-order boundary nodal zeros. Planar separation then forces exactly two simple endpoints. The boundary phase is consequently a one-sheeted circle covering. Equivalently, winding number and the constant sign of J give exactly one interior preimage. These are paid original operations, not this round's contribution. Their statements and proof sections were read, with administrative and grade sections excluded.

## 2. Exact boundary jets on the full smooth class

Let τ=γ′, let n be the inward normal, and write τ′=κn, n′=−κτ, so κ>0 on a round disk. For small t≥0 use

    X(s,t)=γ(s)+t n(s),       a(s,t)=1−κ(s)t,
    H(s,t)=F(X(s,t)),         h(s)=H(s,0).

Then det DX=a>0 and the Neumann condition is H_t(s,0)=0. The pulled-back componentwise Helmholtz equation is exactly

    H_tt − (κ/a)H_t + a^(−2)H_ss + κ′t a^(−3)H_s + μH = 0.       (2.1)

Indeed the Euclidean metric is a²ds²+dt², so Δ=a^(−1)∂s(a^(−1)∂s)+a^(−1)∂t(a∂t). This also fixes the curvature signs.

Put q=H_tt(s,0) and r=H_ttt(s,0). Evaluation and one t derivative of (2.1) give

    q=−h″−μh,
    r=κq−2κh″−κ′h′=3κq+2κμh−κ′h′.                         (2.2)

Define

    A=det(h′,q)=μB−det(h′,h″).

For D=det(H_s,H_t)=aJ, Taylor expansion with remainders uniform on a fixed compact boundary gives

    D(s,t)=A(s)t + κ(s)(3A(s)−2μB(s))t²/2 + O(t³),          (2.3)
    J(X(s,t))=A(s)t + κ(s)(5A(s)−2μB(s))t²/2 + O(t³).       (2.4)

The extra κA in (2.4) comes from dividing by a; dropping that factor would give an incorrect second normal derivative. Since D>0 for t>0, A≥0 at every boundary point. Thus the exact, non-strict image-curvature inequality is

    det(h′,h″) ≤ μ det(h,h′).                               (2.5)

This is an upper signed-curvature constraint, not convexity of U. If A(p)=0, (2.3) becomes D(p,t)=−κ(p)μB(p)t²+O(t³). Since μB>0, necessarily κ(p)≤0. Therefore

    κ(p)>0  ⇒  A(p)>0.                                    (2.6)

At a zero of A with κ<0 the normal image displacement is exactly cubic, after removal of tangential displacement: if d_U is the signed distance into U, then

    d_U(H(s,t)) = [A/(2|h′|)]t² + O(t³),
    A(s)=0 ⇒ d_U(H(s,t)) = [−κμB/(3|h′|)]t³ + O(t⁴).        (2.7)

To check the second formula, the quadratic vector q is tangent when A=0. The quadratic term in the Taylor expansion of d_U around h is then O(t⁴), so only n_U·r/6 enters the cubic term. Since n_U=rotation(h′)/|h′|, n_U·r=det(h′,r)/|h′|=−2κμB/|h′|. These statements are conditional identities on the source class; no global example with A=0 is claimed.

## 3. Complete positive-curvature consequence and its exact strength

Suppose now κ>0 on all ∂Ω. By (2.6), A>0 everywhere. This extra condition is compatible with a double eigenspace; examples are given in Section 5. The ensuing conclusions are for a fixed Ω, uniformly over orthonormal bases and normalized coefficient vectors, not effective uniform estimates over a geometric class.

Every boundary point is a quadratic fold. Here is a direct normal-form proof without invoking singularity-theory terminology as a black box. In a small target collar choose smooth coordinates (α,β), where α parametrizes the boundary and β=d_U. Choose α(h(s))=s locally. Then

    α(H(s,t))=s+O(t²),
    β(H(s,t))=c(s)t²+O(t³),     c=A/(2|h′|)>0.

The source change (s,t)→(σ,t)=(α(H(s,t)),t) is a diffeomorphism and preserves t=0. In these coordinates β=f(σ,t) satisfies f(σ,0)=f_t(σ,0)=0 and f_tt(σ,0)>0. Taylor's integral formula gives

    f(σ,t)=t² b(σ,t),
    b(σ,t)=∫₀¹(1−z) f_tt(σ,zt) dz >0

on a smaller collar. The source coordinate τ=t√b(σ,t) is smooth and has positive t derivative at the boundary. The map becomes exactly

    (σ,τ) ↦ (σ,τ²),       τ≥0.                             (3.1)

This is a one-sided fold, not a diffeomorphism of two-dimensional manifolds with boundary.

There are constants c_Ω,C_Ω>0 such that for every x,y∈closure Ω,

    c_Ω |x−y|² ≤ |F(x)−F(y)| ≤ C_Ω |x−y|.                 (3.2)

For the local lower estimate in fold coordinates, put δσ=σ−σ′ and δτ=τ−τ′. On a bounded chart, δσ²≤M|δσ|, while δτ²≤|τ²−τ′²| because τ,τ′≥0. Hence δσ²+δτ²≤√(M²+1)|(δσ,τ²−τ′²)|. The smooth source/target coordinate maps and their inverses are Lipschitz on smaller compact charts, yielding (3.2) there. On interior charts the inverse is smooth, which yields an even stronger linear local estimate. A finite cover of closure Ω has a Lebesgue number; pairs closer than that number lie in one of these smaller charts. On the compact set of pairs at larger separation, injectivity of the closure map gives a strictly positive minimum of |F(x)−F(y)|/|x−y|². This proves the lower estimate globally. Smooth extension to a neighborhood, bounded first derivatives locally, and compactness for far pairs give the upper estimate (or use convexity of Ω).

Thus F^(−1) is globally Hölder 1/2. This exponent is optimal for every such Ω: along an inward normal x_t=p+t n(p), q has a nonzero transverse component and

    |F(x_t)−F(p)| = (|q(p)|/2)t²+O(t³).

A Hölder exponent α>1/2 would give t≤C′t^(2α), impossible as t↓0.

Similarly, for the smallest singular value σ_min(DF), there are fixed-domain constants c,C>0 with

    c dist(x,∂Ω) ≤ σ_min(DF(x)) ≤ C dist(x,∂Ω)             (3.3)

for all x∈Ω. In a collar, J/t→A>0 uniformly and σ_max tends to |h′|>0, while σ_min=J/σ_max. Away from the collar, all quantities are positive on a compact set, so adjust constants. Consequently every w=a₁u+a₂v with a₁²+a₂²=1 satisfies |∇w(x)|≥c dist(x,∂Ω). This includes all directions in the exact eigenspace, not arbitrary vectors in a split spectral cluster.

The constants in (3.2)–(3.3) use actual h, A, finite-chart bounds and an interior inverse margin. No expression in diameter, inradius, area, boundary norms or spectral gap alone has been proved. Under dilation Ω→LΩ with L²-normalized eigenfunctions F_L(x)=L^(−1)F(x/L), the lower constant in (3.2) scales as L^(−3), its upper constant as L^(−2), the inverse Hölder constant as L^(3/2), and the lower coefficient in (3.3) as L^(−3). These scaling checks preclude an amplitude-free or scale-free bound.

## 4. Why the positive-curvature step is already paid

The complete actual proof of Jerison–Nadirashvili Lemma 6.6 was read through its ending, separately from the following heat-flow paragraph. It uses the Neumann condition to fix a cubic Taylor coefficient when the normal second derivative vanishes at a positive maximum, contradicting maximality under positive curvature. The proof uses local data for that step; its spectral and symmetry context does not supply an additional new operation here. Its HTML extraction loses signs, so the independent calculation (2.1)–(2.4), not an ambiguous transcription, fixes the signs used in this record.

The relation is concrete. If A=0 then det(h′,h″)=μB>0: the image curve is locally strictly convex at that point. The outward target normal a then makes a·F have a positive local boundary maximum, because a·h=B/|h′|>0 and a·h″=−μ a·h<0. The already-established closure homeomorphism places its nearby interior image on the inward side. The classical local maximum Taylor contradiction applies. Equation (2.3) is a simultaneous two-eigenfunction version of that same third-order operation. The scalar-to-map translation, fold coordinates, and compact patching do not identify a distinct substantial operation.

Bañuelos–Pang, Sections 2–4, was also read in full operative extent. Their conformal upper-half-plane reduction gives Δψ+qψ=0, ψ_y=0. At a positive critical boundary value with ψ_yy=0, differentiation gives ψ_yyy=−q_yψ. Positive original curvature fixes the sign of q_y. Their subsequent level-set argument treats the case with nonzero normal second derivative and the degenerate case, including the figure-based monotonicity alternatives. This is a further actual antecedent for the boundary-jet mechanism, not evidence that a new all-domain conclusion is free.

## 5. The positive-curvature class is not empty or confined to disks

For the unit disk, separation in angular Fourier modes gives a double first positive mode f(r)cosθ,f(r)sinθ with f(r)=J₁(αr), J₁′(α)=0 at its first positive derivative root. One can identify its position without numerical Bessel values. The trial function x has Rayleigh quotient 4, and equality cannot hold for the Neumann minimizer because x has nonzero normal derivative; hence the first n=1 radial quotient is <4. Angular frequencies n≥2 have quotient at least n²≥4. A nonconstant n=0 radial eigenfunction has derivative solving the n=1 radial equation with Dirichlet value zero at r=1, so its eigenvalue is at least the first n=1 Dirichlet value, strictly larger than the first n=1 Neumann value. Strictness follows from variational equality plus simultaneous Dirichlet and Neumann data for the radial ODE. Thus the first positive eigenspace is exactly the sine/cosine pair. Here A=(μ−1)f(1)²>0, also directly forced by (2.6).

There are noncircular examples. Take r(θ)=1+ε cos(3θ), for sufficiently small nonzero real ε. These smooth domains are simply connected and have positive curvature: the numerator of the polar curvature is r²+2r_θ²−r r_θθ, uniformly close to 1. Their threefold dihedral symmetry preserves the spectrum.

For completeness the multiplicity compatibility does not assume that arbitrary eigenvector branches remain first modes. Use a smooth radial cutoff χ, zero near the origin and one near r=1, and T_ε(x)=(1+εχ(|x|)cos3θ)x from the disk. It is a D₃-equivariant diffeomorphism for small ε. On the fixed disk the exact pulled-back forms are

    a_ε(f,g)=∫ det DT_ε (DT_ε^(−T)∇f)·(DT_ε^(−T)∇g),
    b_ε(f,g)=∫ det DT_ε f g.

These carry the Neumann condition as the natural conormal condition. Uniform C¹ closeness yields |a_ε−a₀|≤C|ε| a₀ on quadratic forms and |b_ε−b₀|≤C|ε| b₀. The min–max principle gives convergence of each fixed eigenvalue and retains the gap around the two-dimensional first-positive disk cluster. The solution operators for a_ε+b_ε converge in norm: subtract their variational equations, use uniform coercivity in H¹ and the displayed form bounds, then use H¹→L² compact inclusion. After the mass identification f→(det DT_ε)^(1/2)f, these are self-adjoint operators on one fixed L² space. The Riesz projector around the isolated cluster therefore converges in operator norm, by the resolvent identity on a fixed contour. Its rank is two, and its restriction to the disk cluster is an isomorphism for small ε. It intertwines the D₃ actions because the coefficients and contour operators are equivariant.

The disk cluster carries the standard irreducible real D₃ representation. On that representation a self-adjoint commuting operator is scalar: commuting with rotation by 2π/3 gives aI+bR₉₀, and symmetry (or the reflection) forces b=0. Thus the two perturbed eigenvalues coincide. The separated constant eigenvalue remains zero and the next cluster stays higher, so this is the exact first-positive eigenspace. This proves the claimed compatible noncircular examples. It is a standard form/projector argument supporting compatibility, not a separate nomination.

## 6. Local cubic and quartic models: what they do and do not establish

A local model can disprove an implication from purely local PDE data, but cannot by itself disprove a theorem about global first modes. The following models are explicitly not asserted to extend to a smooth bounded simply connected domain with the required global spectrum and normalization.

### 6.1 Negative-curvature cubic model

Near an arc of r=1, take the local domain r>1 and μ=1. Solve the analytic ODE

    f″+r^(−1)f′+(1−r^(−2))f=0,      f(1)=1, f′(1)=0.

Then f″(1)=0 and f‴(1)=−2, so f(1+t)=1−t³/3+O(t⁴). Let F(r,θ)=(f(r)cosθ,−f(r)sinθ). Its two components solve ΔF+F=0 and have zero normal derivative on r=1. For small t>0, det DF=−f f′/r=t²+O(t³)>0, so every nonzero real combination has nonzero gradient there. In the counterclockwise boundary orientation for the local exterior, κ=−1 and B=1. The image approaches its circular boundary cubically, exactly as (2.7) predicts. A local inverse exponent greater than 1/3 fails. There is no imposed outer boundary condition and no claim about the first eigenvalue of a global domain.

### 6.2 Flat-boundary quartic model with an explicit convergent construction

Let μ=1, x be tangential and t inward. Define

    E(x)=exp(x²/2),
    h₁(x)=E(x)−x∫₀ˣ E(z) dz,       h₂(x)=x.

Both solve h″−x h′+h=0. Let h=(h₁,h₂), and define the even-in-t analytic solution

    H(x,t)=Σ_{j≥0} (−1)^j t^(2j) (∂x²+1)^j h(x)/(2j)! .    (6.1)

This is a genuine convergent series locally, not a formal Cauchy expansion. On a complex x-disk where h is analytic, Cauchy gives |∂x^(2k)h|≤M(2k)!/ρ^(2k) on a smaller disk. The absolute jth term of (6.1) is bounded by M|t|^(2j)(1+ρ^(−2))^j, using (2k)!≤(2j)!. On a still smaller product neighborhood the differentiated series also converges, since only polynomial j factors and a reduced Cauchy radius are needed. Thus H_tt+H_xx+H=0, H(x,0)=h(x), H_t(x,0)=0. The second component is exactly x cos t.

Here B=det(h,h′)=E(x)>0 and q=−h″−h=−x h′, so A=0 identically along the flat edge. Expanding one more order gives

    det(H_x,H_t)= [E(x)(1−x²)/3]t³ + O(t⁵).                (6.2)

The remainder is uniform for |x|≤δ<1. Therefore the Jacobian is positive on a sufficiently small half-rectangle, and every nonzero combination of the two components has nonvanishing interior gradient there. At x=0,

    H(0,t)=(1−t⁴/12+O(t⁶),0).

The boundary point is approached at fourth order, and no local inverse Hölder exponent >1/4 holds at that point. This demonstrates that a 1/2 or 1/3 boundary theorem cannot be obtained from local Helmholtz, local Neumann, local injectivity, and regular radial boundary data alone. It is not an example in the global first-eigenspace class; global realization or exclusion remains an explicit obligation.

To verify (6.2) without numerical inference: for a flat edge, H_ttt=0 and H_tttt=−q″−q. With q=c h′, c=−x, the t³ coefficient is

    det(h′,−q″−q)/6 + det(q′,q)/2
      = −B(c′+c²)/3 = E(x)(1−x²)/3.

### 6.3 A higher-order attempt that actually fails

In a restricted flat analytic ansatz, start from F₀=(cos x,sin x), and prescribe leading trace changes δu=a x⁶, δv=b x⁵ with all lower changes zero. The leading Helmholtz extensions are a Re(x+it)⁶ and b Re(x+it)⁵. The first possible Jacobian term is

    t[(30a+20b)x⁴−(60a+20b)x²t²+6a t⁴].                  (6.3)

It cannot be nonnegative for all t>0 and x unless a=b=0. Nonnegativity on x=0 forces a≥0. If a=0, the polynomial changes sign unless b=0. If a>0, put z=b/a≥−3/2 from the t x⁴ coefficient. For ρ=x²/t² the bracket divided by at⁴ is

    (30+20z)ρ²−(60+20z)ρ+6.

At z=−3/2 it becomes 6−30ρ. For z>−3/2 it has positive leading coefficient, positive sum and product of roots, and discriminant

    400[(z+12/5)²+36/25]>0.

It is negative between its two positive roots. Thus this attempt at still higher flattening fails by an exact sign obstruction. It is only a restricted ansatz obstruction: arbitrary lower jets and curved or merely smooth boundaries have not been reduced to it. It does not prove a universal 1/4 bound.

## 7. What is unresolved after the strongest executed combination

The complete executed chain is source reciprocal/vector machinery → paid global eigenmap theorem → exact boundary jets → classical positive-curvature nondegeneracy → one-sided normal form → sharp fixed-domain inverse and eigensphere bounds. This chain closes, but does not leave an identified substantial operation beyond the strongest actual source/history/classical combination.

For the full smooth simply connected double-eigenspace class, the concrete remaining problems are:

* Can A vanish at a nonpositive-curvature boundary point for a *global* exact first eigenspace? The cubic/quartic local models satisfy all the displayed local data, but do not solve the outer boundary conditions, mean-zero requirement, first-mode spectral ordering or global nodal topology. They supply no compatible global examples.
* If A can vanish, is there a uniform finite order of transverse contact, even pointwise? In particular, a universal 1/4 inverse exponent would require a reduction of arbitrary degeneracies to controlled jets and exclusion of infinite-order contact for C∞ boundaries. Neither the restricted polynomial obstruction (6.3) nor the nodal unique-continuation lemma proves that reduction for the Jacobian.
* An effective quantitative constant in geometric parameters would require bounds for A, h′, the collar charts and the interior inverse margin. No such bounds follow from the present compactness patching. Spectral multiplicity under a general perturbation is not preserved; the exact D₃ example proves compatibility only for that specified symmetric family.

No candidate with those unresolved assertions is frozen, narrowed, renamed or submitted as proved. No previous closed target is reopened. PREFREEZE/no nominee is the final research disposition requested of the parent, with no self-assigned mathematical grade.
