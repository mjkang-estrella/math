# T366A166 — first independent correctness review

**Verdict: PASS for the entire unchanged frozen statement and author proof.** This verdict is conditional on precisely the stipulated truth of SOURCE366 and its operative upstream proofs, including the identified DF endpoint framework. No additional smoothness of the fidelity datum, nonvanishing coefficient, symmetry, uniform scale, or bound on component count is needed. I found no remaining mathematical obligation requiring a repair of these frozen bytes. This is correctness review only; it assigns no contribution grade, acceptance, or count.

Reviewed statement SHA256: `c518b1e730585463899f83a6c1aa1023717817671ecdcd540245024745a1cd33`.

Reviewed proof SHA256: `5a5877d58132597566ba6fed1cd376501810dc4294270c84f14b3d65325a8828`.

Authorized reviewer provenance: Codex / GPT-6 Astra / high / default service tier. No earlier independent findings, author response, sibling review, or live-peer activity were inputs. The parent alone may integrate or adopt this verdict. The reconstruction below expands the argument actually present in PROOF §§1–7; it neither substitutes another theorem nor changes the author proof.

## 1. Scope and applicable upstream operations — PROOF §1

The canonical SOURCE366 introduction defines the same admissible pair and compact-change comparison class as STATEMENT.md: bounded Lipschitz planar domain; real bounded measurable g; relatively closed finite-length K; global L2 u and W1,2 off K; reduced support; every compactly supported comparison in every relatively compact open V. SOURCE366 Proposition `prop:initial-reduction` supplies local boundedness, the SBV representative, rectifiability, and identification of the reduced crack with the jump support. Its restriction argument permits the locally Sobolev comparison class of DF: a finite-energy competitor extends through an unchanged collar, and its fidelity term supplies its local L2 norm. Thus the stronger-looking global integrability conventions in the frozen statement do not obstruct use of the primary local theory.

SOURCE366 `thm:main`, `prop:planar-facts` and the completion proof provide the endpoint chart and tangent at every loose end. On a sufficiently small punctured chart the remaining points are pure jumps. DF Proposition 2.5.2 and its Appendix A proof give C1,1 geometry there and the Neumann/curvature system with a bounded variational representative g_K, satisfying ||g_K||∞ ≤ ||g||∞. This is the representative produced by the variation argument; it is not a pointwise trace of an arbitrarily chosen L∞ function. This resolves the rough-data interface without adding regularity to g.

DF Lemma 5.0.4 supplies continuity at the tip and the square-root estimate. Subtracting u(p) from both u and g preserves the fidelity difference and the variational problem; changing sign means changing both together. On any fixed local normalization of spatial scale ρ, the energy divided by ρ becomes the DF energy for U(x)=ρ^(-1/2)(u(p+ρx)-u(p)), G(x)=ρ^(-1/2)(g(p+ρx)-u(p)), with λ=ρ². The bound M0 in DF (1.1.2) is any fixed finite bound. This normalization makes no uniform-in-minimizer assertion. Subsequent tail estimates are for this fixed pair, with T allowed to increase. In particular the argument does not require a universal scale at which rescaled g remains bounded by a prescribed universal constant.

The actual operative input is DF arXiv:2308.14660v2, complete Chapter 5, not a claimed extension of its homogeneous C2 conclusion. The following distinctions matter:

* The unnormalized estimate on printed p.150, immediately before (5.5.5), controls the nonlinear odd part in strip H2 and a=θ' in interval H1 with a positive exponential rate. Taking square roots of that estimate only changes the positive exponent.
* Formula (5.5.6) controls the projected even error. It should not by itself be read as fixing the first even amplitude. The full even error tends to the specified S with a positive rate by Corollary 5.5.2, specifically (5.5.10). The proof uses that additional input.
* Lemmas 5.0.3 and 5.1.3 supply a corrected harmonic conjugate on the whole disk, equal boundary values H1, the cylindrical equations, and errors at every exponent s<3/2. The quantitative Hölder estimate (5.1.21), as well as (5.1.20), supplies the boundary norm decay. A pointwise bound on H1 alone would not suffice.

Here is an explicit check of the further elliptic consequences used in §1. Set h=f-S and

P_a = ∂tt - 2a∂tφ + (1+a²)∂φφ,

Q_a = P_a - ∂t - (a'-a)∂φ + 1/4.

Then the exact equation is

Q_a h = (a'-a)S_φ - a²S_φφ,

with h=H1 on the two spatial sides. The principal matrix in coordinates (t,φ) is [[1,-a],[-a,1+a²]], of determinant one. Uniform boundedness of f_φ, a and H2 in the angle equation gives a'∈L∞; hence a is Lipschitz and the principal coefficients are uniformly Lipschitz and elliptic on the tail. The lower-order coefficient a'-a need only be bounded. Its L2 norm decays by the unnormalized odd estimate. Since h has decaying L2 norm from the odd and full even estimates, the fixed-strip boundary H2 estimate gives a positive decay rate for full h. Boundary H1∈H3/2 has a positive decay rate because its derivative has a Hölder exponent strictly greater than 1/2 with exponentially decreasing seminorm. Integrating a to the limiting tangent angle zero gives θ in H2 at a positive decay rate as well.

This formulation also makes clear that no decay of the time derivative of h needs to be assumed in order to get full H2 decay: it is obtained by the same elliptic estimate. It is an explicit verification of the elliptic alternative already stated in PROOF §1.

For finite p, choose α>1-1/p in the available C1,α boundary bound. The fractional Sobolev seminorm of H1' is finite in W^(1-1/p,p), so H1 belongs uniformly to W^(2-1/p,p) on each fixed interval. The bounded first derivatives and the bounded a' give a bounded Lp right side when Q_a is used, and local boundary W2,p estimates give uniform W2,p bounds for f. Interpolation of each derivative of order ≤2 between its decaying L2 norm and a uniform Lq norm, q>p, gives a positive decay rate ε_p for ||h||W2,p. For p>2 this embeds in C1,α on the two-dimensional strip, for some α>0. Thus §1(i)–(ii), including decay of e_tφ in any specified finite Lp, follow with no forcing differentiation.

The coarse nonlinear estimate is a stipulated upstream operation. Its moment constraint cannot simply be omitted when obtaining coarse decay. The later argument correctly uses coarse decay to eliminate the nondecaying Jordan solutions, rather than trying to impose an extra homogeneous moment condition on the forced system.

## 2. Parity, residual estimates, and the boundary-state signs — PROOF §§2 and 5

Reflection φ↦2π-φ leaves S even and reverses a φ derivative. With f=E+O and E=S+e, the odd equation is exactly

LO=(a'-a)S_φ+(a'-a)e_φ+2a e_tφ-a²O_φφ.

Since both boundary values of f equal H1, O vanishes at 0 and 2π; oddness also makes O(π)=0. At the endpoints E_φ(2π)=-E_φ(0) and O_φ(2π)=O_φ(0). Consequently

f_φ(2π)²-f_φ(0)²=(-E_φ+O_φ)²-(E_φ+O_φ)²=-4E_φ O_φ.

Using S_φ(0)=c=1/√(2π) gives exactly (2.2)–(2.3), with coefficient -4c, and not its opposite. In particular there is no additive even-only quadratic forcing in the odd equation. This matters because the even decay rate may be slow.

For clarity the estimate (2.4) can be checked term by term on nested fixed strips. The factors e_φ in sup norm and e_tφ in L2 decay at positive rates. The H2/H2 norm X of (O,θ) controls a'-a in L2, a in sup norm by the one-dimensional embedding, and the boundary normal derivative O_φ(0,·) in L2 by the trace theorem. Hence the first two products in R are ≤Ce^(-εt)X. The factor a² is already small with a positive decay rate, so the last product has the same bound. In N, the coefficient (1+a²)^(5/2)E_φ(0)-c is bounded by C(|e_φ(0)|+a²). The cubic a³ uses two coarse sup factors and one factor controlled by X. The remaining H2(t) is bounded by C_s e^(-st), for a fixed s<3/2. Enlarging the strip changes constants only. These bounds establish (2.4), with the boundary forcing measured in its independent one-dimensional L2 norm.

Set ζ=O-cθ cos(φ/2). Its boundary state is ζ(0,t)=-cθ(t); it is not a trace assigned to the forcing. The bulk equation gives Lζ=R because (∂φφ+1/4)cos(φ/2)=0. Also ζ_φ(0)=O_φ(0), and

(-cθ)''-(-cθ)' = -c(a'-a) = 4c²ζ_φ(0)-cN = (2/π)ζ_φ(0)-cN.

Therefore the second coordinate of A must be -(2/π)ζ_φ(0), and the state equation really is

Z''-Z'+AZ=(R,-cN).

No R(0,t) occurs. R is only an L2 bulk field at this stage, and the author's formulation respects that limitation.

## 3. Completion, positivity, and graph domain — PROOF §3

For I=(0,π), use H=L2(I)⊕R with the positive norm specified in the proof and indefinite pairing [·,·]. For trace states in D(A), integration by parts gives

[AZ,H] = -∫_I z'h' + (1/4)∫_I zh.

The lower-end bulk boundary term is -z'(0)h(0), canceled by the scalar-coordinate term +z'(0)h_b. The term at π vanishes. Thus bracket symmetry has the stated sign. The graph norm is equivalent to ||z||H2: z'' is controlled by the bulk part of AZ and z, and the interval interpolation inequality controls z'. Conversely H2 controls both traces and AZ. This proves closedness as stated.

Direct differentiation of z0=(φ-π)sin(φ/2) gives z0''+z0/4=cos(φ/2) and z0'(0)=-π/2. Thus Ae0=e1, including its scalar component, while Ae1=0. Further,

[e1,e1]=π/2-π/2=0,
[e1,e0]=(1/2)∫_0^π(φ-π)sinφ dφ=-π/2.

The determinant of the two-dimensional Gram matrix is therefore -π²/4, regardless of the value of [e0,e0]. Its projection is bounded, and the generalized zero mode cannot be treated as a positive self-adjoint eigenmode.

For the high mode q_k, the bulk identity is immediate. The scalar identity is

-(2/π)ν_k cos(πν_k) = (ν_k²-1/4)sin(πν_k) = -λ_k(q_k)_b,

which is exactly the frozen root equation. From symmetry,

λ_k[q_k,q_k]=∫|q_k'|²-(1/4)∫|q_k|².

Every H1 function on (0,π) vanishing at π satisfies the Neumann–Dirichlet Poincaré inequality with first eigenvalue 1/4. Equality consists of multiples of cos(φ/2). Therefore the displayed quantity is strictly positive for q_k with ν_k>1/2. This verifies the normalization without assuming positivity of the whole state space.

The root equation gives |sin(πν_k)|≤2ν_k/[π(ν_k²-1/4)]=O(k^-1). The exact bulk integral is π/2-sin(2πν_k)/(4ν_k), hence bounded above and below for large k. Subtracting (π/2)sin²(πν_k) leaves the bracket norm with the same property; finitely many earlier positive modes cause no problem. Thus the normalized boundary sequence ((h_k)_b) lies in ℓ2. Bracket orthogonality of distinct eigenvalues and orthogonality to e0,e1 follow from symmetry and Ae0=e1. For finite high sums this yields

Σ|d_k|² ≤ ||Σd_k h_k||H²
             = Σ|d_k|² + π|Σd_k(h_k)_b|²
             ≤ (1+πΣ|(h_k)_b|²)Σ|d_k|².

This proves the asserted Riesz inequalities and closed high subspace. DF Proposition 5.3.8 supplies H1 completeness on the reflected odd interval. Restriction to I identifies that space with H1(I) functions vanishing at π. H1 convergence implies convergence of their boundary states in H. These trace states are dense in H: compactly supported smooth bulk approximations may be augmented by a width-δ boundary layer of height equal to the desired independent scalar, with L2 norm O(√δ). Thus the closed direct sum of the Jordan sector and the high subspace is all of H. There is no missing scalar direction.

Finally, if Σλ_k²|d_k|²<∞, the partial sums converge in the graph norm and hence to a member of D(A). Conversely, for Z∈D(A), bracket symmetry identifies the high coefficients of AZ as -λ_k d_k. The bounded coefficient map on H then gives this summability condition. The finite Jordan coordinates impose no additional summability condition. This verifies both directions of the operator-domain assertion, not merely convergence of a formal mode series.

## 4. The forced half-cylinder estimate — PROOF §4

In the complete state coordinates the two low equations are triangular: y0''-y0'=F0 and y1''-y1'=F1-y0. For

y(t)=∫_t^∞(1-e^(t-s))h(s)ds,

one has y'=-∫_t^∞e^(t-s)h(s)ds and y''=h+y' in distributions. Unit-interval Cauchy–Schwarz bounds control y,y' pointwise and y'' locally in L2 at every positive exponent below the forcing exponent. The homogeneous solutions 1 and e^t, and the corresponding coupled Jordan solutions, cannot occur in an exponentially decaying state. Applying this inverse twice preserves every slightly smaller positive exponent. No vanishing of the forced Jordan projection is being assumed.

For k≥2, λ_k=μ_k(μ_k+1)>0. The two formulas for G_k in (4.5) are continuous at zero and have derivative jump

μ_k/(2μ_k+1) - (-(μ_k+1)/(2μ_k+1)) = 1.

They therefore invert ∂tt-∂t-λ_k. With a cutoff χ that is constant near each end of its transition, the additional forcing is 2χ'Z'+(χ''-χ')Z, in L2 and compactly supported. Coarse decay makes the cut-off state globally L2, so it is the scalar L2 convolution solution in every high coordinate.

There is no circular assumption of a faster weighted norm in the multiplier step. To make the justification explicit, first work with finitely many high coordinates and smooth approximations of the cut-off forcing. For any 0<d<μ_m, where m=2 (or m=3 after extraction), the weighted convolution kernel satisfies

|e^(dτ)G_k(τ)| ≤ C_m e^(-(μ_m-d)τ)       (τ≥0),
|e^(dτ)G_k(τ)| ≤ C_m e^((μ_m+1+d)τ)     (τ<0),

uniformly for k≥m. The scalar majorant is integrable, so the diagonal convolution operator is bounded on L2(R;ℓ2). Consequently the weighted state is already in L2 whenever the weighted forcing is. Its two derivatives and its graph norm can now be estimated by the Fourier multiplier

p_k(ξ)=(iξ-d)²-(iξ-d)-λ_k,

|p_k(ξ)|≥ξ²+λ_k-d(d+1)
        ≥[1-d(d+1)/λ_m](ξ²+λ_k).

The square-bracketed constant is positive. The multipliers for ∂tt, ∂t and A are thus bounded uniformly in k. Plancherel, the Riesz inequalities, and density pass the estimates to all modes. This explains precisely why summing absolute values of spatially differentiated kernels is neither required nor appropriate. The author's kernel-plus-multiplier argument has the necessary uniform infinite-mode estimate.

Local graph norms control ζ_φφ and ζ_tt in L2. The ordinary mixed derivative follows from the product-Sobolev estimate, after an interval extension in φ and a time cutoff; equivalently the Fourier inequality ξ²η²≤(ξ⁴+η⁴)/2 gives the estimate on the extended rectangle. The independent scalar coordinate controls θ_tt directly, without taking the boundary trace of ζ_tt. Thus the graph norm really has the strip H2 strength used later.

For the first coefficient write H for its cut-off forcing. The convolution has the exact form

y2(t)=-(2μ+1)^(-1){e^(-μt)∫_(-∞)^t e^(μs)H(s)ds
                         +e^((μ+1)t)∫_t^∞e^(-(μ+1)s)H(s)ds}.

If β>μ, the first integral converges at infinity. Define D=-(2μ+1)^(-1)∫_R e^(μs)H(s)ds. Subtracting D e^(-μt) leaves two future integrals, each controlled at any rate γ<β, together with its first derivative; the differential equation controls its second derivative in local L2. The higher modes admit the same weighted estimate for d<μ3, and the low sector was already controlled. This proves (4.3) in the stated norm. The cutoff can change the formula expressing D through H, but it cannot change the coefficient of the original solution on the tail.

## 5. Finite nonlinear bootstrap and the first coefficient — PROOF §5

The state norm and ||O||H2+||θ||H2 are equivalent on padded strips, with the mixed-derivative estimate just checked. Choose a fixed s with μ2<s<3/2, possible because the actual first root is in (3/2,2). If X has exponent d, (2.4) gives forcing exponent min(d+ε,s). The forced estimate gives every exponent strictly below min(d+ε,s,μ2). Choose increments smaller than ε/2 until d lies in (μ2-ε,μ2); only finitely many steps are needed. Each step uses an estimate already established, and only finitely many fixed-width paddings are needed. Constants may depend on the pair and these choices.

At that stage min(d+ε,s)>μ2, so the extraction theorem applies. Pick γ strictly between μ2 and min(β,μ3). The boundary coordinate gives B=-D(h2)_b/c and θ=B e^(-μ2t)+θ*, with θ* decaying in H2 at rate γ. Since interval H2 embeds in C1, θ* and a*=θ*' have uniform sup bounds at that rate. Recovering O yields exactly the profile O0 written in §5, including the minus sign before (h2)_b cos(φ/2). Its bulk and boundary equations follow from Ah2=-λ2h2 and the scalar trace condition, so subtracting it in §6 is legitimate.

At no point is D, B or an unknown norm divided by. If D=0, all assertions instead give faster decay. The entire argument therefore includes the zero-leading-coefficient case without reclassification or an alternative theorem.

## 6. Rough-data trace upgrade — PROOF §6

The initial remainder is V∈H2 on strips and b=a-a0∈H1 on intervals, both with rate γ>μ. The normal derivative trace of V is H1/2 in the one-dimensional time variable. On bounded intervals this embeds in every finite Lp, but not automatically in L∞. The author correctly uses only finite p at this stage.

In (2.3), the sup-small e_φ and a² multiply the full normal trace O_φ, whose finite Lp norm has rate μ. Also a³ has rate 3μ and the fidelity error has the fixed rate s>μ. Thus N has an Lp rate β0>μ. Equation (6.1) gives b' in Lp at rate min(γ,β0)>μ; the full a' has rate μ in Lp.

Subtracting the leading bulk equation gives exactly (6.2). In particular the coefficient a² multiplies V_φφ on the left, and there is no missing mixed derivative of V: the mixed derivative in the odd equation acts on the even part, already retained as 2a e_tφ. For a fixed p>2 the four right-hand terms have respective exponents bounded below by

min(γ,β0),   μ+ε,   μ+ε_p,   3μ.

All exceed μ. The lower-order term and ||V||Lp are handled by the strip estimate, with ||V||Lp already controlled by H2 in dimension two. The principal coefficients diag(1,1+a²) are uniformly elliptic and Lipschitz. V has homogeneous Dirichlet traces at 0 and π. Local boundary W2,p regularity on a smaller strip therefore yields a rate γ_p>μ. The temporal ends are excluded by padding; no corner regularity is asserted. Odd reflection across the spatial sides is also valid for this diagonal operator with coefficients independent of φ and V=0 there.

For p>2, W2,p in two dimensions embeds in C1,α for some α>0, so V_φ(0,t) now has a genuine uniform bound with rate greater than μ. Reusing (2.3) gives N in L∞ at a rate greater than μ. Equation (6.1) then gives b' in essential supremum at such a rate. This order of operations avoids both false H1/2→L∞ embedding and differentiation of H2(t). It gives exactly the three estimates in (6.4), with an essentially bounded, possibly discontinuous a'.

## 7. Graph conversion and all frozen limits — PROOF §7

For C=cosθ and Sθ=sinθ, differentiating with dt/dr=-1/r gives

x_r=C+aSθ,                    y_r=Sθ-aC,
x_rr=-[(a'-a)Sθ+a²C]/r,       y_rr=[(a'-a)C-a²Sθ]/r.

Their determinant is

x_r y_rr-y_r x_rr=(a'-a-a³)/r.

Since x_r→1, it is positive and bounded away from zero on a small interval. The one-dimensional Sobolev chain rule for the locally C1,1 curve therefore yields (7.1) almost everywhere. This verifies the cubic sign and denominator without differentiating an asymptotic remainder.

From (6.4), θ=B r^μ+O(r^(μ+η)), a=-μB r^μ+O(r^(μ+η)), and a'=μ²B r^μ+O_ess(r^(μ+η)). Hence x=r(1+O(r^(2μ))), and its inverse has the corresponding estimate. Choose η' positive and no larger than η and 2μ (decreasing it if necessary). The exact graph formulas then give

ψ(x)=B x^(1+μ)+O(x^(1+μ+η')),
ψ'(x)=(1+μ)B x^μ+O(x^(μ+η')),
ψ''(x)=μ(1+μ)B x^(μ-1)+O_ess(x^(μ-1+η')).

Changing r to x preserves the essential statement: the coordinate change is locally bi-Lipschitz with derivative bounded above and below, so null sets remain null; countably many annuli cover the punctured chart. Fixed-width overlapping time strips likewise cover the whole tail. Thus the estimates hold uniformly for all sufficiently small x, with the third understood in essential supremum, rather than merely along a sequence of radii.

The three normalized remainders are bounded by C r^η' on 0<x<r and therefore give exactly the three frozen limits. Since μ>1, ψ'' is essentially bounded and tends essentially to zero. Local C1,1 away from the endpoint covers the remaining compact portion of a shorter chart, giving W2,∞((0,δ)). The tangent extends continuously, giving C1([0,δ]). Finally ψ'(x)/x→0, so the one-sided derivative of ψ' at zero exists and equals zero. The curvature ψ''/(1+ψ'²)^(3/2) has the same vanishing essential limit. This uses no continuity of ψ'' on the punctured chart.

All arguments apply to an arbitrary loose end of an arbitrary pair in the stated class. Their constants and chart sizes are local. There is no uniform selection over all minimizers and no finite-component assumption. Zero B satisfies the same estimates. The conclusion is therefore the entire frozen statement, including the endpoint second derivative, not just a weaker C1 estimate or an L2 curvature expansion.

## 8. Dependency and reading limits relevant to this verdict

I read all nine actual pinned SOURCE366 TeX/Bib objects in full and authenticated their bytes against the complete pinned tree by size and Git blob, independently computing SHA256. I read complete DF Chapter 5, the normalization and variational interfaces, full Appendix A, and the selected crack-tip amplitude and weak-L4 proof pages. The spectral and forced-boundary formulas and the unnormalized coarse estimate were additionally checked on rendered PDF pages. This is the operative dependency, whose proof truth remains stipulated.

I also read Deangelis v2 and the Labourie–Lemenant article in full, AM v5's full §8 plus the initial 19,000 extracted bytes, and the first 15,000 extracted bytes of DFG v4. AM's earlier lemmas invoked by §8 were not all read, and DFG's complete proof was not read. Neither is substituted for the full later DF proof. These comparison sources supply context and already available operations; this report draws no contribution or novelty verdict from their coverage. The separately linked erratum was attempted by this reviewer and returned HTTP 403; it remains unread. No claim is made that the arXiv DF bytes equal the inaccessible author or published edition.

The two exactly authorized I122 sections were read from the original at the supplied byte extents. They include administrative and other-family material; that incidental admission is disclosed, not used as a premise. The old polynomial graph-complexity target is unchanged and irrelevant to the proof of this endpoint asymptotic. The historical r165 work was not reread, as the current review instructions expressly remove that unrelated obligation.

Exact dependencies, objects, extents, transport recoveries, the lack of a broad history scan, and isolation limits are recorded in `private/DEPENDENCIES.md`, `private/READING-AND-ISOLATION.md`, `private/EXTENTS.json`, and `private/selected-inputs.json`. Metadata authentication and packet controls are artifact observations only. There is no unresolved mathematical repair request at the frozen scope, and no self-assigned contribution, acceptance, or campaign-count change.
