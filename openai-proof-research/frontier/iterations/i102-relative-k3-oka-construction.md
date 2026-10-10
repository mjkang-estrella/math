# I102 — Original relative-K3 audit and entire-family construction

**Disposition: original technical proofs accepted at their precise scope; R98 remains unproved and unrefuted. No substantial finding nominated. Eight accepted, two remain.**

The strongest new construction here is **G102**, a single compatible holomorphic germ along the *whole* central entire spray, with exact moving core and first jet. Unlike separate applications of A98, all its finite windows are restrictions of one map and use one recentering. Its domain is an open neighborhood of the noncompact central slice, not necessarily a product with a positive-radius target-parameter ball. **S102** retains holomorphic target parameters in the complete annular sewing operation, provided a uniformly buffered holomorphic exact chain is supplied on one parameter domain. The finite raw atlas supplies a common deformation domain for its finitely many charts, but I have not constructed that infinite holomorphic chain on that domain. **E102** gives the precise exhaustion and final recentering argument that would suffice without preserving a central entire map away from its core. Its required relative extension step is not established.

All theorems and lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are assumed true. No upstream truth audit, contradiction between sources, or ex-falso synthesis is used. The external compact nonellipticity result is treated as its authors' primary theorem. No children, active I100/I101 outputs, shared edits, staging, commits, or publication are used.

The unchanged target **R98** is: every surjective proper holomorphic submersion `π:X→B` of complex manifolds with arbitrary complex K3 fibers is an Oka map, without polarization, projectivity, isotriviality, compact-base or global-volume-form hypotheses. The needed analytic construction is a holomorphic spray `S:V×C^N→X`, for each lift f near a compact convex `K⊂C^m`, with `S(z,0)=f(z)`, `πS(z,w)=πf(z)`, and surjective vertical derivative at zero on K. V is one neighborhood of K for all w; N may depend on the input. It suffices to do this over a fixed open cover of B as in the primary definition of convex ellipticity. The prescribed base map `g(z)=πf(z)` may be nonconstant.

## 1. Original verdicts, with defects stated before elaboration

* **A98: ORIGINAL PASS WITHOUT REPAIRS.** No defect was found in its finite-radius conclusion, exact core or first jet, fixed-before-radius source neighborhood, or displayed sufficient base-radius bound. In particular, it does not assert a positive infimum of those radii.
* **W98: ORIGINAL PASS WITHOUT REPAIRS as the stated subelliptic/Oka-map theorem.** No repair of the Hodge twist, vector fields, completeness, or domination is required. The Oka-map assertion is interpreted in the reduced-space category of the primary criterion. There is a wording ambiguity in the expanded R98 paragraph: an arbitrary *nonreduced* “closed complex subspace” with prescribed infinitesimal data is not specified by a continuous map on its underlying set. That stronger reading is not an accepted conclusion. The precise reduced POPAI formulation and the distinct jet statement are given below. This scope clarification does not change W98's geometric hypotheses or proof.
* **Moving-pole nonextension: ORIGINAL PASS WITHOUT REPAIRS.** It obstructs extending that chosen compatible family, not choosing a different family.
* **Persistent-curve-class obstruction: ORIGINAL PASS WITHOUT REPAIRS.** It excludes the specified proper-curve data over a full Kuranishi neighborhood; it does not exclude Stein-source entire maps, finite raw charts, or relative Oka maps.

These verdicts concern the original report frozen verbatim in the evidence, before G102/S102/E102. None is a substantiality verdict. Both original positive constructions reduce completely to the stipulated lower operations and standard Oka machinery. The additions below must not be silently inserted into the original proof to improve its verdict.

### A98: chart, splitting, and domain audit

Choose bounded convex neighborhoods `K ⊂ V ⊂⊂ V+ ⊂⊂ U0`, and a sufficiently small polydisc in the target base. The bundle `f* T_(X/B)` is holomorphically trivial on a contractible Stein product. For the central dominating spray `T(z,ξ)`, the surjection `A: O^N → f0*TX0` admits a holomorphic right inverse after identifying the latter with `O²`: apply Cartan B to the exact sequence obtained by applying `Hom(O²,–)`. The kernel is a vector bundle since A has constant full rank. The resulting `S0(z,w)=T(z,R0(z)w)` is entire in w. Shrinking U0 and choosing V+ and V at this stage, rather than after fixing R, pays the stated quantifier order.

The relative chart is legitimate without a chart on the compact target. Work in the pullback manifold

`Y = {(z,b,x): π(x)=b}`

over the Stein source `(z,b)`. The graph of f is a closed Stein submanifold. In a Stein neighborhood of it, the tangent sheaf vertical over `(z,b)` is locally free. The exact restriction sequence for this sheaf and the graph ideal, followed by Cartan B, extends the given frame as *vertical* fields. Their short flows produce E with derivative L. The inverse of `(z,b,v) ↦ (z,b,E(z,b,v))` is a holomorphic inverse on an open neighborhood of the graph, after taking one positive fiber radius over the retained compact source margins. This is an inverse of a graph chart, not an inverse to an arbitrary map into X.

For fixed finite R, horizontal lifts are constructed on a Stein neighborhood of the graph of S0 over a Stein product containing `closure(V+) × closed Δ_(R+2η)²`. Their projection to B is the coordinate field, and their projection to the source is zero. Their composition is therefore jointly holomorphic and lies exactly over b. All time and inverse-chart radii are chosen over larger compact margins before estimates on closure(V).

For the original H, let `c0=2M`, `c1=2N(2M+1)` and take precisely the original bound

`0<δ<min(β/2, r/(4M), 1/[4N(2M+1)], η/[2(c0+c1R)])`.

The contraction ball has radius `2Mδ<r/2`; throughout it the derivative error is at most `N(2M+1)δ<1/4`. Its image radius is at most `3Mδ/2<2Mδ`. Iteration, uniformly on these compact margins, gives the holomorphic root a. At that root the chart derivative is L, so `D_w H=L^(-1)A` and `A^(-1)L=(D_w H)^(-1)`; there is no tangent-space mismatch. The inverse bound is at most `1/(1-1/4)=4/3`, so the original more generous factor 2 in c1 is valid. Finally

`|a+Cw| ≤ R+(c0+c1R)δ < R+η/2 < R+2η`.

The inequalities apply on the whole open retained product, not merely K. Uniqueness at b=0 gives a=0 and C=I there. Thus both exact moving first-jet identities and the identity with S0 on the central entire finite window hold. Constants for the finite deformation may depend on R; Cauchy estimates do not remove that dependence. Neither properness nor a relative Kähler form is used in this lemma.

### W98: bundle, singular-level, and flow audit

Here the original hypotheses are that π is a surjective proper K3 submersion and there are finitely many holomorphic maps `f_i:X→C_i` to smooth complex curves such that `(df_i)_i` is injective on every vertical tangent space. The conclusion is a finite dominating family of global fiber sprays for π and hence an Oka map. The maps and curves are actual analytic data; a fiberwise selection or cohomological marking does not satisfy this hypothesis.

The relative canonical bundle is locally free and flat over B. Proper cohomology and base change applies because `h⁰(X_b,K_b)=1` is constant. It gives a line bundle `L=π_*K_(X/B)` with the stated fibers. Evaluation is an isomorphism at every x: its restriction to each K3 fiber evaluates a nowhere-zero generator. No global generator on B is used.

The canonical contraction is

`T_(X/B) → Hom(π*L, Ω¹_(X/B)) = Ω¹_(X/B)⊗π*L*`.

Writing λ as `a du⊗ω*`, and replacing ω by gω, replaces a by ga. Thus `ι_(Aλ)(gω)=ga d(u∘f_i)` is the same equation. The original dual twist is correct. The form in this equation is the *relative* differential; no horizontal component of df_i is erroneously contracted.

In a relative two-dimensional chart let α be that covector and `ι_vω=α`. Then α(v)=ω(v,v)=0. This proves `df_i(v)=0` even on singular levels, including points where the relative differential is zero. The vector field `(A_xλ,0)` is consequently tangent to `E_i=X×_(B×C_i)M_i` everywhere. The ambient space E_i is a vector bundle over the smooth X; singularities of a level of h_i do not introduce singularities into its manifold of definition.

Here is an explicit uniform completeness check for the original short flow argument. The map `h_i=(π,f_i)` is proper: for a compact Q in `B×C_i`, its inverse image is closed in the compact `π^(-1)(pr_B Q)`. Its base change `E_i→M_i` is proper. Choose a relatively compact neighborhood of λ in M_i. The inverse image of its closure is compact and invariant under the vector field. A finite coordinate cover gives a common local complex-time radius τ. For any T choose an integer n with `T/n<τ`; the n-fold composition of the time-t/n map exists for |t|<T, stays over the same λ, and is jointly holomorphic in t and initial point. Uniqueness and the local group law make these formulas agree on common domains. They give an entire complex-time flow, without analytic-continuation monodromy. Exhausting M_i gives a holomorphic time-one map on all E_i.

At λ=0 its first variation is exactly A: in the linearized equation the derivative of `x↦A_xλ` vanishes at λ=0, and integration of the remaining constant forcing for time one gives A. The injective joint vertical differential has surjective dual; contraction with L* therefore makes the images of these derivatives span the vertical tangent at every x. This is a finite dominating family of fiber sprays, hence subellipticity. Smooth local triviality from proper Ehresmann gives the required fibration, without any compactness assumption on B.

For the analytic implication use the precise primary interface: Kusakabe, *Elliptic characterization and unification of Oka maps*, [v1](https://arxiv.org/abs/2003.03757v1), Definition 1.1, Theorem 1.3, and Corollary 5.7. It supplies **all compact Hausdorff pairs** `P0⊂P`; since P0 is compact in the Hausdorff P it is closed. No cofibration, neighborhood retract, metrizability, or Euclidean embedding of the pair is required. Maps are continuous jointly in the compact parameter and source, holomorphic in the source variable for each parameter. Source spaces are reduced Stein spaces, including singular ones. The initial holomorphy near K is on a common open neighborhood as in the definition, and the homotopy retains holomorphy near K and uniform approximation on `P×K`. The prescribed holomorphic base family is fixed throughout. This is stronger than a statement about individual sections or finite polyhedra of parameters.

Ordinary POPAI interpolates the restriction to a **closed reduced complex subvariety** A. Merely giving a continuous map on |A| specifies no derivative on a nilpotent thickening. For example, on the doubled origin in C the underlying point value does not determine the coefficient of z. The source's Remark 5.4 and Corollary 5.5 also supply POPAJI, with its actual holomorphic jet data and hypotheses, but those data must be given to ask for jet interpolation. This is the exact convention in which the original W98 Oka-map theorem passes. A literal claim of automatically preserving unspecified nonreduced data would be ill-posed, not a strengthened theorem proved here.

### Audited method obstructions

For the moving pole, choose b0 as in the original argument. The R=1 window already gives a nonempty disc on which the proposed extension has the stated formula. Normalize the invariant form θ by pulling it back to du on C. The coefficient of its pullback on the b0 slice is entire if an extension exists. On the connected punctured plane it agrees, by the identity theorem, with `(1-b0 w)^(-2)`. The latter has a genuine double pole at `1/b0`, contradiction. Quotienting by the lattice does not remove this differential obstruction. The alternative `[w]`, independent of b, has the same core, first derivative, and central entire map and is defined on every product. Thus even fixing those data is not obstructed by this example; only preserving the chosen germ in b is obstructed.

For persistent curves, simultaneous differentiable trivializations identify the fiber maps along small paths and hence their integral pushforward fundamental classes. Their pairing with the holomorphic two-form and its conjugate vanishes; Hodge decomposition gives type (1,1). Pairing with a Kähler class is the strictly positive area of a nonconstant holomorphic map, so the class is nonzero. At the chosen period, after fixing a nonzero period vector, the tangent of the period domain identifies with `H^(1,1)`. Its intersection form is nondegenerate, so pairing with the nonzero α is a nonzero linear functional. The equation `(α,ω_b)=0` defines a genuine local hypersurface. This remains valid for isotropic α: nondegeneracy, rather than nonzero self-intersection, is what is needed.

For a W98 map use a regular level in the compact connected target-curve component and its nonzero effective divisor class. A nonconstant holomorphic map from a compact connected surface to a curve has open and compact image, hence surjects onto that compact component. The pullback of its integral orientation class is locally constant in the K3 local system and has positive Kähler pairing. No simultaneous smoothness of all level fibers is needed. This establishes the original obstruction exactly on its stated mechanism.

## 2. Route one: retaining target parameters through annular sewing

The complete pinned `sewing.tex`, `degeneration.tex`, `rational.tex`, `local.tex`, `gluing.tex`, `globalization.tex`, `projective.tex`, `dynamics.tex`, and `dense.tex` were read through their endings. Their truth, including all uniform estimates, is stipulated. The following parameter argument concerns an extra variable not quantified by their fixed-target conclusions.

### S102 — relative sewing for an already holomorphic buffered chain

Let `π:X→B` be a holomorphic family of symplectic surfaces on a polydisc B, with a nowhere-zero *relative* holomorphic two-form Ω. For a K3 family this is available after trivializing the Hodge line locally. Suppose all the input charts `φ_j(w,p,b)`, j∈Z, of `sew:chain` are jointly holomorphic on their displayed block domains times **this same B**, lie over b, and pull back Ω *vertically* to `dw∧dp`. Suppose their transition branches and shears are jointly holomorphic on B with all original h,r,A, error and domain margins uniform in b and j. Suppose the vertical period defects are zero. Then the conclusion is a jointly holomorphic map

`Φ:C×Δ_b0×B→X`, with `πΦ(w,p,b)=b`,

periodic in w, vertically symplectic, with the original uniform approximation statements on smaller blocks. The retained radius b0 and B are independent of chain length and of the long coordinate. B need not shrink during the Newton iteration.

**Proof.** The primitive removing the transverse zero mode is integration in w with its mean subtracted. For joint holomorphic inputs it is holomorphic in (p,b). The Fourier coefficients and their exponential factors are holomorphic in (p,b); use a fixed interior coefficient circle in each seam. The source's double geometric-series majorant is uniform in b. Thus both infinite Fourier sums converge normally on the jointly open domains and are jointly holomorphic. Taking derivatives in w,p uses only the original margins. Derivatives in b, if desired, use one fixed relatively compact subpolydisc of B *afterward*; no b differentiation is required to execute the construction.

The Hamiltonian vector fields have zero b component. Their local flows retain b and are jointly holomorphic in it. Choose the same losses `δ_n=d0 2^(-n)` for every b. With Q the fixed Newton exponent and `D=C d0^(-Q)`, the source recurrence is

`e_(n+1)≤D 2^(Qn)e_n²`, hence `e_n≤D^(-1)2^(-Q(n+1))θ^(2^n)` if `D2^Qe0≤θ<1`.

All `Σδ_n^(-k)e_n` converge. The compositions stay in their reserved original domains and converge with first derivatives on smaller domains, uniformly in b and j. The limit is jointly holomorphic and vertically symplectic. The common transverse radius is positive after the fixed sum of losses. Finally, the corrected shears give consecutive long-coordinate heights separated by at least `1-h/3`, uniformly in b,p. Their domains form a jointly open cover of `C×Δ_b0×B`. On each compact subset only finitely many blocks are needed: cumulative imaginary displacement has a uniform positive lower bound per step. The limiting identities glue these holomorphic maps. This proves the domain and all assertions, without invoking compactness as a normal-family theorem. ∎

The relative period-adjustment operation is also exact. For a holomorphic transition F_b, integrate `P dW-p dw` in the w,p variables around a fixed period circle. Its value D(b) is holomorphic, independent of p and of the representative circle. Translating the new chart and its model by the same D(b) changes the period to `D(b)-D(b)∫dW=0`. Uniform buffers pay this translation on the fixed B whenever its size stays below the original threshold. No derivative or primitive of a period function on the target deformation base is being assumed.

S102 is a technical extension of the complete lower operation: its estimates do not differentiate the added parameter. It is not an arbitrary-family theorem, because its infinite input data have additional quantifiers.

### What the actual finite raw atlas supplies

In `degeneration.tex`, first choose all compact regular families, partners, end-position patches, disc boundaries and buffers. Then choose d, then a nonzero α, and only then deform the finite raw atlas in the full Kuranishi family of that smooth quartic. Since the source domains of these finitely many charts are relatively compact Stein annulus products, there is one small B on which *all raw charts* are holomorphic, with their larger margins. Their finitely many selected inverse branches, symplectic normalizations and seam estimates persist uniformly. This is appreciably stronger than deforming an infinite list of already corrected maps; the latter is not needed and is not what the pinned proof does.

For any **fixed finite itinerary** of centered charts about b=0, recenterings are holomorphic in b: integrate each defect, use the local inverse branch to read the outgoing position, and choose the next chart with its original buffer. By induction each finite list works on some neighborhood. A finite intersection gives its one neighborhood. Its Newton constants do not deteriorate with its length once the data are on that neighborhood.

For the infinite itinerary, the pinned construction chooses a raw chart whose smaller patch contains the **current** outgoing nominal point of the compact elliptic curve E, then uses its larger patch. This proves indefinitely repeatable choices on each individual surface with uniform numerical margins. It is not yet a holomorphic selection of those choices over B. A finite cover of E is not a holomorphic section-selection operator for all maps B→E. It does not imply that the chart chosen at b=0 remains valid for every b in one neighborhood at every step.

Here is a precise diagnostic of this missing inference, not a counterexample to relative sewing. Take `E=C/Λ` and centers `c_j(b)=[jb]`. They are holomorphic for all b, and each point of E has a chart from a fixed finite buffered cover. Nevertheless, for every δ>0, for sufficiently large j the image `c_j(Δ_δ)` is all E (a large disc meets translates of every point in a fixed compact fundamental parallelogram). It is not contained in any one sufficiently small raw chart. At b=0 all these centers equal the same point. In local lifted coordinates the recurrence is `u_(j+1)-u_j=b`; no bounded solution in j exists for b≠0. Equivalently, the difference operator on bounded sequences has no right inverse on constant forcing. Thus small uniform one-step errors alone do not give a bounded perturbation of one preselected infinite itinerary.

This model allows global holomorphic center maps and therefore does **not** prove that rechoosing charts or gluing choices cannot work. It isolates the additional input needed: a holomorphic construction of the entire exact chain on one B, with all recentered charts and transition branches remaining in their uniform buffers, or a replacement that glues changing chart choices without decreasing B to a set with no interior. No estimate with that conclusion has been obtained here. Claiming an Oka-map theorem even on the unrestricted special open region solely from “finite atlas + uniform sewing” would skip this step.

### From relative strips to relative approximation: further bookkeeping

Once two transverse relative strips with common B and compact inverse-chart margins are supplied, the source's alignment construction is holomorphic in b by the inverse and implicit function theorems. The Cauchy–Green splitting in `loc:splitting` acts only in the planar variable and is bounded independently of the passive polydisc. Its contraction therefore preserves the target parameter. One obtains the corresponding finite planar operation for maps `h(s,u)` with `πh(s,u)=g(u)`, by composing the relative strips with `b=g(u)` and correcting only their two vertical coordinates. For a compact input lying in one witness chart the output retains that same g; approximation on a slightly larger passive product gives any needed fixed-order passive derivatives by Cauchy. The two strip-coordinate polynomials are approximated; the prescribed base map g is not.

The planar spokes, sectors and disc-propagation operations are finite, so their compact target margins and losses can be chosen in advance for that input, provided such relative witnesses are available. The open-overlap and real-interface splitting operators are linear on their fixed source geometry and preserve added holomorphic parameters. The nonlinear corrections are vertical chart reparametrizations. Thus these *gluing* operations introduce no error in π.

There is still a distinction between a genuine passive target parameter and an arbitrary source-dependent base map. The pinned polydisc proof precomposes the source by `h_d=H_d^(-N)L^N`; if applied to all source coordinates of a lift f, its base becomes `g∘h_d`, rather than g. Approximate equality of these maps is insufficient. For the spray problem one may instead act only on the w coordinates, keeping z and `g(z)` passive. This prevents that particular error, but it no longer concentrates the image as z varies: `f(z,w)` over a whole retained z-domain need not lie in a single witness neighborhood for each planar boundary point. A finite cover of the z-domain can handle one finite input locally; its new-side maps must then be holomorphically glued on the enlarged w-domain, with controlled z losses. The fixed-target proof does not automatically provide that selection and matching estimate. Likewise its real-face induction removes constraints in variables it later makes entire; blindly making the prescribed-base coordinates entire is not a proof of relative CAP on `Ω×C^N`.

These are transfer obligations, not objections to any stipulated fixed-target lower operation. If both the chain selection and the corresponding relative finite extension on prescribed source products were supplied by uniform lower operations, the conclusion restricted to the existing special open region would have a concrete technical reduction. It should not automatically be nominated as a substantial finding.

### Transport to arbitrary periods must be holomorphic

A valid conditional local transfer is available. Suppose an Oka-map assertion has actually been established for the local universal family on a full complex-open period region O. If a **single fixed** lattice isometry γ sends the central period P into O, first choose the underlying central-surface isomorphism provided by Torelli (including its chamber adjustment). K3 local deformations are universal as germs, since `H⁰(T_X)=0`; the isomorphism identifies their deformation functors. It therefore gives a holomorphic isomorphism of sufficiently small universal families after a holomorphic base change. Pull back the established Oka map to the given local family. This is a family isomorphism argument, not an interpretation of a marking as a trivialization. A locally fixed γ suffices because O is open. One does not choose γ separately at every nearby parameter.

Consequently an established full-open-region family theorem would transport to the saturation `⋃γ γ^(-1)O`. The stipulated zero-rational-direction orbit result shows this saturation contains every such period. It does not, by itself, cover every period of the other two rationality types.

The rational-direction construction uses `D_v={P:v∈P}` with its **relative real topology**, and the smoothly varying normalization `[Im σ]=v`. This is not a complex-open Kuranishi neighborhood. Indeed D_v is totally real: at P its tangent consists of variations of the second real direction with v fixed, whereas the complex structure rotates that variation into one moving v. More invariantly, represent a tangent by `δω∈H^(1,1)`; the condition for v to stay in the real period plane makes δω, up to a fixed phase, real. Both δω and iδω satisfy it only when δω=0. Thus a holomorphic period map with image in D_v has zero derivative and is locally constant. The action-conservation proof on D_v cannot simply be promoted to a nonisotrivial holomorphic family over a complex base.

At a rational period plane the pinned projective construction uses proper genus-one source curves. Its persistence in a full Kuranishi neighborhood is precisely what the audited class obstruction forbids. Density of covered points, Lárusson's finite-window bounds, or individual orbit choices do not extend an Oka-map property to the missing parameters. No conclusion for arbitrary families has been extracted from these transports.

## 3. Route two: a compatible global germ and an exhaustion that permits rechoosing maps

### G102 — compatible recentered germ along the entire central spray

Retain the hypotheses and chosen S0 of A98. There are V and δc>0, fixed once, an open set

`𝒟 ⊂ V×C²×Δ_δc^q`

containing `V×C²×{0}` and a product `V×Δ_rc²×Δ_δc^q` for some rc>0, and a jointly holomorphic map G on 𝒟 such that

`πG=b`, `G(z,0,b)=f(z,b)`, `d_wG(z,0,b)=L(z,b)`, `G(z,w,0)=S0(z,w)`.

For each finite R a δ_R>0 gives `V×Δ_R²×Δ_δR^q ⊂𝒟`. All these restrictions agree on their overlaps. The same holomorphic affine recentering a(z,b)+C(z,b)w is used for every R. No preservation of a prescribed higher b-jet is assumed. No product `V×C²×Δ_δ` with δ>0 is asserted.

**Proof.** Put `M=U0×C²`, a Stein manifold, and form the closed graph of S0 in `M×X` over b=0. It has a Stein neighborhood W contained in the submersion locus. On W the vector bundle of vectors vertical over M maps surjectively to the pulled-back TB. Cartan B lifts each base coordinate vector field to a holomorphic vector field Z_i on W, vertical over M. This uses the entire graph, not a countable selection of fields on expanding compact sets.

For each i the local holomorphic flow is defined on an open neighborhood of W×{0}. Restrict it to sufficiently small discs in time about zero; uniqueness identifies these local flow maps on overlaps. Compose the q flows for times b_1,…,b_q starting at `(z,w,S0(z,w))`. The condition that all intermediate points and times lie in their flow domains is open. Its component near `M×{0}`, or a smaller open neighborhood of that slice, gives a jointly holomorphic `S~(z,w,b)` on an open set 𝒟0 containing `M×{0}`. Each flow changes only its specified base coordinate, so `πS~=b`, and the zero-time composition is S0. There is no assertion of a time radius uniform on the noncompact M.

Choose `K⊂V⊂⊂V+⊂⊂U0`. Compactness of `closure(V+)×{0}` in M gives one small w-ball and b-ball on which S~ and the relative chart E of A98 are defined. Its uniform contraction gives a(z,b) and `C=(D_wH(z,a,b))^(-1)` on a neighborhood of `closure(V)×closed Δ_δc`, after decreasing δc. Their identities and bounds are independent of any later R. At b=0, a=0 and C=I. Define

`𝒟={(z,w,b)∈V×C²×Δ_δc : (z,a(z,b)+C(z,b)w,b)∈𝒟0}`

and `G=S~(z,a+Cw,b)`. This set is open, contains the whole central slice, and, by the compact core margins, contains a uniform core product after reducing rc,δc. The exact identities follow exactly as in A98. For any R, compactness of `closure(V)×closed Δ_R²×{0}` in the larger retained source gives a positive product base radius contained in 𝒟. Taking finite successive minima makes δ_R decreasing if wanted. Compatibility is automatic because all maps are restrictions of G. ∎

This proof also pays all formal orders at once: the b-Taylor jets of G along `(V×C²)×{0}` are compatible holomorphic infinitesimal maps over the whole entire w-source, with the prescribed moving core and first w-jet at every order. In each local target chart they are ordinary holomorphic Taylor coefficients; on overlaps they obey the target coordinate change identities. They need not be uniformly convergent on a product with one base radius. This is stronger than an isolated H¹-vanishing calculation, but is still a technical consequence of the global Stein graph lift.

The apparent `1/R` cost of the original affine recentering estimate need not itself be the obstacle. Choose δc so that `|a|≤1/2`, `||C||≤3/2`. For R≥1, `|a+Cw|≤2R` on |w|≤R. Use the finite deformation window of radius `2R+1`. The constants controlling the recentering then stay fixed; the remaining allowable base radius is that of the horizontal flows on the expanding compact source. Nothing in the construction bounds those time radii below. A compact target fiber does not make W, the source graph neighborhood, or these lifted fields compact or uniformly controlled.

The moving-pole family has exactly such a compatible germ: its local expansion before quotienting is `Σ_(k≥0)b^k w^(k+1)`, with kth coefficient norm `R^(k+1)` on |w|≤R and radius `1/R`. Every formal order and every finite window exist. This demonstrates the analytic distinction without disproving possible better choices of G.

### E102 — fixed-domain exhaustion with only core domination retained

Here is an exact sufficient extension interface, allowing maps to be reselected rather than continuing G102. Let K be compact convex, let f be a lift on a neighborhood, and set `g=πf`, allowed nonconstant. Take a vertical local chart spray

`F0(z,w)=E(z,w)`, `πE=g(z)`, `E(z,0)=f(z)`, `d_wE(z,0)=L(z)`

on a neighborhood of a bounded convex `closure(V0)` containing K and a closed small w-polydisc. Rescale w to make its radius exceed R0=1. Fix decreasing positive source margins

`a_n=a_∞+(a_0-a_∞)2^(-n)`, `a_∞>0`, `V_n={dist(z,K)<a_n}`,

with all closures in the original source neighborhood. Fix `R_n=n+1`. Choose a complete compatible Hermitian distance d on X.

**Extension interface (not proved for arbitrary K3 families):** for this initial map and arbitrarily small prescribed positive summable errors ε_n, there exist holomorphic maps F_n on neighborhoods of `closure(V_n)×closed Δ_Rn²` with

`πF_n(z,w)=g(z)` and `sup_(closure(V_(n+1))×closed Δ_Rn²) d(F_(n+1),F_n)<ε_n`.

If this interface holds, after one fixed further shrink inside V∞ it produces exactly the spray required by R98 with N=2. No exact interpolation at intermediate stages, and no agreement with a prescribed S0 for w away from zero, is necessary.

**Limit and jet proof.** Let `V∞={dist(z,K)<a∞}`. For every compact subset of `V∞×C²`, all sufficiently late F_n are defined on a common neighborhood. The tail distance is bounded by the tail of Σε_n, so completeness gives uniform convergence there to F. The limit is holomorphic: at a point choose a target chart about its limit value; continuity of the uniform limit on a smaller compact source neighborhood places all late maps there in this one chart. Coordinate functions then converge uniformly and their limit is holomorphic. This uses the constructed Cauchy estimates in distance, not a normal-family assertion about all holomorphic maps to a compact target. Continuity of π gives `πF=g` exactly.

Choose a fixed smaller z-neighborhood V′ of K with closure inside V∞, and a radius ρ>0 whose closed w-disc lies strictly inside the initial chart domain. The inverse graph chart of E contains a fixed metric tube around its image over a slightly larger compact product. For total error Σε_n sufficiently small, `H(z,w)=E(z,·)^(-1)F(z,w)` exists there and is uniformly close to w. Choose the metric error so that, in these fixed coordinates,

`sup|H-w|<τ`, with `τ<ρ/8` and `4τ/ρ<1/4`.

The scalar Cauchy bound on each of two w components, summed in the maximum operator norm, gives `||D_wH-I||≤4τ/ρ<1/4` on |w|≤ρ/2. For each z, the map `w↦w-H(z,w)` sends the closed ρ/2 ball into itself and contracts; its fixed point a(z) satisfies H(z,a)=0 and is holomorphic in z. In fact |a|≤τ. Let `C(z)=(D_wH(z,a))^(-1)`. Then

`S(z,w)=F(z,a(z)+C(z)w)`

is defined on `V′×C²`, preserves g, has exact core f and derivative L. Its affine argument has no domain restriction because F is entire in w. All required identities hold on one V′ fixed independently of w. This proves E102. ∎

For example, `ε_n=ε 2^(-n-1)` pays the total ε budget. The geometric losses are `a_n-a_(n+1)=(a0-a∞)2^(-n-1)` and sum to `a0-a∞`, leaving a positive margin. The limit proof does not require uniform derivative bounds on the expanding outer w-boundaries, nor dominance of F_n there. All derivative and inverse estimates used to restore the first jet are on one fixed initial compact product.

### Where the relative extension attempt stops

On a convex bump one can construct small relative chart sprays and carry out the source's vertical Cartan splitting once two sufficiently close holomorphic lifts on the overlap have been supplied. What is missing is a lift on the *new* part, holomorphic in z and exactly over g(z), which approximates the old map on the overlap on the prescribed V_(n+1). Fixed-target Oka approximation chooses it separately in each X_b. A98 or G102 deforms a chosen finite approximant over some small base neighborhood depending on that approximant. Neither guarantees the predetermined source/base margin at step n.

Covering the base by many such neighborhoods does not yet solve this. The separate approximants agree approximately with F_n on the old w-region, but on intersections of base patches in the new w-region they can be unrelated. Gluing the base patches needs transitions there too, not just on the old region. The lower splitting estimates solve a *small* jump problem; they do not create the missing smallness. Replacing them by Lárusson's fiberwise bounds still supplies neither holomorphic choices nor close overlaps in the moving family.

Thus the missing estimate can be stated concretely: execute these relative bump extensions with any prescribed summable loss of z-domain, and any prescribed ε_n error on the whole previous compact product, while keeping `πF_n=g` exactly. The input map may be reselected at each stage subject only to this approximation. There is no requirement to preserve the higher b-jets of G102 or a fixed central spray off its core. This weaker, adaptive problem is not refuted by the pole example. It remains an actual construction problem, rather than a consequence of compactness or finite-window diagnostics.

## 4. Stronger companions and primary operations: scope comparison

The complete 749-manuscript/10,373-original domain is reused by reference. The inherited I98 screen binds its 28 selected title families, 423 representations and 56 statement slices; no new manuscript theorem asserting an arbitrary K3-family Oka map was found in the additional exact lexical searches. Searches include false positives and duplicated representations and are **not** a semantic audit of 749 manuscripts. The one narrow family query's two hits are “Lokal-triviale Familien” bibliography entries, not relative Oka statements.

The actual decisive comparisons are these:

* The pinned K3 theorem is fixed-target CAP for all complex K3 surfaces and all source dimensions. Its projective vector-bundle-spray corollary explicitly retains projectivity. Its complete lower operations and all three period types were examined above. The punctured-K3 and relative splitting targets from I98 are not renamed as findings.
* The semialgebraic-cover Remmert/Stein assertion, special-Kähler Albanese splitting, and integrable-tangent universal-cover splitting already have their own conclusions and hypotheses. None is a theorem about holomorphic selection of lifts for a varying target with prescribed base. The October 6/7 MMP/abundance companions retain the hypotheses and distinctions frozen in I98's statement screen. They supply no missing spray extension interface. No Hodge/Kuga–Satake or topology branch is reopened.
* Lárusson, [*Deformations of Oka manifolds*, v1](https://arxiv.org/abs/1106.5300v1), was read in full, including the endings of Theorem 7, Lemma 11, the lower semicontinuity argument, and Theorem 16. Its compact-set uniform Oka assertion is already available for the stipulated K3 fibers. Its definition controls each finite quintuple `(K,U,V,r,ε)` and chooses approximants in individual fibers. The proof deforms one chosen approximant on a relatively compact domain. Its tori theorem instead uses an explicit universal-family addition spray and local versal pullback. That latter mechanism explains what an actual family argument requires; it is not present just because the K3 fibers are Oka.
* Kusakabe's [v1 criterion](https://arxiv.org/abs/2003.03757v1), Definitions 1.1/1.2, Theorem 1.3, Proposition 5.3 and Corollary 5.7, has the exact entire spray variable on one source neighborhood. Its relative CAP Definition 5.1 keeps a fixed holomorphic map `Ω→B` over all `Ω×C^N`. Its local spray/right-inverse and recentering operations support A98 and E102. They do not replace the relative CAP input. Corollary 5.13 requires Zariski-open neighborhoods in the *total space* whose restrictions already have POPAI; an arbitrary coordinate chart or an open period region is not that hypothesis.
* Xie–Zhao, [*Periods of Oka K3 surfaces are dense*, v2](https://arxiv.org/abs/2608.24392v2), Lemma 3.1, Propositions 3.2/3.3, Corollary 3.4 and the complete Proposition 4.4, provide the flow/spanning operations used by W98. W98 pays compactness by proper h_i. The retained-pencil deformation is over `per^(-1)(D_Q)`, with `D_Q` orthogonal to the specified lattice; extending the line bundles and their sections uses those Hodge conditions. Neither the density assertion nor this lattice-constrained family is R98.
* Kusakabe–Matsumura, [*Atiyah classes and ellipticity of Oka manifolds*, v1](https://arxiv.org/abs/2610.12175v1), Theorem 1.2(2) and complete Examples 2.9/2.10, genuinely assert the compact Kummer obstruction used by I98. The proof uses meromorphic Taylor coefficients, algebraic reduction of P(E), a hypersurface sent into an exceptional curve, and a branched double cover to continue the squared displacement. It does not say that a Stein graph has no local chart spray. The compact-target vector-bundle notion is kept separate throughout.
* The same current paper's Theorem 3.1 and the complete used bump-extension and exhaustion operations in §3.2 were also inspected. Its Lemma 3.17 invokes fixed-target Oka approximation on `V′×P1` to obtain the new map G before the weighted splitting is used. Turning that into a lift exactly over a prescribed varying base would require the relative approximation currently missing. Positivity of a line bundle and a local compact-target spray are additional hypotheses for its global ellipticity theorem; they are not assumed for arbitrary K3 families. Thus this later operation does not already close R98.

Current arXiv abstract/version pages were fetched in this round for these four primary papers and Forstnerič–Lárusson `2502.20028`; they retain v1, v1, v2, v1 and v6 respectively. The primary bodies and fixed-version Xie–Zhao byte identity are inherited, immutable, and selectively replayed by the original verifier. No absence-of-title argument establishes priority. The named significance remains the K3 case of the proper-Oka-fiber question expressly posed by Lárusson. No verified MathDB page or ranking is added.

## 5. Evidence and handoff

The original I98 task JSON, the complete I102 task JSON containing the supplied original brief/report/final parent response, the original I98 report, and the immutable parent verification JSON are snapshotted in full. AGENTS.md, upstream metadata, complete tree, catalogue and all four informational ledgers are also frozen. Only the four live informational ledgers may drift; their snapshots may not. The I98 seal and all its owned files, plus the inherited complete original-domain mapping, are bound by hashes without copying the corpus. No active I100/I101 output is bound.

The read manifest uses **1-based inclusive LF-split ranges, no newline appended to the selected passage**; formfeeds remain within a line. It records source and passage hashes, total LF/newline/splitlines counts, pinned raw URLs and original Git blob IDs where applicable. The complete proof-unit readings are distinguished from statement and history screens. The two new lexical multisets use Python `read_text(errors='replace').splitlines()` with universal-newline translation and retain exact expressions and ordered hits. The inherited replay checks all 10,373 original Git/SHA identities and all 776 inherited PDF-text hashes, but re-extracts only five unique primary PDFs and three selected pinned PDFs. This is the exact replay limit, not universal PDF extraction.

The I102 verifier is offline and read-only: no network, output-file writes, bytecode, repair, or reseal. It also runs the unchanged frozen I98 verifier. Preparation failures, truncated exploratory output and the inherited font warnings are retained. Validation is run before one final seal; the seal excludes only itself and binds the exact owned inventory. Finite arithmetic diagnostics check the recurrences and stated budget algebra, not the universal analytic claims.

Run from the project root:

`python -B frontier/experiments/i102_relative_k3_oka_construction/verify.py`

**Parent handoff:** A98, W98 in the precise reduced POPAI category, and both original method obstructions pass independently without proof repairs. G102 is an actual compatible whole-central-slice holomorphic germ with exact moving first jet; S102 is an actual parameter-preserving sewing theorem with explicitly stronger input; E102 rigorously explains how adaptive approximations would produce the required entire spray while preserving only the final core/first jet. All are technical bridges. The unsupplied estimates are the holomorphic infinite-chain selection on one target neighborhood and/or the adaptive relative extension with prescribed summable source losses. Period transport has been paid only conditionally where a full-open-region family theorem is available; it does not cover arbitrary periods by fiat. R98 is unproved and unrefuted. No new candidate is sent for final acceptance and no count increment is requested.
