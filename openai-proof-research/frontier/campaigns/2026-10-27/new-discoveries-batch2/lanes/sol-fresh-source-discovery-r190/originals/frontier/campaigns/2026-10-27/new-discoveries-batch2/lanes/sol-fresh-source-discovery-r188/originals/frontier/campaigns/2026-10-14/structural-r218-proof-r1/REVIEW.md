# Structural218 — independent round-one correctness review

**Verdict: PASS for the entire unchanged frozen THEOREM.md and submitted AUTHOR-PROOF.md.** This is a correctness verdict only, under the stipulated upstream premises and the hypotheses actually frozen. No essential mathematical repair, substituted proof, restricted target, or changed quantifier is needed. All objections below resolve within the submitted argument. No unresolved mathematical correctness obligation remains at this scope. No contribution grade, acceptance, count, priority clearance, or formal proof certification is assigned.

The reviewed statement is THEOREM.md, all 33 lines / 3717 bytes, SHA256 `179ae89c876e18067a24b6be7a43a6eee3d6b4c697ab8d6e07a27d203feda8fe`. The reviewed proof is AUTHOR-PROOF.md, all 164 lines / 13002 bytes, SHA256 `cbfb43a1bf679f28ad840e418009ff4198428d8ba84bd7f22cbb638d40e1619f`. Both were read directly, fully, and without truncation. Locations below use those original files' one-based lines; exact byte offsets are retained in private/author-line-offsets.json. Supporting author prose was also read, but neither its conclusions nor its read log was adopted as independent reasoning.

This was a fresh adversarial first-round review. There were no inherited mathematical objections, responses, verdicts, or peer-review inputs. “Response” below means the strongest response already available in the unchanged submission, independently checked here; it does not imply communication with the author. All reasoning takes place on the fixed oriented flat torus, without pulling back by a parameter-dependent gauge.

## 1. Arbitrary input data and actual parameter range

Locations: statement 5–9; proof 23–41, 45.

**Challenge.** A product-bump example would not prove the assertions for an arbitrary allowed two-variable f. The zero set of p could have many components or irregular boundary, p could be very large, c could be very small, or f might accidentally be constant. One must also keep the bounds valid at every parameter.

**Independent check and resolution.** A nonnegative nonzero bump p supported in a proper circle arc can be normalized to mean one. A nonzero bump χ with values in [0,1] supported in an open arc of its zero set gives f(x,z)=χ(x)χ(z), so the hypotheses are nonvacuous. For general permitted p,f, continuity and f≥0, f≠0 imply c>0 and a nonempty open set {f>0}; the volume-one normalization and f≤1 give c≤1. Since mean(p)=1, p is positive at some point, and hence on an open interval. At every pair with first coordinate in that interval, p(x)f(x,z)=0 forces f=0. A nonzero constant f is therefore impossible. None of this requires product structure or regular zero-set boundaries.

For any s in [0,1/4], A_s≥s and mean(A_s)=1; q_s≥s and mean(q_s)=1. Multiplying its definition by f uses exactly the two assumed identities p(x1)f=p(x3)f=0 and gives q_s f=s f everywhere, including points where f=0. Thus mean(q_s f)=sc. The actual path has 0<s(t)≤e^{-1}/4<1/4 for 0<t≤1, so using the larger interval [0,1/4] is conservative. The bound |a_s|≤s(1+s)≤5/16 and r_s<2 is valid, independently of the height of p. The quantifier over sequences is understood in the already specified parameter domain; finitely many terms are immaterial to the limit argument. There is no restriction of the arbitrary p,f quantifier. Resolved by the submitted Section 2.

## 2. Signs, complex orientation, and uniform taming

Locations: statement 5, 7, 11; proof 5–21, 43–47.

**Challenge.** A sign error in converting a two-form into an endomorphism could reverse taming. Positive wedge square alone also does not select the positive Hermitian component.

**Independent check and resolution.** With g(Iu,v)=U(u,v), the coordinate images are I(e1)=e2, I(e2)=−e1, I(e3)=e4, I(e4)=−e3. For K defined by V, K(e1)=e3, K(e3)=−e1, K(e2)=−e4, K(e4)=e2. Hence I and K are skew, each squares to −Id, and IK=−KI. Therefore L=I+aK satisfies L²=−(1+a²)Id and LᵀL=(1+a²)Id. J=L/r is orthogonal and J²=−Id with precisely the claimed fundamental form.

The Hodge signs are *e12=e34, *e13=−e24 and *e14=e23. Thus U,V,W are mutually orthogonal self-dual forms of squared norm two, and F²=2dV. Its complex orientation agrees with the fixed one. Since IK is skew, ⟨Iv,Kv⟩=0, whence U(v,Jv)=⟨Iv,Jv⟩=|v|²/r≥|v|²/2. This checks the argument order in U(v,Jv), rather than silently using U(Jv,v). U is closed with square 2dV. The constant 1/2 is valid uniformly over the whole interval and over all admitted data.

For an orientation-compatible orthogonal J, Λ_J^+=RF⊕Λ_g^− and Λ_J^−=F^⊥∩Λ_g^+. In a g-unitary basis a real invariant form is a Hermitian form with eigenvalues λ1,λ2. Its self-dual coefficient is (λ1+λ2)/2, its square is 2λ1λ2 dV, and |α|²=λ1²+λ2². Positive trace and positive square force both eigenvalues positive. The proof supplies both signs whenever it uses this criterion. Resolved without an altered convention.

## 3. Smoothness, flatness, and bounded seminorms

Locations: statement 11, 16, 27; proof 43–47, 80–84.

**Challenge.** Parameter flatness might hold only pointwise in x, or only for a finite number of derivatives. Smoothness on a closed interval requires the endpoint interpretation, and bounds must not silently be uniform over unbounded sets of input functions.

**Independent check and resolution.** Extend s by zero for negative t; its positive-side derivatives are exponential decay times powers of t^{-1}, hence all tend to zero at t=0. Its formula extends beyond t=1 as well. Every mixed spatial/parameter derivative of a=s f−s²c exists, and every positive parameter-order derivative at zero vanishes, also after any number of spatial derivatives. Composing with the globally smooth matrix map a↦(I+aK)/sqrt(1+a²) proves the asserted joint smoothness and flatness of J−I. The denominator never vanishes. The polynomial-in-s formula for η and the formula for ζ have the same smoothness property.

Each fixed mixed derivative is bounded on the compact product [0,1]×X. This means one finite bound for each seminorm and each fixed admissible input pair; it does not mean a common bound for all derivative orders or all possible smooth f. That is the statement's ordinary meaning, not an extra condition or repair. The metric, volume and injectivity radius are fixed. Resolved.

## 4. Exact class of the displayed family

Locations: statement 13–16; proof 49–67.

**Challenge.** An off-diagonal coefficient with zero total mean need not be exact on an arbitrary manifold. Here it must be checked in both variables, with a genuinely periodic primitive. There must be no hidden gauge.

**Independent check and resolution.** A_s(x1)e12 and A_s(x3)e34 are closed because their coefficient derivatives repeat a wedge coordinate. The off-diagonal coefficient h=2s²(f−cq_s) depends only on x1,x3, so h e13 is also closed. Each A_s has mean one; h has total mean zero. The diagonal differences have periodic primitives P_s(x1)dx2 and P_s(x3)dx4, where P_s'=A_s−1.

For arbitrary smooth periodic h(x,z) of zero total mean, m(z)=∫h(x,z)dx is smooth and periodic with mean zero. H(x,z)=∫_0^x(h(u,z)−m(z))du is periodic in x because its x-increment over a period is zero, and periodic in z because its integrand is. M(z)=∫_0^z m(v)dv is periodic because m has zero mean. All derivatives match at the seams. Directly,

    d(H dx3)=(h−m)e13,
    d(−M dx1)=+m e13.

Their sum is h e13, with the claimed plus sign. These global primitives on the fixed coordinate torus establish exactness of every nonconstant contribution and [η_s]=[U]. They also depend smoothly on s, although a smoothly chosen primitive is not needed for the class assertion. No diffeomorphism is used. Resolved by the explicit primitive already in the proof.

## 5. Invariance, positive square, and the precise degenerate endpoint

Locations: statement 13–16; proof 69–84.

**Challenge.** The correction could preserve cohomology but destroy positivity, especially on the open region where p vanishes. Conversely, η_0 cannot supply the positive endpoint fibre claimed elsewhere.

**Independent check and resolution.** Hodge projection gives η_s^+=q_s U+s²(f−cq_s)V. The exact identity q_s f=s f gives q_s a_s=s²(f−cq_s), so η_s^+=q_s r_s F_s. The anti-self-dual part is automatically J_s-invariant, and this establishes full invariance. Every wedge involving the e13 correction is zero, including its self-wedge. Thus η_s²=2A_s(x1)A_s(x3)dV>0 for s>0, while q_s r_s>0. The two-eigenvalue criterion proves compatibility without any smallness assumption on p or perturbative norm estimate.

At s=0, η_0=p(x1)e12+p(x3)e34 is a smooth closed J0-invariant nonnegative form. On {f>0} both p factors vanish, so the entire form is zero. This is a nonempty open set, and η_0 is not symplectic. Its class is still [U]. Its square may have positive total integral while it vanishes on an open subset; there is no contradiction. The theorem correctly uses U itself, separately, to establish the nonempty compatible fibre at zero. It never calls η_0 compatible. Resolved.

## 6. Every representative, not just η: uniqueness, periods, and the norm constant

Locations: statement 18–23; proof 86–104.

**Challenge.** Could a different compatible representative avoid the concentration, perhaps by a large anti-self-dual component? The division by s is invalid at zero, and the normalization factors of two must be exact.

**Independent check and resolution.** For any compatible α at positive t, invariance gives α^+=bF_t with b=(λ1+λ2)/2>0. Therefore q=b/r_t is smooth and positive and is uniquely determined, since U+a_t V is nowhere zero. Orthogonality gives q=⟨α,U⟩/2. The fixed de Rham class implies

    ∫α∧U=∫U∧U=2,    ∫α∧V=∫U∧V=0.

Self-duality and the squared norms two turn these into ∫q=1 and ∫q a_t=0. Substitution of a_t=s f−s²c and division by s>0 give ∫q f=sc. This uses no endpoint division and no choice of representative. Positivity gives

    |α|²=λ1²+λ2² ≤ (λ1+λ2)²=4q²r_t²,

hence |α|≤2q r_t≤4q. Thus an arbitrarily large anti-self-dual component cannot evade the trace bound. For every δ>0, δ∫_{f≥δ}q≤∫qf=sc. The assertion also holds if the level set is empty, or δ>1. Resolved with all constants as submitted.

## 7. Compactness for arbitrary sequences and every possible limit

Locations: statement 25; proof 106–112, 130–136.

**Challenge.** Weak-* compactness is not in general sequential without an appropriate predual; one must extract a common subsequence for all coefficients. A proof for η alone would not establish the universal assertion.

**Independent check and resolution.** The previous section applies to each arbitrarily chosen α_n. It gives ∫|α_n|≤4. Each of the six signed coefficient measures has total variation at most this bound. C(X) is separable because X is compact metrizable; bounded sets of its measure dual are weak-* sequentially compact. Extracting for the finite list of coefficients gives a common subsequence. The coefficient vector retains a finite variation bound (equivalently, work in the finite-dimensional vector-valued measure dual). Since q_n=⟨α_n,U⟩/2 exactly, no independent incompatible subsequence for q is needed: q_n dV tends along the same subsequence to ν=⟨A,U⟩/2. Testing with nonnegative functions and with 1 proves ν≥0 and ν(X)=1.

All subsequent arguments use only these universal identities and the mass bound. They therefore apply to any coefficient weak-* convergent subsequence of any choices α_n. No uniqueness of the limit, equality of its support with {f=0}, absence of singularities, or convergence of nonlinear wedge squares is asserted. Resolved.

## 8. Distributional closedness and the full cohomology class

Locations: statement 25; proof 114–118.

**Challenge.** The two pairings used earlier fix only two linear combinations of mean coefficients. A distributional class assertion requires all six zero modes, and the Fourier primitive needs the right sign and an actual distribution.

**Independent check and resolution.** Write α_n=U+dγ_n; this is the meaning of the assumed class [U] for each n, with no bound on γ_n needed. For every constant two-form θ, ∫⟨α_n−U,θ⟩dV=∫dγ_n∧*θ=0, since *θ is closed and X has no boundary. Thus all six coefficient means agree with U, and testing weak-* convergence against the constants gives the same for A. This justifies proof line 114 directly from its existing class assumption, rather than incorrectly deriving it from only the U,V equations.

Exterior differentiation is continuous on distributions. Consequently dA=0, and D=A−U is closed with zero Fourier mode. For Fourier convention exp(2πi k·x), closedness is k♭∧D̂(k)=0. The submitted definition

    β̂(k)=(2πi |k|²)^{-1} ι_k D̂(k),   k≠0;   β̂(0)=0

gives (dβ)̂(k)=|k|^{-2} k♭∧ι_k D̂(k)=D̂(k), by the contraction/wedge anticommutator. The sign and factor 2πi are correct. The Fourier coefficients of D are bounded because it has measure coefficients; β̂(k)=O(|k|^{-1}) for k≠0. More generally polynomial growth would suffice. This is a periodic distributional one-form, with real conjugacy symmetry when D is real. The zero mode also agrees. Thus A−U=dβ in the distributional de Rham complex.

This proof uses closed distributional two-forms (dA=0). Source342's metric-dual convention for two-currents uses d* instead; silently identifying those conventions would be wrong, but the submission does not do so. Its coefficient-form/Fourier argument is internally consistent. Resolved.

## 9. Varying-J invariance, positivity, and the support assertion

Locations: statement 25; proof 120–134.

**Challenge.** Positivity and invariance refer to different J_n, and weak convergence alone does not control products with varying coefficients. Support control for the scalar trace alone also needs transfer to the entire form.

**Independent check and resolution.** The anti-invariant projection R_t is a smooth coefficient-wise bundle map, uniformly converging to R_0. Since R_{t_n}α_n=0, the variation of R_0α_n is bounded by ||R_0−R_{t_n}||∞∫|α_n|, which tends to zero. Multiplication by the fixed smooth R_0 is continuous for these limits, so R_0A=0.

For a smooth local vector field v and nonnegative smooth test φ, α_n(v,J_{t_n}v)≥0. Replacing J_{t_n} by J_0 makes an error bounded by C||φ||∞||v||∞²||J_{t_n}−J_0||∞∫|α_n|, which tends to zero. Passing to the limit proves A(v,J_0v)≥0 as a scalar measure. Local frames and polarization give precisely a nonnegative invariant measure-valued two-form, without strict positivity or regularization. Only bounded mass is used, not bounded derivatives of α_n.

Testing the universal moment against fixed smooth f gives ∫f dν=0. A nonnegative measure with this property is supported in {f=0}. For the form itself, every smooth test two-form β with compact support in {f>0} has f≥δ>0 on its support; the pointwise norm bound yields |∫⟨α_n,β⟩dV|≤4||β||∞s_n c/δ→0. Thus A vanishes on the whole open set {f>0} and is supported in the complementary closed set. Smooth compactly supported tests suffice to identify vanishing there. No regularity of the level-set boundary is needed. Resolved.

## 10. Exclusion of all smooth compatible endpoints and the topology of selection

Locations: statement 25; proof 136–138.

**Challenge.** The failure of η to stay symplectic at zero does not alone rule out another selection. Compactness of a subsequence also does not by itself address every distributionally convergent sequence or the topology meant by “continuous.”

**Independent check and resolution.** If arbitrary α_n converged distributionally to any smooth J0-compatible α0, then q_n would converge distributionally to the smooth positive function q0=⟨α0,U⟩/2. Testing with f forces ∫q0 f=lim s_n c=0. This is impossible: f is nonnegative and positive on a nonempty open set, and q0 is everywhere strictly positive. This argument directly addresses distributional convergence, independently of extraction. Equivalently, the established weak-* limits vanish on that open set and cannot be compatible endpoints.

Precisely, it suffices to use the weakest ordinary distribution topology here: convergence against every fixed smooth test form, in the fixed coordinate identification, or σ(D′,C∞) component by component on the compact torus. The contradiction already uses only the single smooth functional α↦∫f⟨α,U⟩/2. A selection continuous into this weak distribution space would make that functional continuous at zero, giving the same contradiction on every [0,ε], 0<ε≤1. Thus the result also excludes continuity for the usual stronger distribution topology. Coefficient C0 continuity and smooth dependence imply this weak continuity. There is no unsupported assertion that these topologies coincide or that the choice is merely a continuous path of cohomology classes. Resolved for every endpoint and every interval in the frozen statement.

## 11. Exact anti-invariant spaces, kernel jump, and b+

Locations: statement 27; proof 140–146.

**Challenge.** Closed anti-invariant forms might have nonconstant coefficients, or exact representatives might enlarge the claimed cohomology spaces. Constancy of the metric does not alone imply that every closed form is constant.

**Independent check and resolution.** Anti-invariance gives self-duality for this orientation and this same fixed Hermitian metric. If dψ=0 and *ψ=ψ, then d*ψ=0, so ψ is harmonic. For the flat torus the Hodge Laplacian acts on each coefficient as the scalar flat Laplacian. Its Fourier symbol is 4π²|k|²; only the zero modes can be harmonic. Therefore ψ=uU+vV+wW with constants, not arbitrary coefficient functions. Orthogonality to F_t is exactly u+v a_t(x)=0 everywhere.

At t=0 this is u=0, leaving V,W. At any positive parameter, a_t is nonconstant because s(t)>0 and f is nonconstant. Subtracting its values at two points gives v=0, then u=0, leaving W. Constant nonzero forms cannot be exact, and V,W have independent de Rham classes, so these representative computations give exactly the stated cohomology spaces, not just inclusions. All harmonic self-dual forms are the three-dimensional span of U,V,W. The complementary constant anti-self-dual basis has negative square, so b+=3. This is the standard harmonic method also present in the actual source torus example and DLZ primary interfaces. It validates the kernel jump; it cannot provide a constant-rank inverse through zero. Resolved.

## 12. The free-class family and consistency of all endpoints

Locations: statement 29–31; proof 148–158.

**Challenge.** ζ might not be closed for two-variable f, might fail positivity, or might accidentally stay in [U], contradicting the nonselection statement.

**Independent check and resolution.** Since a depends only on x1,x3, da∧e13=0, so ζ=U+2a e13 is closed. Its self-dual part is U+aV=rF, and its square is exactly 2dV because e13 wedges trivially with U and itself. The trace is positive, so the same two-eigenvalue test proves compatibility for all t, including ζ0=U. Smoothness follows from the already checked coefficients.

The off-diagonal coefficient's mean is 2∫a=2sc(1−s). Subtracting this mean leaves a two-variable zero-mean function, whose e13 multiple is exact by Section 4's primitive. Hence [ζ]=[U]+2sc(1−s)[e13] exactly. For t>0, s>0, c>0, s<1, and [e13]≠0, so its class differs from [U]. Thus ζ executes the free-class alternative but is not an exception to the fixed-class universal moment. It requires no volume claim for η and no integrability claim. Resolved.

## Source and primary application audit

All operative upstream proofs at the stipulated pin were treated as true, not audited. I independently retrieved and authenticated all 25 Source342 blobs against the complete pinned tree and the admitted author bytes. I read both versions' differing operative introduction text, both drivers' abstract/include ranges, the preambles, the bibliography and its actual version difference, and all eight October sections. Actual byte equality of sections 02–07 justifies reuse for September. In particular, the full October cone argument and its torus example were read, not inferred from a catalogue description.

The October compatible-cone test concerns a fixed J, the invariant subspace (H_J^−)^⊥, closure within that subspace, and strict pairing against every nonzero closure element, with the tested class itself in the invariant taming cone. Its internal closed lift, exact-form correction, prescribed-class separation, mass/energy/density/splitting and residual-pairing operations are already available. The submission never derives a prescribed-class parameter selection from that pointwise criterion. It supplies explicit representatives and proves its universal obstruction independently. The older version's broader cone wording is recorded as a version difference and is not used to infer a new fact or to challenge the stipulated upstream truth.

The source's torus construction already uses self-dual normalized directions, explicit closed corrections, and a flat harmonic computation of H_J^−. Those operations do not by themselves disprove this submission. The correctness-specific issue is whether its different nonnegative f and exact shifted period cancellation work for every input and every representative; Sections 1–12 above verify that directly. This paragraph is not a contribution evaluation.

I also read the actual strongest relevant primary statement/proof interfaces in DLZ's cohomology and metric-related-deformation papers, Donaldson's local positive-plane deformation argument and his distinct nonextension construction, Li–Zhang's cone/separation section, Draghici–Zhang's exact-form arguments, and Li–Ning's taming/integrable-compatible path constructions. The pinned companion's smooth-compatible-family lemma was read with its local context. Its smooth rank-two kernel and allowed period variation differ from the jumping kernel and prescribed class here. DLZ/Donaldson allow harmonic positive-plane class changes; a general fixed-class right inverse is not supplied by those arguments. Li–Ning's taming convexity is not compatible-form invariance for a varying J, and its compatible argument uses integrability. None yields a counterexample to the submitted universal moment obstruction. Exact versions, selected boundaries, recovery, OCR and access limits are private/READING-LIMITS.md; no unexamined intermediate is silently treated as independently read.

The actual pinned Lean comparator was inspected in full. Its theorem ends at line 63 in `sorry`. It supplies no proved endpoint or formal coverage of this nominee; neither compilation nor new formalization was performed.

## Final disposition and limits

The strongest attempted escapes were arbitrary high anti-self-dual components, concentration on complicated zero sets, singular coefficient limits, failure to fix all Fourier zero modes, a reversed primitive sign, another smooth positive endpoint, and a local deformation theorem with more period freedom. Each resolves by the unchanged submitted arguments as detailed above. The proof establishes all six frozen conclusions and its operative auxiliary assertions. No essential gap or counterexample remains identified.

The PASS is limited to mathematical correctness of this exact submission on the fixed torus with the stated smooth p,f and interval, under the stipulated source premises. It is not a PASS for an unstated uniform-in-input estimate, integrable deformation theorem, arbitrary gauge, stronger positive limit, prescribed volume, or general parameter-selection principle. These are not omitted frozen obligations.

Reading was bounded. The guarded independent original-history navigation found no eligible mathematical match; excluded namespaces, coarse filters and possible opaque aliases prevent exhaustive historical or worldwide-priority clearance. Primary OCR was not visually certified, and several upstream antecedents/intermediates were not independently read. Actual accidental editorial/adjacent exposures and one recovered output truncation are expressly retained in the private limits record. None supplies an essential premise for the elementary proof audited here. Artifact authentication and the successful rational matrix script corroborate identity and signs only; they were not used as mathematical gates.
