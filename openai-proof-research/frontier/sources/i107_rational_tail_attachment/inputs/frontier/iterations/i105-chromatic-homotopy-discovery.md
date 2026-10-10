# I105 — chromatic homotopy discovery: a rational-tail obstruction

Status: **author-level technical partials; no substantial nomination**. The selected target R105 is unproved and unrefuted. Eight accepted findings remain eight. This is fresh discovery, not an independent review. No child agents, shared edits, staging, commits, or publishing were used.

The hypotheses are the stipulated theorems **and lower proof operations** of `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Nothing below audits their truth or combines contradictory premises. The proofs below need independent review. Evidence replay is not a proof or contribution certificate.

## Scope, source contracts, and the four screens

I read AGENTS.md, the four ledger status/acceptance and relevant history passages, and their headings for duplication. Their snapshots are frozen here; their live versions alone may drift. I101, I100, and I102 remain parked at the gaps in the task. No active I103/I104 artifacts are bound or used. No closed technical lane is reopened.

All symbols in the mathematical development are at a **fixed prime p≥5**. Write S for the derived p-complete sphere, Q=L₀S=Hℚₚ, Aᵢ=LᵢS for Johnson–Wilson E(i)-localization, Rᵢ=L_K(i)S, T=L_K(3)S, and X=L₂T. Unless explicitly forgotten, maps are in Mod_S. No telescope localization is substituted. Finite spectra, dualizable local spectra, and compact local spectra are not identified.

The exact pinned aliases below refer to the entire title directory under `preprints/`; `selected-inventory.json` records individual source representations, URLs reconstructed from the pinned revision, Git blob identities and SHA-256 hashes. The passage manifest records the proofs actually read, not a claim to have read every selected representation.

- **F**: Finite-generation-for-the-Kn-local-sphere-September-24-2026. `01-introduction`, Theorem `thm:main`, is degreewise finite generation, with no uniform generator/torsion bound. `12-sphere`, including its ending, proves mod-p finiteness, compact Nakayama, and the complete height-one formula.
- **S**: Stabilizer-Orbits-and-Thick-Tensor-Ideals-of-Dualizable-Kn-Local-Spectra-September-24-2026. The exact tensor is L_K(n)(−∧−). `06-classification`, Proposition `fin:support` and its proof, gives tensor-ideal support containment, not ordinary finite assembly or a uniform construction length.
- **C**: Cyclic-Length-and-Chromatic-Fixed-Point-Loss-September-24-2026. The statement concerns finite genuine p-local G-spectra for G a finite p-group and every embedded H≤G. `07-support` constructs sharpness witnesses by prime separation; its ending gives the separate p-residual/conjugacy conditions for arbitrary finite groups.
- **G**: Filtered-chromatic-splitting-at-generic-primes-September-25-2026. Range p>n+1. `02-assembly`, Proposition `prop:assembly`, constructs actual quotient maps and finite pullbacks, not just a graded count. `06-constants`, Proposition `prop:modification-transport`, retains products and finite Postnikov sphere coefficients, but its block identity fixes the connected quotient frame.
- **H**: The-height-three-chromatic-overlap-an-explicit-filtration-and-its-attachments-September-27-2026. `02-fracture`, `12-application`, and `12-attachment` were read through their endings. We use its **same** F₄, a:F₄→X, rational quotient V, and g=∂ₐt, not a replacement filtration. Its `11-rational` proves the degree-three comparison, retaining the finite Witt maps, limits, and common determinant.
- **O**: A-rational-obstruction-to-strong-chromatic-splitting-at-height-three-September-25-2026. Theorem `thm:main` is nonvanishing of the **canonical** rational K(2)-localization map in degree −3, for the sphere before completion. H's `12-attachment` gives the completion/localization comparison needed here. `07-detection` constructs a K(2)-local completed detector and a factorization into it; a factorization alone is not injectivity of that detector in every degree.
- **W**: Counterexamples-to-weak-chromatic-splitting-sphere-kernels-and-descent-exponents-September-27-2026. The sphere kernels have heights p (p≥5) and p+1 (p≥7). `04-adic`, `08-upper-kernels`, `11-upper-nullity`, `12-coherent-trace`, and `13-exponent-contradiction` distinguish filtration-zero images from actual null maps, and ordinary from local tensors.
- **P**: Failure-of-finite-assembly-for-a-chromatic-overlap-at-the-prime-three-September-25-2026. Its `02-detector` and the complete generic-abutment/final deduction in `10-obstruction` use ordinary thick closure and a semilinear norm constituent. This prime-three theorem is not used at p≥5. Adding a putative determinant-twisted generator would require its actual realization and extension maps; the displayed constituent is not such a realization.

The complete 13,223-entry tree has 749 manuscripts and 10,373 original blob positions. All title leads and stronger relevant pinned companions were checked before selecting R105. The lexical domain reuses 9,340 I14 originals and the I79/I88 mapping for 1,033 additional positions, including 776 PDF-text representations. Two full-domain lexical searches retain exact matched expressions, repeated occurrences, whole lines and splitlines positions. They are **not full semantic reading**. The selected inventory also includes the nearby Hahn–Wilson paper as a title/search comparison, not as a theorem dependency. No later pinned version of the eight listed titles occurs in the complete tree. Current external version checks have the limits recorded below.

Four exact targets were screened:

1. **Uniform torsion from local-sphere finiteness.** At each fixed (p,n), ask for e(p,n) killing the torsion in π_dRₙ for every integer d. This is falsified already at n=1. F's actual fiber calculation gives π_(2t−1)R₁=ℤ/p^(1+vₚ(t)) for nonzero t∈(p−1)ℤ. Taking t=(p−1)pᵃ, a≥0, gives unbounded exponents. This uses the source's exact formula, not a guessed failure of finite presentation. Arbitrary dualizable inputs are not covered by F's restricted coefficient class.
2. **A numerical descent improvement.** In W's upper-height ranges, ask to replace the actual upper exponent a²+2 by a²+1. The only extra degree in `04-adic` is lim¹H^(a²) of finite-quotient cohomology. A finite analytic resolution making those groups finite makes the tower Mittag–Leffler, and W's finite-test/phantom/finite-layer operations would then supply the claimed map nullity. Thus the candidate is a technical sharpening if that finite-resolution input is supplied; it is not nominated. I do not assert the sharpened theorem here, nor transfer this bound to torsion stabilizers or infer it from sphere coefficients alone.
3. **Quantitative genuine realization.** Given finite p-group G, H≤G, n≥0 and 0≤r<ℓ(G,H), construct a finite genuine G-spectrum witnessing K(n+r)-acyclicity at H and nonzero K(n) at G, with an explicit cell/representation-dimension bound depending on (p,G,H,n,r). C already supplies existence for every such tuple, including n=0, by separation of primes. Merely enumerating witnesses or rephrasing its support classification would not count. Its finite product of separating objects has no cell bound on the individual factors. No such bound was obtained, and no algebraic type function was passed off as a realized spectrum.
4. **R105, selected: split the last rational block in the actual height-three construction.** For every p≥5 and every common set of H's allowed choices, ask whether its cofiber triangle
   F₄ → X → V → ΣF₄,
   V=Q[−5]∨Q[−6]∨Q[−8]∨Q[−9],
   splits by an S-linear equivalence **under F₄ and over V**. Equivalently all four components of g=∂ₐt vanish as actual maps. This is stronger than having the given eight-stage filtration and weaker than strong chromatic splitting: it explicitly retains the nonzero middle attachment. The two routes below pay three vanishings and reduce the fourth to a two-dimensional mapping group. Its value for the actual overlap remains unpaid.

R105 relates directly to [the strong chromatic splitting conjecture, MathDB 341679](https://mathdb.com/p/341679/the-strong-chromatic-splitting-conjecture). The observed page records the prescribed wedge and its unit condition, citing Barthel–Beaudry; it provides no ranking warrant. O already refutes that wedge under the stipulated premises. R105 asks for a compatible replacement with its nonsplit middle block retained; solving R105 would not restore the refuted wedge. The primary BSSW v2 discussion of the conjecture and rational theorem distinguishes the rational exterior algebra from the integral factorization requirement.

## Route A: compute mapping spectra, not rationalizations of boundaries

Put ΓZ=F_S(Q,Z), with evaluation ΓZ→Z induced by S→Q. This is the right adjoint to the inclusion of rational S-modules. It is exact. Multiplication by p is invertible on ΓZ, so ΓZ is a Q-module. For rational D,

[ D,Z ]_S = [ D,ΓZ ]_Q.

This Γ is **not** L₀. An attachment can have L₀g=0 while g≠0. Positive-height local targets have ΓRᵢ=0, by localization adjunction: the rational source is K(i)-acyclic. All equivalences involving Γ below are equivalences of actual Q-modules, not E₂-page identities.

### Technical lemma A: three small mapping spectra

For p≥5 there are unit-compatible choices giving

(1) ΓA₁ ≃ Q[−2],

(2) L₁R₂ ≃ A₁∨A₁[−1]∨Q[−3]∨Q[−4], with A₁→L₁R₂ the first inclusion,

(3) ΓA₂ ≃ Q[−4]²∨Q[−5],

(4) F_S(A₁,A₂) ≃ A₁[−2]∨Q[−4]∨Q[−5].

Here Z[j]=ΣʲZ; multiplicities denote finite wedges. None of these splittings is claimed canonical.

**Proof.** Height-one fracture expresses A₁ as the pullback of R₁ and Q over L₀R₁. The height-one calculation in F gives L₀R₁≃Q∨Q[−1], with the rational unit the inclusion of Q. Apply Γ, using ΓR₁=0 and ΓQ=Q, to obtain (1): the fiber of Q→Q∨Q[−1] is Q[−2].

For (2) use G at n=2, p>3. Its first block B=A₁∨A₁[−1] is given by the actual unit and its degree-minus-one class, and its rational quotient is Q[−3]∨Q[−4]. The boundary of that quotient lands in ΣB. By (1), ΓΣB=Q[−1]∨Q[−2]. Maps from Q[−3] or Q[−4] to this Q-module vanish in the derived category of a field. The boundary itself therefore vanishes by the adjunction. A chosen nullhomotopy splits the cofiber triangle under B, giving (2) and its unit condition. This derives the needed height-two module splitting from an accepted lower construction, without presuming an arbitrary spectral splitting is S-linear.

Height-two fracture gives A₂≃R₂×_(L₁R₂)A₁. Applying Γ and (2), the map ΓA₁→ΓL₁R₂ is the inclusion
Q[−2] → Q[−2]∨Q[−3]∨Q[−3]∨Q[−4].
Its fiber is Q[−4]²∨Q[−5], proving (3).

Apply F_S(A₁,−) to the same square. Its R₂ term vanishes because A₁ is K(2)-acyclic. For an E(1)-local target Z, the module localization adjunction gives F_S(A₁,Z)≃Z (on all suspensions). Consequently F_S(A₁,A₂) is the fiber of A₁→L₁R₂. Using the first inclusion in (2) gives (4). This completes every claimed equivalence. ∎

A low-stem fact used below is
π_(−1)A₁=0, and π_(−2)R₁=π_(−3)R₁=0.
For the latter two assertions use F's complete height-one formula: −3 corresponds to t=−1, not divisible by p−1; −2 is neither 0 nor an allowed odd stem. For the first, fracture and π₀R₁=ℤₚ, π_(−1)R₁=ℤₚ give a surjection π₀(R₁∨Q)→π₀L₀R₁ and the injection ℤₚ→ℚₚ in degree −1. The exact sequence gives π_(−1)A₁=0. In particular (4) implies

[ A₁[−3],A₂ ]_S = π_(−3)(A₁[−2]∨Q[−4]∨Q[−5]) = 0.   (5)

### Technical proposition B: one actual residual map

Retain H's W=A₂∨A₂[−1], U=A₁[−3]∨A₁[−4], map d:U→ΣW, F₄=fib(d), and a:F₄→X. Then

ΓF₄ ≃ Q[−4]²∨Q[−5]⁴∨Q[−6]².                         (6)

The last block boundary g has g₆=g₈=g₉=0, and

[Q[−5],ΣF₄]_S ≅ ℚₚ².                                (7)

Thus for the **actual** g₅ one has an equivalence under F₄ and over V

X ≃ fib(g₅:Q[−5]→ΣF₄) ∨ Q[−6]∨Q[−8]∨Q[−9].          (8)

All maps in (8) are in E(2)-local S-modules. The first F₄→X map, hence the original unit A₂→X, is retained. The identification in (7) depends on choices; the vanishing of g₅ does not.

**Proof.** From A, ΓW=Q[−4]²∨Q[−5]³∨Q[−6] and ΓU=Q[−5]∨Q[−6]. Therefore a degree-zero Q-linear map ΓU→ΓΣW can have only one potentially nonzero component: from Q[−5] to the Q[−5] in the second summand ΓA₂ of ΓΣW. This component comes from the projection of d|_(A₁[−3]) onto the A₂ summand of ΣW=ΣA₂∨A₂. That entire map is zero by (5), before applying Γ. All other components vanish by unequal degrees. Hence Γd=0. Applying exact Γ to W→F₄→U and splitting a null boundary over a field gives (6), with the displayed multiplicities.

Now ΓΣF₄ has degrees −3,−4,−5 with multiplicities 2,4,2. The rational adjunction shows that maps from Q[−6], Q[−8], Q[−9] to ΣF₄ are zero, and gives precisely (7). H's construction says X is the fiber of the actual map g:V→ΣF₄. Choose nullhomotopies of its three zero components. In a stable category the fiber of (g₅,0):Q[−5]∨V'→ΣF₄ is fib(g₅)∨V', compatibly with its cofiber triangle. This proves (8). It also proves the assertions about the original last boundaries: H gives them by composing these same gᵢ with Σ(F₄→F_(i−1)). ∎

This is a complete full-scope reduction of B to the accepted height-two construction and ordinary mapping adjunctions. It is classified **technical**, even though an exact printed duplicate has not been identified.

### Technical proposition C: compatible positive-height and finite-input splitting

Let J=K(1)∨K(2), B₂=L_JA₂. There exists an equivalence, compatible with the unit-and-determinant map from L_JW,

L_JX ≃ B₂∨B₂[−1]∨R₁[−3]∨R₁[−4].                    (9)

One choice of (9) gives, for every r≥1, compatible equivalences

X/pʳ ≃ A₂/pʳ ∨ (A₂/pʳ)[−1] ∨ (A₁/pʳ)[−3] ∨ (A₁/pʳ)[−4],  (10)

where compatibility is with the actual Moore quotient transitions. More generally every finite p-local spectrum M with L₀M=0 has a unit-preserving equivalence

L₂L_K(3)M ≃ L₂M∨(L₂M)[−1]∨(L₁M)[−3]∨(L₁M)[−4].     (11)

The same chosen map (9), smashed with M, provides naturality in finite rationally acyclic M. No multiplicative equivalence or canonical choice is claimed.

**Proof.** Apply exact L_J to the height-two fracture square for A₂. Its corners become R₂, R₁ and L_K(1)R₂. From (2), localizing at K(1) gives L_K(1)R₂≃R₁∨R₁[−1], and the map from R₁ is the first inclusion. Mapping from R₁ into the R₂ corner is zero; mapping from R₁ into a K(1)-local S-module is its underlying spectrum by localization adjunction. Therefore

F_S(R₁,B₂) ≃ fib(R₁→R₁∨R₁[−1]) ≃ R₁[−2].            (12)

Under L_J, U becomes R₁[−3]∨R₁[−4], and ΣW becomes ΣB₂∨B₂. Using (12), its four component mapping groups are respectively π_(−2)R₁, π_(−1)R₁, π_(−3)R₁, π_(−2)R₁. The first, third and fourth vanish by the low-stem fact. The second need not vanish, but its particular map is L_J applied to the zero map (5). Thus **the whole actual L_Jd is null**, not merely zero on homotopy groups. Choose a nullhomotopy; it splits L_JF₄ under L_JW. Since V is J-acyclic, a induces L_JF₄≃L_JX, proving (9).

For an E(2)-local S-module Z, the cofiber of Z→L_JZ is E(2)-local and J-acyclic, hence rational, by the positive-height fracture argument in H. Smashing with a rationally acyclic finite spectrum annihilates that cofiber. Apply this observation to X,A₂,A₁ and the corresponding terms of (9). Finite spectra are dualizable in ordinary spectra: tensoring with a finite spectrum preserves local objects and localization maps, so L_K(3)(S∧M)≃T∧M and E(i)-localization commutes with this smash. Also S∧M≃M for such M: the p-local completion cofiber is rational. This gives (11).

For Moore spectra S⁰/pʳ the same argument uses the entire natural diagram of quotient maps. Tensor (9) with that diagram, not a separately chosen splitting at each r. All comparison equivalences are natural; hence the equivalences (10) commute coherently with transitions. No commutative algebra structure on a Moore spectrum is used. ∎

This supplies a spectral construction, but its complete proof is a reduction to accepted local bases plus two low height-one groups. It is **technical**, not a proposed ninth finding. It does not address p=3 or finite type-zero inputs.

### Technical criterion: the choice-independent missing map

For the actual X let u_J:L₀X→L₀L_JX be induced by localization. R105 is equivalent to

π_(−5)(u_J)=0.                                          (14)

In particular this is independent of the allowed generators and roof choices in H.

**Proof.** For every E(2)-local S-module Z the fiber N_Z of Z→L_JZ is rational by the argument in C. A rational source has zero mapping spectrum into the J-local object L_JZ. Applying Γ to the fiber triangle and using ΓN_Z≃N_Z therefore identifies ΓZ≃N_Z, compatibly with its map to Z. Rationalizing the triangle shows

im(π_dΓZ→π_dL₀Z)=ker(π_dL₀Z→π_dL₀L_JZ)

for every integer d. Here π_dΓZ=[Q[d],Z]_S, so this image is exactly the set of rational classes admitting an actual S-linear rational-source lift. Rationalization of W→F₄→U gives L₀F₄≃Q∨Q[−1]∨Q[−3]∨Q[−4], since its rational boundary has unequal source and target degrees. Consequently π_(−5)L₀X→π_(−5)V is an isomorphism: the adjacent groups of L₀F₄ in degrees −5 and −6 vanish. In the exact mapping sequence of F₄→X→V, the inclusion Q[−5]→V lifts to X if and only if its boundary g₅ is null. Since π_(−5)V=ℚₚ, this lift is equivalent to a nonzero generator of π_(−5)L₀X admitting a rational-source lift: a nonzero scalar discrepancy can be inverted. The kernel identity now proves (14). By B, the other three boundary components already vanish. The canonical condition (14) thus characterizes splitting for every allowed construction, not just one choice. ∎

### Technical proposition D: scalar unit retractions already fail

For every p≥5 and every nonzero c∈ℤₚ, no map of underlying spectra f:X→A₂ satisfies fη=c·id_(A₂), where η:A₂→X is the canonical unit. In particular it has no retraction. This is a **formal technical deduction**, not a substantial nomination or a claim that O itself states weak nonsplitting.

**Proof.** H gives the actual K(2)-equivalence w=(η,ζ):A₂∨A₂[−1]→X. Use it to identify R₂X≃R₂∨R₂[−1]. The rational degree −3 of the second summand is π_(−2)L₀R₂=0 by the accepted rational exterior calculation at height two. Thus the entire rational degree −3 of R₂X lies in the first summand. By O and the exact completion/localization comparison in H, the canonical map u_X:L₀X→L₀R₂X is nonzero in this degree.

If fη=c id, then R₂f on the first summand is c id. Its second summand cannot affect degree −3 after rationalization. Hence L₀R₂f∘u_X is nonzero in degree −3: multiplication by nonzero c is invertible on a nonzero rational vector. Naturality of localization identifies this composite with u_(A₂)∘L₀f. But π_(−3)L₀A₂=π_(−3)Q=0, a contradiction. This argument allows f to be an arbitrary underlying spectrum map. ∎

C and D are compatible: positive-height or finite torsion tests discard the rational gluing responsible for D. They do not license replacing X by a wedge before localization.

## Counterexamples to the two tempting completion steps

### Actual S-module ambiguity, not merely a page count

Fix the actual F₄ and its given map W→F₄. For **every** v∈[Q[−5],ΣF₄]_S, construct

X_v=fib(v)∨Q[−6]∨Q[−8]∨Q[−9].

Its cofiber triangle under F₄ has exactly the required V and boundary (v,0,0,0). Thus each v is realized by an actual E(2)-local S-module, by finite fibers and sums. Applying L_J identifies every X_v with L_JF₄; all finite rationally acyclic inputs give the same result. Rationalization also gives the same graded homotopy: L₀F₄ has degrees 0,−1,−3,−4, so every map Q[−5]→ΣL₀F₄ is zero. Consequently L₀X_v has the eight exterior-list degrees with the same dimensions. These statements follow from exactness and the unequal-degree vanishing over Q, without a numerical experiment.

The triangle splits **under F₄ and over V** exactly when v=0: a split triangle has zero connecting map; conversely a nullhomotopy of the connecting map splits it. Thus the nonzero elements of the genuine two-dimensional mapping group give counterexamples to inferring R105 from *all* the already listed local tests, rational dimensions, or finite coefficient splittings. We do not identify any X_v with the actual overlap except its actual, still undetermined v, and do not claim these arbitrary modules carry compatible E∞ multiplications.

### Multiplicativity in the algebraic shadow does not remove the ambiguity

Let K be any characteristic-zero field. Give exterior generators z,a,b degrees −1,−3,−5. For every λ∈K the assignments

Λ_K(z,a,b) → Λ_K(t,z,d),    z↦z, a↦d, b↦λ tzd,

where |t|=|z|=−1 and |d|=−3, define a graded algebra homomorphism. Indeed the three images are odd, their squares vanish in the exterior algebra, and distinct odd images anticommute; these are exactly the defining relations of the free graded-commutative exterior algebra. The monomial tzd is a nonzero exterior basis vector. Therefore varying λ changes the degree −5 map while keeping the unit, z, a and za fixed. Setting t or d to zero kills this variation. Two copies allow independent λ₁,λ₂. This is an algebraic counterexample to the suggested rank/product inference, **not** a realization of ring spectra or an actual homotopy counterexample to R105.

## Route B: a fifth-degree geometric class and the remaining descent cost

The second route attacks the actual coefficient map, independently of the calculation of Γ. It is developed far enough to identify which reduction can and cannot be used.

In H's `11-rational`, the common modification has projective presentation [ℙ²/P₃] and Drinfeld presentation [Ω²/J₃]. Its projective splitting is constructed at finite coefficients by powers of the equivariant hyperplane class, before taking Rlim and inverting p. The same **already accepted** splitting gives in total degree five

H_b⁵(𝓜)=H_b⁵(P₃) ⊕ H_b³(P₃)(−1) ⊕ H_b¹(P₃)(−2).     (13)

Proof of (13): the accepted finite complex decomposition has the three summands indexed by j=0,1,2 with shift [−2j] and twist (−j). Take its degree-five cohomology after its prescribed limit. This yields exactly (13), without exchanging an infinite sum or a new limit. Arithmetic with infinite-order cyclotomic character acts trivially on the first summand and with distinct nontrivial weights on the other two. Thus the arithmetic-fixed part is the first summand. The Drinfeld bottom-row comparison likewise extends its **weight argument** to (5,0): the only incoming differentials are from (3,1) and (2,2), both of different arithmetic weight. Its finite-resolution and finite-filtration hypotheses are the same all-degree assertions in that source. These are technical consequences of complete lower operations, not a newly invented estimate.

The hoped-for input is a degree-five primitive on the matrix group whose full parabolic restriction is zero. A five-linear alternating matrix expression does vanish on gl₂ simply because dim(gl₂)=4. On block upper-triangular matrices its trace is the sum of diagonal-block traces, so the corresponding alternating degree-five trace expression vanishes also on gl₂⊕gl₁. This is an exact linear-algebra calculation: an alternating 5-form on a 4-space is zero, on a 1-space is zero, and products of block upper-triangular matrices have diagonal blocks the products of their diagonal blocks. **This observation is not asserted to be a construction of a nonzero group-cohomology primitive with every needed normalization.** Nonzero evaluation of a cocycle would not prove its nontriviality in cohomology either.

Even granting the primitive identification, one must transport the zero through the **actual two** lower-localization constructions:

- At height one, the required map is the unframed ordinary, bounded-pole finite-Witt coefficient map with its semilinear first coface, then its derived inverse limit. H's degree-three proof uses an actual unique edge in that stem, equality of finite orders under the ghost maps, and a multiplier chosen independently of Witt length. For a vanishing claim in stem −5, one must produce compatible primitives or a single uniform annihilator in this different stem, and identify the limiting map with α₅ under localization. “Zero after each rationalization” is not that statement.
- At height two, O constructs g:T→𝒟 through a **completed** K(2)-local detector. A vanishing calculation in 𝒟 would imply vanishing in L_K(2)T only after proving injectivity of the induced detector on the relevant rational image in degree −5. The direction used in O for degree −3 nonvanishing does not provide this converse. Its completed coefficients and H's ordinary coefficient union must not be silently identified.

The stronger generic companion G was checked specifically here. Its Proposition `prop:modification-transport` compares stable sphere cochains and gives exact block restriction on the independent extension locus **after fixing the connected quotient frame**. Forgetting the lower frame is precisely where the lower norm/cohomology factor can reappear. The displayed algebraic family above demonstrates the elementary reason that lower primitives and their products do not determine its fifth-degree component. The all-degree finite coefficient transport is valuable, but a full equivariant unframed reduction to the two actual maps has not been supplied in this report. If such a reduction follows completely from accepted operations, the resulting R105 should be classified technical; absence of a printed corollary is not substantiality evidence.

The fracture computation and (14) make the obligation finite, exact, and choice-independent. R105 is equivalent to the vanishing of the single map g₅∈[Q[−5],ΣF₄]_S, a vector space of dimension two. A choice of basis is not needed to state the gap. A proof via canonical comparison must identify its class using H's same b,a,t and the signed roof in `02-fracture`; an arbitrary map between the same local corners is insufficient. The source's rescaling of α₃ by a nonzero rational scalar is allowed, but it supplies no valuation or integral normalization of a new degree-five class. Nothing here replaces nullhomotopy by vanishing of a module constituent.

## Significance and disposition

The deepest paid bridge is (6)–(11): an actual three-summand rational splitting and one residual two-dimensional attachment, together with a single compatible positive-height/finite-input splitting. Proposition D is a short canonical-map deduction. Every positive new statement in this report is **author-level technical** with the full proof above; none is independently audited or certified by the verifier.

The selected all-prime p≥5 rational-tail target is neither proved nor refuted. The explicit X_v family refutes only the proposed *method* of reading its value from local tests and ranks. The geometric route retains the exact unframed coefficient/limit and detector-injectivity obligations. No exponent is inferred from a rank count. No result for p=3, arbitrary finite groups, arbitrary dualizable objects, or telescopic localizations is claimed.

There is no forced nomination, no claim of worldwide priority, human review, or formal certification. A parent continuation should first test whether the all-degree stable transport of G already pays the exact two map comparisons; only then should it invest in a purported new fifth-degree mechanism or a multiplicative refinement.

## Evidence and reproduction

Pre-seal validation passed with 10,373 original identities, 776 inherited PDF-text hashes, 1,823 homotopy-search matching lines, 2,993 bridge-search matching lines, and 30 reading passages. No verifier failure occurred before sealing; retrieval/display failures remain in `events.json`. This is not mathematical certification.

Run from the repository root:

`python -B frontier/experiments/i105_chromatic_homotopy_discovery/verify.py`

The final verifier is offline and read-only. It checks the exact owned inventory, SHA-256 and Git-blob identities against the complete tree, all 10,373 original positions and 776 inherited PDF-text hashes, exact lexical occurrence multisets, frozen reading passages with explicit line conventions, and independent finite degree/exterior-algebra diagnostics. It compares only the four authorized live ledgers as driftable. It does not download, write, emit bytecode, repair, or reseal. Originals are referenced immutably by hash; the corpus is not recursively copied.

Current literature: BSSW, *On the rationalization of the K(n)-local sphere*, [arXiv:2402.00960v2](https://arxiv.org/abs/2402.00960v2), revised 9 September 2025, was checked at the official version page and downloaded from the versioned primary URL. Its full relevant theorem/splitting discussion and the bounded spectral-sequence deduction were inspected; no independent audit of its geometry is claimed. Weinstein's current author page links the BMR coheight-one preprint; browser retrieval timed out and the direct author-PDF request failed certificate verification. Those failures are retained. Its pinned citation is the author manuscript dated 26 August 2026, 116 pages. No current theorem version was inferred from a title or search snippet. The pinned BMR-dependent operations used above are accepted as part of the stipulated source, not replaced by an inaccessible current draft.

Only one newly downloaded PDF was text-extracted (BSSW v2); the verifier re-extracts it to stdout in memory for an exact hash replay. No corpus-wide PDF re-extraction is performed. The corpus search uses UTF-8 decoding with replacement followed by Python `splitlines()`; source passages additionally retain LF-only positions/counts. These conventions differ in PDF text containing form feeds and are never conflated. Initial truncated terminal displays, the initial wrong-cwd read failure, and retrieval failures are recorded in `events.json`; proof passages used above were subsequently read in bounded slices or complete short files. Verification validates evidence identity and finite algebra, not the universal spectral proofs or the contribution classification.
