# Arithmetic/algebraic discovery r79

This is a prefreeze research archive, with no target frozen and no nominee. It assigns no contribution rating, mathematical gate, acceptance, or count. All statements and operative proof operations in the pinned OpenAI manuscripts are stipulated true. The pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

The sustained work concerned three distinct mechanisms: twisted and algebraic Bass traces (207), quantization from a singular free-tangent surface (048), and the passage from diskwise to several-parameter topological triviality (064). The last route has an actual r15 antecedent found late in screening, before any freeze. The record below distinguishes calculations made during feasibility from theorem nominations. No weaker replacement is offered for the remaining algebraic trace gap.

## Screening and history

The complete preprint tree was parsed, including all 13,223 entries and `truncated=false`. Its SHA256 is recorded with the selected Git blobs. The truncated root tree was not used. Four content scans searched actual campaign, iteration, experiment, review and finding bodies without a file-size cutoff. They were not title-only searches. Private/source/dependency directories were generally excluded from authored-history searches; the final focused scan accidentally also included some virtual-environment dependency bodies, recorded as noise. Its 18,395-file count is not a count of mathematical papers read. An earlier overly broad `King` pattern also matched “working”; the final scan corrected this with word boundaries.

The first pass covered 194, 204, 199, 044, 053, 065, 168 and 207, followed by 048, 049, 052 and 064. These were not equally studied. For 194/204/199 the present work was history navigation, not new primary proof research. Actual authored comparison bodies were read for r11's 053 ideal-gluing/arity and 065 reverse-Virasoro routes, r24's 044 Hikita route, structural r111's 168 parabolic Kazhdan–Lusztig route, arithmetic r5's 048/049 routes, r14's 064 route, and r16's 052 discussion. Their existing mechanisms were exclusions, not nominations. The 052 source introduction and consequences were inspected; its companion product implication is explicit. No new many-summand theorem was pursued.

The actual r78 research and its reading limits were read. In particular, no new version of the 055 étale numerical-support descent, 206 fixed-Q symmetric-group realization compiler, 210 modular Chow obstruction, or 057 root descent is proposed. The user-specified exclusions and R023–R040 scopes were retained. This archive does not reopen the recent 253 transfer calculation or the other dispatched analytic/structural families.

The late 064 correction is material: the initial history pass led to r14's unresolved primary access, while the final focused scan also found r15's complete King reduction. The entire r15 checkpoint was then read. It is stronger and simpler than the additional Hardt/curve-selection route explored here. Nothing was frozen before or after that discovery; no frozen bytes were replaced. Both the initial search limitation and its correction remain in this archive.

## 207: unitary cocycles preserve the source trace operations

The operative ℓ¹ manuscript is *The ℓ¹ Bass Conjecture for Discrete Groups*, October 5, 2026. `thm:main` asserts finite support on torsion conjugacy classes for the ℓ¹ Hattori–Stallings trace. The algebraic companion, *The Bass trace conjecture for complex group rings*, September 24, 2026, `thm:bass` and `cor:torsion-free`, already gives the complex group-ring support theorem, integer trace rank and characteristic-zero scalar-idempotent consequences. Those are not fresh targets.

The actual ℓ¹ reduction is stronger than its headline: `red:reduction` replaces a matrix idempotent by a similar idempotent in a finitely generated subgroup algebra with an exponential word-length moment. Its square-root correction is a convergent power series in the idempotency defect. `cy:weights-lemma` and `cy:trace-identity` then use cyclic tuple weights, deletion of a vertex via idempotency, cyclic rotation, absolute convergence and a compatible connection. The curvature bound `pf:bound` is for every tuple separately and is independent of its trace weight. Proposition `co:connection` supplies the geometric family used by the weighted identity. Its geometry is not constructed from the coefficients of the idempotent.

Here is the feasibility calculation for a normalized unitary 2-cocycle σ on an arbitrary discrete group G. Write

    u_x u_y = σ(x,y) u_xy,      A = ℓ¹(G,σ).

For g with σ(g,h)=σ(h,g) for every h in C_G(g), there is a bounded conjugacy-class trace t_g on A, normalized by t_g(u_g)=1 and zero away from [g]. To construct it, transport the value 1 by conjugation with the invertible u_h. Independence of the transporter is exactly the displayed centralizer condition. Invariance under conjugation by every u_h implies the trace identity first on basis elements and then on A by absolute convergence. Its coefficient values on [g] have modulus one. A nonregular class cannot carry a nonzero trace of this form.

For a cyclic tuple with h_(i+k+1)=g h_i and w_i=h_i^(-1)h_(i+1), replace the source weight by

    v_σ(h_0,...,h_k)
      = t_g(tr((p(w_0)u_w0) ... (p(w_k)u_wk))).

Left multiplication of all h_i by an element of C_G(g) leaves every w_i unchanged. Cyclic rotation uses the trace property, including the matrix trace. Deleting a vertex sums exactly the twisted convolution p *_σ p = p. The sum of the weights is t_g(tr(p^(k+1)))=t_g(tr p), just as in the source. Finally,

    |v_σ| ≤ product_i ||p(w_i)||,

so all polynomial moments and the exponential reduction retain their original estimates. The square-root correction and similarity calculation work in the twisted Banach algebra because the weighted norm is submultiplicative and every cocycle factor has modulus one.

Consequently the precise source interface has the same inputs, including its joint-in-dimension compatible connection, not just its final vanishing assertion. Its terminal estimate is

    |t_g(tr p)| ≤ C_R M_p (Q_R M_p)^n,
    Q_R = C S^(3/2) R^(-1/10),   S = O(1+log R).

One fixes R sufficiently large depending on p so that Q_R M_p<1, and then lets the even dimension n tend to infinity. Constants have the same dependence as in the source; no uniform bound over p, G or σ is asserted. This kills infinite-order classes and torsion classes whose conjugacy classes avoid the fixed finite word ball. Only finitely many classes meet that ball. There is no remaining phase-dependent geometric estimate in this comparison.

The primary [Chakraborty–Yamashita v1](https://arxiv.org/pdf/1709.03337v1), §2, Lemma 2.1 and Proposition 2.2, was read for the actual conjugacy-phase trace construction. That paper's local deformation setting is more specific; it is not cited as an arbitrary-cocycle Bass theorem. Finite-valued cocycles also admit the familiar finite central-extension/character-idempotent reduction. Arbitrary unitary cocycles were tested directly against the stronger weighted source operations above, without pretending that an infinite central circle has an ℓ¹ character idempotent.

This screen offers no nominee: the apparent new compatibility is the preservation of the already supplied trace identities and absolute-value estimates. It is not rejected merely because its pieces can be named separately, nor declared a worldwide verbatim duplicate. No C*-completion conclusion follows without a separate K-theory lifting interface.

## 207: algebraic HH₀ is a genuinely different, unresolved interface

A second feasibility question keeps the algebraic universal trace rather than its continuous class-sum image. Let

    T : K₀(ℓ¹G) → ℓ¹G / [ℓ¹G,ℓ¹G]_alg,

where the denominator means finite complex linear combinations of commutators, without closure. Can T([e]) always be represented by a finite linear combination of finite-order group elements? This was not frozen as a target. No complete general argument was obtained.

This distinction is explicit in [Berrick–Chatterji–Mislin's author manuscript](https://people.math.ethz.ch/~mislin/pspdffiles/BassCj03225.pdf), §2: the algebraic universal trace T is followed by a map p to ℓ¹ of conjugacy classes, and HS¹=p∘T. The source controls HS¹. The complex group-ring companion does not remove the distinction because its elements have finite support.

For clarity, class-sum zero is exactly the norm closure of the commutator span. One inclusion follows from continuity of class sums. For the other, approximate f by a finitely supported a and subtract from a its class sums at one representative of each class met by a. The resulting b is a finite sum of differences of conjugate basis elements, hence of commutators. Since the class-sum map is a contraction and p(f)=0,

    ||f-b||₁ ≤ ||f-a||₁ + ||p(a)||₁ ≤ 2||f-a||₁.

This proves density, not membership in the algebraic span.

The strongest supplied reduction was tried before declaring a gap: replace e by the source's similar exponential-moment idempotent p in a finitely generated Γ. Similarity preserves the algebraic trace class (the trace of a matrix commutator is a finite sum of entrywise commutators). Subtract the finite torsion representatives furnished by HS¹; the scalar remainder f still has an exponential word-length moment and zero class sums.

There is an explicit sufficient finite-generator mechanism. Choose one representative r_C per conjugacy class and, for each h, a word w_h with h=w_h r_C w_h^(-1). If

    sum_h |f(h)| length(w_h) < ∞,

then telescope each u_h−u_rC along the letters of w_h. Group the resulting edges by the finitely many generators s. Absolute convergence gives b_s in ℓ¹Γ with total norm at most the displayed sum, and

    f = sum_s (u_s b_s u_s^(-1) − b_s)
      = sum_s [u_s, b_s u_s^(-1)].

All regroupings are justified by that summability bound. The representative terms cancel because every class sum is zero. This would give a finite commutator decomposition.

The missing step is a suitable conjugation-flow summability estimate for the actual idempotent remainder, or another finite-commutator construction. The source controls coefficient decay in |h|. It does not supply a bound on the required conjugator lengths in terms of |h| for an arbitrary finitely generated group. Its scalar Pfaffian cancellation does not directly produce a summable flow on conjugacy orbits. No assertion is made that the absence of this particular estimate disproves the desired algebraic trace statement.

A small model clarifies the error in replacing a closed range by a range. On the integer line let μ(0)=−1, μ(k)=1/(k(k+1)) for k≥1, and μ(k)=0 for k<0. Then μ is summable and has total mass zero. A summable solution of b(k−1)−b(k)=μ(k) would have b(k)=0 for k<0 and b(k)=1/(k+1) for k≥0, which is not summable. Thus a zero-total-mass ℓ¹ input need not have an ℓ¹ edge primitive. This is only a model obstruction to an unjustified range argument. It is neither a group-idempotent counterexample nor a result offered for acceptance. The full algebraic trace question remains unresolved in this round.

## 048: a global noncommuting frame already fits ringed-space Fedosov

Source *A singular normal affine surface with free tangent sheaf*, `thm:main` and `prop:algebraization`, supplies a finitely generated normal integral complex algebra A of dimension two with Der_C(A) free of rank two and with a singular marked point, smooth elsewhere. The equation-and-relation algebraization and global affine shrinking are source operations. No replacement by a smooth locus or formal neighborhood is needed. Arithmetic r5 already treats the different Nakai/differential-operator consequence via Rego's existing implication; it is not reused as a nomination.

Choose a global basis δ₁,δ₂ of L=Der_C(A), and write

    [δ₁,δ₂] = a δ₁ + b δ₂,       a,b in A.

The Lie–Rinehart two-form ω with ω(δ₁,δ₂)=1 is nondegenerate, and d_Lω=0 because Λ³L*=0. The bivector δ₁∧δ₂ gives a Poisson bracket on A: its Schouten self-bracket is zero since its expression lies in Λ³L. This says nothing about freeness of the Kähler differential module at the singular point.

The following feasibility calculation supplies the actual connection input, without assuming the frame commutes:

    ∇₁δ₁ = 0,          ∇₁δ₂ = a δ₁,
    ∇₂δ₁ = −b δ₂,      ∇₂δ₂ = 0.

Extend A-linearly in the first entry and by the anchor Leibniz rule in the second. Its torsion on (δ₁,δ₂) is aδ₁+bδ₂−[δ₁,δ₂]=0. Both connection matrices have trace zero, so they preserve ω. In this basis the curvature matrix is

    R₁₂ = [ −ab              −δ₂(a)−a² ]
          [ −δ₁(b)+b²         ab        ].

It is not assumed to vanish. The arithmetic of this formula uses ∇_[δ₁,δ₂]=a∇₁+b∇₂; dropping that term would silently impose a commuting frame.

The closest operative primary is [Vaisman, math/0106070v1](https://arxiv.org/pdf/math/0106070v1), *Fedosov Quantization on Symplectic Ringed Spaces*. Its HRL-ringed-space framework uses a locally free Lie–Rinehart object over the structure algebra, not a smooth ambient manifold or a requirement that ordinary df span L*. Theorem 2.1, its flat-section recursion (2.35)–(2.44), and product (2.53) supply the full construction once a global symplectic connection exists. Its earlier formulas (1.29)–(1.31) also give the usual torsion/symplectic adjustment.

Theorem 2.1 also assumes that the coefficient sheaf is a subsheaf of continuous complex-valued functions. For this application use the analytic topology on X(C) and the sheaf of functions locally given by algebraic regular functions, with its derivation sheaf generated by the global δ₁,δ₂. Regular functions embed into continuous functions; equality on an analytic open subset determines the regular germ because X is reduced. Thus the additional coefficient-sheaf hypothesis is satisfied. The global recursion starts with elements of A and, using the displayed global frame and connection, puts every recursive coefficient back in A. It does not require identifying all sections of an enlarged analytic function sheaf with A. At fixed formal degree only finitely many operations and divisions by positive integers occur. The resulting formal product on A[[h]] has differential coefficients built from the δ_i, and its first antisymmetric term is the displayed Poisson bracket, subject to the primary's h/sign normalization. No analytic convergence or smoothness of Spec A is asserted. Curvature is handled by the primary recursion itself; it is not an unpaid cancellation to be solved anew.

This is not offered as a nominee. The exact category of the existing theorem already accepts the singular ring and the noncommuting frame. The extra connection calculation checks a hypothesis of that theorem. The source's non-klt behavior and Jörder's commuting-vector-field restriction were inspected as safeguards against claiming a smoothness contradiction, but no extension of differential forms or new singularity classification was obtained.

## 064: r15 already pays the several-parameter passage

The exploratory scope was the full holomorphic family over a neighborhood of 0 in C^m, every finite m, with isolated critical point at the origin and constant Milnor number, asking for a parameter-preserving ambient right trivialization with jointly continuous inverse. This was not frozen in r79. Source `thm:main` supplies the full disk theorem. Its §16 appendix supplies controlled ambient gradient transport when suitable complete zero-fiber lifts exist; it does not, by itself, select such lifts over an arbitrary base.

The actual [King 1980 article](https://link.springer.com/content/pdf/10.1007/BF01391660.pdf), *Topological Type in Families of Germs*, Invent. Math. 62, 1–13, was successfully acquired and read through both operative proofs (§§3–4). Theorem 1 needs a continuous family of zero-set equivalences, not merely pointwise equality of types. Theorem 2 uses comparison cobordisms, independent up to invertible attachments, and equates their invertibility with a jointly continuous family of right equivalences. Theorem 1's proof produces an open embedding of the parameter product. Its complex Corollary 3 cannot simply be cited here because it excludes complex source dimension three.

The strongest existing comparison is the actual **arithmetic r15 checkpoint, §1**, not r14's earlier access limitation. Its argument uses the disk theorem near every point of each fixed radial segment, finitely glues those local trivializations along the segment, and invokes King's necessity and choice-independence to show that the simultaneous comparison cobordism at that endpoint is invertible. This is done for each endpoint, without choosing segment charts continuously in the direction. King's sufficiency then supplies joint dependence once over the whole parameter ball. The proof keeps arbitrary m, the original base, and jointly continuous inverses. It needs no general-base simultaneous resolution.

Before finding r15, an additional finite-type route was explored: choose a fixed outer link and allow every sufficiently small inner Milnor radius, regard the annular cobordisms with both boundary components marked as a bounded subanalytic family, use finite compatible triviality to make the bad invertibility locus a union of finitely many pieces, select a real analytic arc approaching a hypothetical bad parameter at zero, complexify the arc, and apply the disk theorem plus King's necessity to contradict badness. The ingredients read were Coste's Theorem 5.22 with its full proof in the author-uploaded web representation, and Bierstone–Milman's complement/rectilinearization proofs. This exploratory route was not developed into a nominated theorem: r15's radial-segment argument already handles the required compatibility more directly. No absence-of-title inference or new general-base resolution claim is made.

## Disposition

No fresh eligible full candidate emerged from these sustained comparisons. The 207 algebraic universal-trace question retains the exact finite-commutator gap above. The twisted trace and singular quantization calculations test compatible existing operations, and 064 has a concrete prior campaign reduction. There is no target freeze, no weakened substitute, no manuscript or formalization, and no request for a count or gate. Integrity checks below authenticate evidence bytes only.
