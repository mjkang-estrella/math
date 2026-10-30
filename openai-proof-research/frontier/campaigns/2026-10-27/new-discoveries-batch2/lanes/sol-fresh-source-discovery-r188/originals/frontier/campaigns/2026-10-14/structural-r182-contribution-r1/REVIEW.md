# S182P independent contribution review — round 1

**Verdict: TECHNICAL, conditional on full correctness, at the ENTIRE unchanged frozen scope.** This is a contribution assessment, not a correctness PASS, acceptance, count, priority claim, or permission for downstream work. The condition of full correctness is not discharged by this review. The correctness reviewer was not consulted or read. Parent alone integrates and adopts dispositions.

Provenance: Codex / GPT-6 Astra / high / default service tier. Supplied context is Campaign19/20, latestR041. Source322 and every operative upstream proof at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. Their truth is not audited here.

The frozen statement has SHA256 `62b6ad633a662a491be617e82f8eb441be8f02069a7dc5289c10996dc8d9bee8`; the submitted proof has SHA256 `9f2989669c20bea00260a77dd11a4a4fcb1e7cb0d84f75f8777871ae85d1d38e`. Both original byte strings and modes are preserved. The assessment covers arbitrary nonzero real Banach X,Y, every surjective f:S_X→S_Y preserving the unordered pair of sum/difference norms for every unit pair, no regularity or dimension/separability/convexity/smoothness restrictions, f=εT with T a surjective real-linear isometry and ε even, uniqueness modulo simultaneous global sign, unique normalization at ANY prescribed unit vector, and the converse for EVERY even ε.

**1. The precise contribution payment.**

The conclusion does not follow just by naming the ordinary sphere theorem or the whole-space phase theorem. The latter cannot be applied to an unverified radial extension. Nor is a local sphere isometry automatically a global chord isometry. The full compatible payment is instead:

1. The already used antipodal-quotient metric turns f into a homeomorphism of projective unit spheres.
2. The ordinary lifting criterion for two-sheeted covers, with all its hypotheses verified below, produces a continuous odd representative of that homeomorphism.
3. The unit-radius instance of the classical planar monotonicity lemma makes each strict distance-branch region reachable from its forced orientation by a normalized straight segment. Connectedness prohibits changing the chosen branch.
4. The stipulated ordinary-sphere theorem supplies the radial linear extension. Elementary sign bookkeeping supplies the full uniqueness and converse clauses.

The point of the verdict is that this payment leaves no additional operation requiring new Banach-space structure, a new estimate, an infinite-dimensional gluing principle, or a new source argument. This is a concrete classical composition at the submitted scope; it is not an argument from the short length of the proof, an open-problem label, an absent search hit, or a restricted example. The useful choice to combine covering theory with planar monotonicity may be original to this project; this review does not establish whether that combination has appeared previously in the literature. Project originality and the campaign's substantial-contribution threshold are separate.

**2. Full compatible derivation of the sign recovery.**

Write q_E:S_E→P_E=S_E/{±1}. First f is odd and bijective. For x∈S_X choose y with f(y)=−f(x). The input gives {||x+y||,||x−y||}={0,2}, so y=±x. The choice y=x is impossible because f(x) is unit; hence y=−x and f(−x)=−f(x). If f(x)=f(y), the same zero-norm argument gives y=±x, and oddness excludes the negative alternative. This is exactly the operation in Tan–Gao Lemma2, read in its actual proof.

Define

    d_E([x],[y]) = min(||x−y||, ||x+y||).

Representatives do not matter. For signs s,t attaining the minima for (x,y) and (y,z),

    d_E([x],[z]) ≤ ||x−stz|| ≤ ||x−sy|| + ||y−tz||.

This proves the triangle inequality; positivity and symmetry are immediate. The construction is the unit-sphere restriction of the antipodal quotient metric explicitly used in Huang–Tan's 2022 whole-space min-phase paper, not a new metric construction.

For 0<r<1,

    q_E^{-1}(B([x],r)) = B_S(x,r) ⊔ B_S(−x,r).

The balls are disjoint since their centers have distance2. Each orbit in the inverse image has exactly one representative in each ball. The quotient map is continuous because d_E([u],[v])≤||u−v||. It is open: around every representative in an open set choose a sphere ball and note its projection is the corresponding projective ball. Its restrictions to the two balls are therefore homeomorphisms onto the projective ball. Thus q_E is an actual double covering, with the metric quotient topology. The given f induces a bijective metric isometry F:P_X→P_Y; consequently F is a homeomorphism, even when f is wildly discontinuous.

Here are all the needed topological hypotheses. If dim E≥2, normalized straight segments join nonantipodal unit vectors. Antipodal vectors can be joined in two steps through an independent unit vector, so S_E is path connected. Choose a continuous real linear functional φ with φ(x)=1. On {u∈S_E:φ(u)>0}, the map u↦u/φ(u) is a homeomorphism onto {v:φ(v)=1}, with inverse v↦v/||v||. Open convex neighborhoods in that affine hyperplane prove local path connectedness. These arguments require neither separability nor completeness.

For dim E≥3 every loop γ has a finite polygonal approximation p with ||p(t)−γ(t)||<1/8 throughout. Uniform continuity of this one loop gives the finite partition. Normalize p to β=p/||p||; then ||β−γ||<1/4, and normalized interpolation gives a homotopy of loops from γ to β. All edges of β lie in finitely many at-most-two-dimensional subspaces. In a finite-dimensional space W containing those edges and of dimension at least3, choose a unit z outside their union. Such a z exists because a finite union of proper subspaces cannot cover a real vector space: take a nonzero linear functional vanishing on each subspace and use the nonzero product polynomial. The formula

    ((1−s)β(t)+sz) / ||(1−s)β(t)+sz||

contracts β. Its denominator cannot vanish, since that would put z in an edge subspace. This contraction provides a disk filling, even though its boundary basepoint can move during the contraction. Therefore the based fundamental group is trivial. Nothing replaces the ambient nonseparable space by a globally separable model; only one compact loop is approximated.

Hatcher's actual Proposition1.33 now applies to Fq_X whenever dim X≥3. Its domain is path connected and locally path connected and has trivial π1; hence the subgroup inclusion in the lifting criterion is automatic. Choose the initial lift value arbitrarily in the two-point fiber. Path lifting defines U(x) as the endpoint of the lifted image of any path from the initial point to x. Homotopy lifting makes this independent of the chosen path. On a sufficiently small path-connected neighborhood, the construction is the inverse of one sheet map composed with Fq_X, so U is continuous. This is exactly the primary's operative construction, with no compactness of S_X assumed.

For each x, U(−x)=±U(x). The continuous function ||U(−x)−U(x)|| takes its values in {0,2}; connectedness makes the choice constant. It cannot be constantly0. Otherwise U would descend to P_X, and composing with F^{-1} would give a continuous section s of q_Y. A continuous section of a two-sheeted covering selects locally one open sheet; its image and its antipodal image would be disjoint nonempty open sets whose union is S_Y, contradicting connectedness. Thus U is odd.

The quotient homeomorphism and oddness make U bijective: it gives a bijection of orbits and of the two elements in each orbit. Sheet charts express it locally as q_Y^{-1}Fq_X; hence its inverse is continuous. If dim X=2 and dim Y≥3, apply the same construction to F^{-1} and invert the resulting odd homeomorphism. This handles the mixed-dimensional situation without assuming dimension equality. If either dimension is1, odd bijectivity of f forces both spheres to have exactly two elements; that case is immediate.

If both dimensions are2, fix bases and write e_E(θ)=(cosθ a+sinθ b)/||cosθ a+sinθ b||. The sphere is R/2πZ and its antipodal quotient is R/πZ. Lift the quotient-circle homeomorphism to h:R→R using the covering R→R/πZ. Locally h is a homeomorphism of intervals; it is locally strictly monotone. The increasing/decreasing orientation cannot change on connected R, so h is globally strictly monotone. The continuous function h(θ+π)−h(θ) is an integer multiple kπ, independent of θ. Monotonicity excludes k=0. If |k|≥2, the intermediate value theorem supplies distinct θ moduloπ with the same image moduloπ, contradicting injectivity of F. Thus k=±1. It follows that U(e_X(θ))=e_Y(h(θ)) is a well-defined odd sphere homeomorphism. This explicitly pays the circle monodromy; the circle was never called simply connected.

In all cases, U(x)∈{f(x),−f(x)}. Thus U=σf for an even sign function σ, because both maps are odd. Pointwise signs preserve the unordered pair, so U is still a surjective phase-isometry. Its continuity is acquired from the quotient, not assumed for f or σ.

It remains to pay chord orientation, where topology alone would be insufficient. The following exact inequality is the needed unit-radius case of Martini–Swanepoel–Weiss Proposition31. For independent unit a,c and a unit b in their positive cone, let p=[a,c]∩R_+b. Convexity gives ||p||≤1; hence p∈[0,b]. The two collinear decompositions and two triangle inequalities give

    1+||a−c||
      = ||b−p||+||p||+||a−p||+||p−c||
      ≥ ||b−a||+||c|| = ||b−a||+1.

Therefore ||a−b||≤||a−c||. If b=αa+βc with α,β>0, then c=β^{-1}b+(α/β)(−a); apply the same inequality with base−a and endpoint b to obtain ||a+c||≤||a+b||. Endpoints follow directly. These are weak inequalities and remain valid on flat faces.

Now fix x,y with A=||x−y||<B=||x+y||. Except for y=x, already settled, they are independent. Along

    z(t)=((1−t)x+ty)/||(1−t)x+ty||,

the preceding inequalities imply

    a(t):=||x−z(t)|| ≤ A < B ≤ b(t):=||x+z(t)||.

Set h(t)=||U(x)−U(z(t))||. Since U preserves the FULL unordered pair, h(t)∈{a(t),b(t)}. Thus (h(t)−a(t))/(b(t)−a(t)) is a continuous {0,1}-valued function. It equals0 at t=0, so it equals0 at t=1. Consequently U preserves ||x−y|| for every such pair. If A>B, apply this result to x,−y and use oddness to preserve the sum norm; the full two-value identity then forces the difference norm as well. If A=B the identity immediately gives the desired distance. Antipodal endpoints follow from oddness. Every unit pair is covered.

This last step is the elementary connectedness principle for a continuous choice between separated branches, with an explicit path and gap B−A furnished by the existing planar inequality. It is not an unproved local-to-global assertion. Nor is it a min-only theorem: knowing only the minimum would not place h(t) in the two-element set {a(t),b(t)}.

**3. Source interface and every remaining conclusion.**

U is now an onto ordinary sphere isometry between the original nonzero real Banach spaces. Source322 Theorem thm:main applies exactly, and gives

    T(0)=0,   T(v)=||v||U(v/||v||)  (v≠0)

as a surjective real-linear isometry. Completeness is used here; the preceding bridge needed only real normed spaces. The source's actual proof first bounds and attains a hypothetical cross-radius defect, propagates common supports to a closed convex invariant set, uses its return-map contraction of noncompactness to obtain aligned chords, and excludes the defect by its secant/perturbation and small-parameter contradictions. Those operations require exact ORDINARY sphere distances, supplied above before the source is invoked. No sign selection in its ultrapower construction is being silently assumed. Both actual main.tex and references.tex were read; the only mathematical include is references.tex. Their authenticated blobs match the complete pinned tree. Every one of those upstream operations is paid and stipulated true.

Since U=σf and σ²=1, f=εT with ε=σ even. For any chosen x_*∈S_X choose U's global sign so U(x_*)=f(x_*). This gives ε(x_*)=1 and T(x_*)=f(x_*).

For uniqueness, if f=ε_1T_1=ε_2T_2, then T_2(x)=ε_1(x)ε_2(x)T_1(x) on S_X. The continuous function ||T_2(x)−T_1(x)|| has values0 or2; on connected S_X it is constant. Thus T_2=T_1 on all unit vectors or T_2=−T_1 on all unit vectors, and linearity gives the same equality on X. The corresponding phases must agree or be negatives everywhere. In dimension1 the value of a linear map at a unit vector determines it, giving precisely the same conclusion. The prescribed basepoint eliminates the negative alternative. This proves both full uniqueness assertions without assuming regularity of ε_i.

Conversely, let T be any surjective real-linear isometry and ε ANY even sign function on S_X. Multiplying one argument by−1 swaps sum and difference, so f=εT preserves their unordered pair for every pair. For y∈S_Y take x=T^{-1}y. If ε(x)=1 then f(x)=y; otherwise ε(−x)=−1 and f(−x)=y. Thus f is onto even when ε is discontinuous everywhere it can be. This pays the converse rather than tacitly imposing a continuous phase.

**4. Actual primary comparison and its limits.**

Ilišević–Omladič–Turnšek, [arXiv:2005.02949v2](https://arxiv.org/abs/2005.02949v2), Theorem4.2 and §§2–4, were read completely. Its signed midpoint sets, iterated half-diameter intersections, homogeneity, local midpoint propagation across two-planes, and projective/orthogonality completion are genuine whole-space operations. Their inputs include 0, halves, sums and unequal radii. No step above asserts that sphere data already supply those inputs. That paper therefore pays the whole-space endpoint once available, but is not the missing sphere bridge by restriction.

Huang–Tan, [Results Math.77:152 (2022)](https://doi.org/10.1007/s00025-022-01702-8), was obtained as a publisher PDF and read completely, resolving the author's late navigation-only lead. Its Lemma2.4 recovers signed midpoints under ||x−y||≤(2/3)||y|| using actual whole-space midpoint sets; Proposition2.5 recovers homogeneity; Proposition2.8 propagates two-plane images; Proposition2.10 treats the plane by extreme directions and dyadic midpoint propagation; the main proof uses projective geometry and orthogonality in higher dimension. Its explicit antipodal quotient metric is relevant classical payment. Its theorem, however, still requires a whole-space min-isometry. None of these midpoint or homogeneity conclusions was used circularly for the frozen sphere map.

Tan–Gao, [arXiv:2008.09282v2](https://arxiv.org/abs/2008.09282v2), was read completely. The operative C(K) proof uses separable back-and-forth and maximal stars, a finite-intersection argument for paired faces, norming functionals determined up to signs, and Urysohn functions to align those signs. Its final norming-family formula then yields a whole-space isometry. This is a real sign-gluing mechanism, but the witnesses and norming-coordinate structure have a specific function-space interface. The general argument above does not assume that interface.

Enami–Matsuzaki, [arXiv:2603.00583v1](https://arxiv.org/abs/2603.00583v1), was also read completely. Lemmas3.4–3.7 pay all signed overlaps: continuity of a face-corrected map follows from the preserved sum norm2, opposite signed overlaps are compared using surjectivity, and a triple-face witness from Urysohn makes the transition signs satisfy a common basepoint normalization. Proposition4.1 and the four-step main proof then recover the weighted composition operator. This is stronger evidence than merely its abstract or its criticism of another paper. Its Lemma2.4 cites the CL paper's general paired-face result; that cited proof was not independently available here. The covering/monotonicity derivation above needs neither that lemma nor any triple-face intersection.

The actual 2023 CL proof remains unread. The publisher PDF returned403; an Elsevier XML endpoint returned1825bytes of bibliographic metadata with no mathematical body. Bounded exact-title searches did not supply an accessible author manuscript. Its publisher theorem/introduction state the CL-to-arbitrary-target result. C0 Remark5.2 describes a disputed mixed-sign overlap in the CL construction, but that is the C0 authors' account, not an independently verified defect adopted here. Access failure supplies no evidence for substantiality, correctness, or novelty.

The strongest additional accessible min-only sphere mechanisms were read directly:

- Tan–Yuan–Yang, [Aequationes Math.98 (2024),1475–1487](https://doi.org/10.1007/s00010-024-01119-4): singleton coordinate images, two-coordinate probes, recovery of coordinate magnitudes, disjoint-support sign relations and a fixed coordinate used to force the ordinary distance branch. It is a class-to-class L∞(Γ)-type construction. Its printed main statement omits a surjectivity word while the abstract, lemmas and proof explicitly use surjectivity; this review uses the operative surjective scope. The coordinate probes cannot be imposed on arbitrary Banach spaces.
- Huang–Kang–Wang, [Bull.Aust.Math.Soc.114 (2026),149–159](https://doi.org/10.1017/S0004972726101075): an L1(μ)-to-arbitrary-normed-target theorem. The proof recovers signed combinations of disjoint-support unit functions by norm equalities and integral inequalities on arbitrary measurable subsets, splits the domain into two support bands, aligns coefficient signs, forces distances by adding a common disjoint component, and extends through simple functions. That is a substantially closer arbitrary-target comparator than a sequence-space abstract, but its support-band decomposition and integral tests are absent in general Banach spaces. They are not borrowed as universal operations here.
- Yuan, [Adv.Fixed Point Theory14:15 (2024)](https://doi.org/10.28919/afpt/8523): the full published text was read. Despite the broad abstract, the detailed main proof is for atomic ℓ_p,1<p<2, using disjointness, coordinate magnitudes, strict convexity and a fixed coordinate to orient distances. The narrower actual theorem/proof scope is what is compared; no all-Lp or all-Banach conclusion is inferred from the abstract.

These later min-only papers were read after the retained working reduction, before this final verdict. Their provenance and limits are recorded. Reading a comparator's proof is not an independent correctness certification of every printed line, and none of these specialized results is needed as a premise of the payment in §§2–3.

For the universal bridge, the actual operative primary proofs are [Hatcher's lifting results](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Theorem1.7 and Propositions1.30–1.34, and [Martini–Swanepoel–Weiss](https://arxiv.org/abs/0708.2900v1), §3.5 Proposition31 (with Lemma5 read). The former supplies exactly the continuous lift after the elementary sphere-topology checks. The latter supplies exactly the two monotonicity inequalities after restriction to span{x,y}. The separated-branch argument then requires only connectedness of an interval. The full proof above verifies their compatibility rather than citing their names as a grade.

**5. Original-history comparison and unresolved obligations.**

The eligible original r94 comparison note was read to EOF. Its quantitative sphere ε-isometry program leaves a quantitative face/chord alignment unpaid; S182P makes no estimate for ε-isometries and does not settle that old target. The actual original I88 target and source-contract sections were read exactly through their next equal headings. Intrinsic rank complexity Q88, coupled absorption/AP/no-BAP S88 and binary-diamond D88 are distinct scopes and remain unchanged. I12 was referred to by r94 but its operative body was not admitted/read. No conclusion about I12 beyond that attribution is adopted.

A prospective guarded authored-history search found no operative phase-lifting original. It produced several unrelated lexical matches and an I13 line mentioning an old brief; linked briefs were not opened. This is a limited navigation result, never a novelty certificate. All supplied older dispositions, including S176A's undischarged condition, remain intact. No r181 body or other structural182 review was admitted.

There is **no remaining integration obligation in the contribution payment §§2–3**. The missing CL body is an explicit limit on comparison with that paper's detailed construction, not a premise or an essential missing payment in the TECHNICAL assessment: even a fully successful CL gluing theorem is unnecessary to the independent universal covering/planar/source derivation. Consequently this verdict does not say that the literature comparison is exhaustive or that CL has been cleared. If the desired question were whether the author repaired the exact CL mixed-sign overlap, or whether it has literature priority over every sphere-phase proof, that separate question would remain INCOMPLETE pending the CL body and broader evidence. It is not the basis of the present grade.

The substantive objection to treating this as the remaining campaign contribution is the complete payment exhibited here. Pointing to arbitrary dimension, discontinuous phases, or an open label does not answer it: those quantifiers have already been discharged by the cover, finite-loop and branch arguments above. No repair to the frozen theorem or author proof is requested or made. To challenge this contribution assessment at this unchanged scope, one would need to identify a specific nonroutine operation left unpaid by the displayed derivation, or a material applicability error in it. Independent correctness review remains entirely separate. No restricted-scope result, numerical test, inherited manifest, or artifact verification earns a mathematical gate here.

The reading record also discloses an initial acceptance-file I/O deviation: NEW-TEN was first loaded as bytes in memory before slicing the authorized acceptance interval; only that interval was decoded/displayed or used, and the retained copy was later made by exact seek/read. No out-of-span journal content was semantically read, but perfect byte-access isolation is not claimed.
