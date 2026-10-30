# S182P independent full correctness review, round 1

**Verdict: PASS at the entire unchanged frozen scope, relative to the stipulated truth of Source322 and all of its operative upstream proofs.** No necessary author correction or essential uncompleted correctness verification remains. This verdict concerns the submitted proof, not a substitute or silently repaired proof. It assigns no contribution verdict, acceptance, campaign count, or downstream authorization. Parent alone integrates and adopts grades.

Reviewer provenance: authorized Codex / GPT-6 Astra / high / default service tier. This is the first independent correctness round; no other review was read. The supplied campaign context is 19/20, latestR041.

## 1. Object and quantifiers reviewed

The exact author statement is `fresh-structural-discovery-r182/FROZEN-THEOREM.md`, SHA256 `62b6ad633a662a491be617e82f8eb441be8f02069a7dc5289c10996dc8d9bee8`, 1,557 bytes, mode 0644. The exact author proof is `notes/03-author-proof.md` in that root, SHA256 `9f2989669c20bea00260a77dd11a4a4fcb1e7cb0d84f75f8777871ae85d1d38e`, 17,401 bytes, mode 0644. Neither was changed.

The hypothesis quantifies over arbitrary nonzero real Banach spaces X,Y, every surjective f:S_X→S_Y, and **every** unit pair x,y, requiring

    {||f(x)+f(y)||, ||f(x)-f(y)||} = {||x+y||, ||x-y||}.

There is no continuity assumption on f, no dimensional bound, and no separability, reflexivity, smoothness or strict-convexity condition. The conclusion reviewed is f=εT on the whole sphere, with T an onto real-linear isometry and ε an even sign function; the pair is unique up to simultaneous global sign and is uniquely normalized by T(x_*)=f(x_*) for **any prescribed** x_*∈S_X. The converse quantifies over **every** onto real-linear isometry T and **every** even sign function ε, without regularity. All these assertions pass. No min-only, approximate, nonsurjective, complex-linear or family conclusion is included.

I read all four author notes, the exact statement/proof, author FINAL/REPORT, and the two exact parent inputs. The parent questions were treated as checks, not as pre-adopted objections. The following reconstructs the author argument in its actual order and supplies the detailed verification of its compressed elementary transitions, not a new proof in place of a missing one.

## 2. Oddness, bijectivity and quotient metric (author §1)

Fix x. Onto-ness supplies y with f(y)=−f(x). Both images have norm one, so the unordered identity gives {||x+y||,||x−y||}={0,2}. One norm vanishes; thus y=±x. The choice y=x would force a unit vector to equal its negative, impossible over R. Therefore y=−x and f(−x)=−f(x). If f(x)=f(y), the same identity gives y=±x; oddness rules out the negative choice. Thus f is a bijection. This does not infer oddness from a norm-distance of 2, an inference that would fail on flat faces. It uses the zero norm and surjectivity.

For antipodal classes define d([x],[y])=min(||x−y||,||x+y||). It is independent of both choices of representatives; d=0 iff the classes agree. Choose s,t∈{±1} attaining the minima for (x,y) and (y,z). Then

    d([x],[z]) ≤ ||x−stz|| ≤ ||x−sy||+||s(y−tz)||
                = d([x],[y])+d([y],[z]).

Hence this really is a metric, not merely a pseudometric on the quotient. Oddness makes Fbar([x])=[f(x)] well-defined, and the two proved bijections on antipodal pairs give its bijectivity. The full unordered identity preserves the minimum, so Fbar is a metric isometry and therefore a homeomorphism.

For 0<r<1, q^−1(B([x],r)) is exactly B(x,r)∪B(−x,r). If one point belonged to both balls, the triangle inequality would give 2<2r. Each orbit has exactly one representative in each of these balls. Moreover q(B(v,r))=B([v],r): choose the representative closest to v. This proves q is open, while d(q(u),q(v))≤||u−v|| proves continuity. Thus each restricted sheet is a homeomorphism onto the open quotient ball. The metric topology equals the quotient topology, and q is an actual two-sheeted covering. No claim that a sheet is an isometry is needed or made.

## 3. Topological prerequisites without separability (author §2)

For dim E≥2, nonantipodal vectors are joined on S_E by normalizing their straight segment. Its denominator cannot vanish: two unit endpoints causing zero in the segment would be antipodal. Antipodal vectors can be joined through an independent unit vector. This proves path connectedness.

At x, a bounded real functional φ with φ(x)=1 exists by Hahn–Banach. On H={u∈S_E:φ(u)>0}, the maps

    u ↦ u/φ(u),       v ↦ v/||v||  (φ(v)=1)

are continuous mutual inverses. In particular, φ(v/||v||)=1/||v||>0; no points are lost. The affine hyperplane has a base of convex open neighborhoods. Their images prove local path connectedness at x. This remains valid for nonseparable and infinite-dimensional normed spaces.

For dim E≥3, take an arbitrary continuous loop γ:[0,1]→S_E. Uniform continuity gives the author's finite subdivision and polygon p with ||p−γ||<1/8 throughout. Thus ||p||>7/8. For β=p/||p||,

    ||β−γ|| ≤ ||β−p||+||p−γ||
             = |1−||p||||+||p−γ|| < 1/4.

Consequently normalized interpolation between γ and β avoids zero; a zero would require unit endpoints β(t)=−γ(t), contradicting their distance <1/4. The partition starts and ends at γ's basepoint, so this first homotopy fixes it.

The image of β lies in the finite union of subspaces E_i spanned by adjacent vertices, each of dimension at most 2. Adjoin enough vectors to their finite-dimensional span to obtain W⊂E with dim W≥3. Each E_i is proper in W. As in the author proof, a product of nonzero real linear forms vanishing on these E_i is a nonzero polynomial and cannot vanish everywhere on W. A unit z outside their union exists. Normalized interpolation from β(t) to z then avoids zero: at an interior zero, z would be a scalar multiple of β(t), hence would lie in some E_i.

This is a continuous contraction as a free loop. Together with the first homotopy it extends γ over a disk: the terminal constant loop collapses the top circle of the cylinder to a point. A loop bounding a disk represents the trivial based fundamental-group element, even though the second homotopy moves the basepoint. Thus S_E is simply connected. The proof uses only one compact parameter interval and finitely many vectors at a time; it does not assert compactness of S_E, a countable dense subset of E, or a global separable reduction. Completeness is unnecessary at this stage.

The actual Hatcher lifting criterion requires the domain to be path connected and locally path connected, and the induced π1 image to be contained in the covering subgroup. Those requirements are now verified, with the image trivial when dim E≥3. Reading the actual path/homotopy-lifting and uniqueness proofs confirms that neither countability nor local compactness of the domain is an extra hypothesis. The author's endpoint-of-a-lift construction is precisely that operation.

Finally, a section s:P_E→S_E would partition the connected S_E, for dim E≥2, into disjoint nonempty images s(P_E) and −s(P_E). Each image is open: near a basepoint, continuity puts s into one sheet over a smaller evenly covered open set, where it equals that sheet's inverse. Their union is all of S_E. This contradiction verifies the no-section fact used below.

## 4. The lift in every dimension (author §3)

**Dimension one.** A real normed space has exactly two unit vectors iff it is one-dimensional: two independent vectors would already supply infinitely many unit directions. Bijectivity of f therefore forces both dimensions to be one if either is one. Its odd two-point bijection preserves the only distances, 0 and 2, and the rest of the argument applies.

**Source dimension at least three.** Lift the continuous map Fbar∘q_X to U:S_X→S_Y using §3 above. For each x, q_Y(U(−x))=q_Y(U(x)), so U(−x)=±U(x). The function x↦||U(−x)−U(x)|| is continuous and takes only 0 or 2. Connectedness makes its value constant. Value 0 would give an even U, which factors continuously through q_X as h:P_X→S_Y. Then h∘Fbar^−1 is a section of q_Y, contradicting connectedness of S_Y. Thus U is odd everywhere.

An orbit over any y has a representative mapped to y or −y; oddness supplies a preimage of y. If U(x)=U(x′), quotient injectivity gives x′=±x and oddness rules out −x. So U is bijective. To check the compressed local-homeomorphism step, choose a source sheet O near x, a target sheet V near U(x), and replace O by the open neighborhood O∩U^−1(V). On this smaller O,

    U = (q_Y|V)^−1 ∘ Fbar ∘ (q_X|O).

Its image is open: q_X|O is open, Fbar is open, and the target sheet inverse is open onto the sheet. Each displayed factor is a homeomorphism onto its image. Hence U is a local homeomorphism, and being bijective it has continuous inverse. This validates the author's stated shrinking; it adds no new regularity premise.

**Only the target dimension at least three.** If dim X=2 and dim Y≥3, apply the same argument to Fbar^−1 and invert the resulting odd homeomorphic lift. All hypotheses are symmetric and already checked. There is no need to assume equality of the dimensions, or import a dimension-classification theorem. The construction is a conditional argument from the given f, even if an independent topological invariant would rule out such a mixed-dimensional f.

**Both dimensions two.** Relative to a basis, e_E(θ)=(cosθ a+sinθ b)/||cosθ a+sinθ b|| identifies the normed circle with R/2πZ and its antipodal quotient with R/πZ. The denominator is nonzero and finite-dimensional norm equivalence gives the continuous inverse; the antipodal shift is exactly π. Lift Fbar∘(R→R/πZ) to h:R→R. Since the composite and the target projection are local homeomorphisms, so is h. A continuous injective map of an interval is strictly monotone. Its local orientations agree on overlapping intervals and hence on connected R. On a compact interval a finite chain of such neighborhoods shows h is globally strictly increasing or globally strictly decreasing.

The continuous integer-valued difference (h(θ+π)−h(θ))/π is a constant integer k. Strict monotonicity excludes zero. If |k|≥2, the intermediate value theorem produces a θ∈(0,π) with h(θ)−h(0)=π or −π, contradicting injectivity of Fbar on R/πZ. Thus k=±1. The 2π increment is 2kπ. It follows that U(e_X(θ))=e_Y(h(θ)) is well-defined and odd; monotonicity and the period increment give bijectivity, and compactness of these finite-dimensional circles gives inverse continuity. This verifies the degree-one argument without incorrectly treating S^1 as simply connected.

In all cases q_YU=Fbar q_X, so U(x)=σ(x)f(x) with a unique pointwise σ(x)∈{±1}. From oddness of both maps, σ(−x)=σ(x). Pointwise signs preserve the unordered identity. Consequently U is a continuous, odd, onto phase-isometry. Neither f nor σ is required to be continuous. A global sign change normalizes U(x_*) to f(x_*) for any chosen basepoint.

## 5. Planar inequalities, including flat faces (author §4)

For independent unit a,c, write a unit point b in their positive cone as b=αa+βc with α,β>0. Its ray meets [a,c] at

    p = (αa+βc)/(α+β) = b/(α+β).

Convexity gives 0<||p||≤1, so p lies on [0,b]. Collinearity yields

    ||b−p||+||p||=1,
    ||a−p||+||p−c||=||a−c||.

Group the four summands differently and apply two triangle inequalities:

    1+||a−c||
      = (||b−p||+||a−p||)+(||p||+||p−c||)
      ≥ ||b−a||+||c|| = ||b−a||+1.

This proves ||a−b||≤||a−c||. The possibility ||p||=1, so b=p and ||b−p||=0, causes no division or strictness failure. It explicitly includes flat faces. It is the unit-radius specialization of the actual two-triangle proof in Martini–Swanepoel–Weiss Proposition 31. No equality classification in that paper is being used.

For the plus norm, c=β^−1 b+(α/β)(−a), so c lies in the positive cone between the independent unit endpoints −a and b. The same proved inequality now gives

    ||a+c|| = ||−a−c|| ≤ ||−a−b|| = ||a+b||.

The endpoint cases b=a,c follow from ||a+c||≤2 and equality respectively. Applied to b=z_t=((1−t)a+tc)/||(1−t)a+tc||, this yields simultaneously

    ||a−z_t|| ≤ ||a−c||,       ||a+z_t|| ≥ ||a+c||

for every t∈[0,1]. The planar argument is performed in span{a,c} with its inherited norm and does not constrain the dimension, faces, smoothness or separability of the ambient space.

## 6. Global metric orientation (author §5)

Fix any unit x,y with A=||x−y||<B=||x+y||. If y=x the assertion is immediate; y=−x cannot have this inequality. In every other case x,y are independent, since real linearly dependent unit vectors are exactly ± each other. Along the normalized segment z_t from x to y define

    a(t)=||x−z_t||,   b(t)=||x+z_t||,
    h(t)=||U(x)−U(z_t)||.

All are continuous. The planar inequalities give a(t)≤A<B≤b(t), so b(t)−a(t)≥B−A>0 **uniformly along the entire path**. The full unordered identity, inherited by U, gives h(t)∈{a(t),b(t)}. Thus

    (h(t)−a(t))/(b(t)−a(t))

is continuous with values in {0,1}. Its initial value is 0 since z_0=x. Connectedness forces it to be identically 0, yielding ||U(x)−U(y)||=||x−y|| at t=1. This is a proof for each arbitrary strict pair; it does not extrapolate from a finite test or a dense collection of pairs.

If A>B, replace y by −y. The just-proved case and oddness give ||U(x)+U(y)||=B. Since A and B are distinct, the remaining member of the unordered pair must be A. If A=B, both target norms equal this common number directly. The antipodal and equal endpoints have distances 2 and 0 by oddness. These cases exhaust **every** unit pair. Hence U is an ordinary surjective sphere isometry.

The proof does not rely on a false general principle that local metric isometries are global. It uses global topological lifting followed by a particular planar path with strictly separated branches. Flat portions of either branch are permitted. Preserving only the minimum would not justify h(t)∈{a(t),b(t)}; the frozen full-pair hypothesis supplies precisely the needed statement.

## 7. Source application, evenness, uniqueness and converse (author §6)

I authenticated and read the entire actual `main.tex` (35,253 bytes, Git blob `ab9bd82b388ec4e55a333d05c61c853b7941798b`) and `references.tex` (5,302 bytes, blob `796debae8df956385c1aee3398c3d578fda1cdf5`) at pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The complete nontruncated tree is the path authority. The only operative include is `references.tex`; no other same-family TeX/Bib companion is listed. The statement of `thm:main` requires exactly nonzero real Banach X,Y and an onto ordinary sphere isometry. It expressly has no dimensional, separability, smoothness or strict-convexity restriction.

U now meets this interface on the actual whole spheres. Source322 gives

    T(0)=0,       T(v)=||v|| U(v/||v||), v≠0,

as a surjective real-linear isometry. This invocation occurs after the ordinary endpoint-distance equalities have been proved. In the actual source, those equalities enter the common-support propagation in `prop:alignment` and the last contradiction in `prop:no-defect`; its defect attainment, return map, Darbo and extension arguments are all stipulated true. No audit of upstream truth was performed. There is no application of the source to discontinuous f, no whole-space phase theorem applied to an unverified radial extension, and no need to choose phase signs after an ultrapower enlargement.

Set ε=σ. Because σ²=1, U=σf implies f=εT on S_X. Evenness was proved above. After the global normalization, T(x_*)=U(x_*)=f(x_*), so ε(x_*)=1. Nonzeroness ensures a basepoint can be chosen, and the construction works for each prescribed choice.

For two asserted pairs, T₂(x)=ε₂(x)ε₁(x)T₁(x). The function x↦||T₂(x)−T₁(x)|| is continuous, takes only 0 or 2, and is constant when dim X≥2. Value 0 forces equality on all of S_X; value 2 forces T₂(x)=−T₁(x) at every x because the displayed relation already restricts T₂(x) to ±T₁(x). Real linearity extends that common sign to X. Since T₁(x) is nonzero on the sphere, the corresponding ε₂ is ε₁ or −ε₁ everywhere. In dimension one, the value at one unit generator determines a real-linear map and the same conclusion follows. At a prescribed basepoint, the negative possibility would force a unit vector to equal its negative, so exactly one normalized pair remains. There is no regularity assumption on either ε_i in this reasoning.

Conversely let **any** onto real-linear isometry T and **any** even ε be given. For every unit pair, factoring out ε(x) shows that ε(x)ε(y)=1 keeps the two source norms in order and −1 swaps them. Thus the full identity holds. Given y∈S_Y, take x=T^−1y∈S_X. If ε(x)=1 then f(x)=y; otherwise ε(−x)=−1 and f(−x)=(−1)T(−x)=y. This proves onto-ness for completely arbitrary even signs. No measurability, continuity or finite-dimensional restriction enters. The simultaneous replacement (T,ε)↦(−T,−ε) also preserves the formula and evenness, so the asserted ambiguity really exists and is exactly the one proved.

## 8. Actual-primary comparisons and remaining limits

These comparisons check applicability and hidden dependencies, not contribution or priority. The actual whole-space proof, Ilišević–Omladič–Turnšek arXiv:2005.02949v2, was read in full. Its signed midpoint-set iteration (Propositions 3.2–3.5), homogeneity (3.7), two-plane propagation (3.9–3.10), and projective/orthogonality final step (4.2) operate on all vectors, midpoints and unequal radii. Sphere input alone does not authorize those operations. The author does not use that theorem as a black box at the missing interface.

The actual Tan–Gao arXiv:2008.09282v2 was read in full. Lemma 2 gives the elementary oddness/injectivity operation reconstructed here. Its C(K) facial correspondence, functional reconstruction and sign consistency are specific comparisons; none is assumed for arbitrary X in the submitted proof. Likewise, the actual Enami–Matsuzaki arXiv:2603.00583v1 was read in full, including even face adjustments (3.2–3.3), continuity on signed faces (3.4), sign consistency on all overlaps (3.5–3.7), gluing (3.8–3.9), exact interpolation (4.1), and the final weighted-composition proof. Its three-point signed-intersection witnesses use C0 function-space structure. S182P has its own global covering lift and therefore assumes none of those facial witnesses. I assign no independent truth verdict to these comparator papers or their criticisms of other papers.

The operative classical proof passages were independently read: the supplied unit-radius specialization of Martini–Swanepoel–Weiss Proposition 31 was checked algebraically and against the actual rendered pages; Hatcher's covering lifting and uniqueness statements and proofs were read, including the path/homotopy construction in Theorem 1.7 and Propositions 1.30–1.34. The author's own normed-sphere topology verifies their exact domain hypotheses.

The full CL original and the 2022 min-only paper were not read in this review and are not premises of the author proof. The author's CL HTTP 403/406 failures are recorded as **inherited access history**, not my own failed requests or evidence for correctness. No favorable verdict is inferred from unavailable literature. Those limits restrict literature-comparison claims, not any step of the self-contained sign recovery plus stipulated source. There is no essential missing correctness verification from them. No claim is made about full literature coverage, priority, or substantiality.

No project historical theorem is a premise of this proof. I did not conduct a broad historical scan or read forbidden original rounds. Author historical claims remain attributed; the exact admitted author/parent prose is not reclassified as a read of its cited originals. All older frozen scopes and supplied dispositions remain immutable. This review makes no historical-clearance claim.

## 9. Disposition

All hypotheses, dimensions, nonseparable cases, both strict-inequality directions, ties, oddness, onto-ness, uniqueness, arbitrary basepoint normalization and arbitrary-even-sign converse have been verified at full scope against the unchanged author argument. The compactness used in the topology is only for individual loops and finite-dimensional circles; there is no hidden ambient compactness assumption.

**Unresolved correctness objections: none. Necessary author repairs: none. Essential uncompleted correctness verifications: none. Full-scope verdict: PASS**, with Source322 and every operative upstream proof stipulated true exactly as instructed. Artifact hashes, extraction agreement and copied controls are provenance checks and played no role as mathematical gates. Contribution, acceptance, count, formalization, manuscript and release remain outside this review.
