# Structural198 independent full correctness review — round 1

**Verdict: PASS at the entire unchanged frozen scope, conditional only on the stipulated Source322 theorem and operative proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.** The source-free auxiliary assertion passes for every pair of nonzero real normed spaces, including incomplete spaces. No essential repair, additional regularity assumption, dimension restriction, or narrowed replacement is required. There is no unresolved correctness obligation identified in this review.

This is an independent adversarial correctness review, not a contribution or acceptance decision. No contribution grade, campaign increment, formal coverage, publication, or priority claim is assigned. Parent questions were checks, not inherited defects. No other review, foreign task body or status was inspected. Authorized provenance: Codex / GPT-6 Astra / xhigh / default service tier.

The exact immutable inputs are the 2,013-byte SCOPE (SHA256 `9b96245518d383432e770924856a44463c118ca68289eb7d85950acf1f872e09`) and 17,317-byte AUTHOR-PROOF (SHA256 `0133cd993a29c07911b198f4553121614363a4f4c5d45c2b67b10b4b60de406d`). Their retained copies are private and byte-for-byte unchanged. This review checks AUTHOR-PROOF sections 2–7 as written; the derivations below explain their existing arguments rather than replace a missing essential step.

## Exact scope and source applicability — question 1

For every surjection f:S_X→S_Y between nonzero real Banach spheres satisfying

    {||f(x)-f(y)||, ||f(x)+f(y)||} = {||x-y||, ||x+y||}

for every pair of unit vectors, the asserted classification f(x)=sigma(x)Ux holds: U is a surjective real-linear isometry and sigma is an arbitrary even sign function. The pair is unique up to simultaneous sign and every such pair works. Set equality permits coincident entries. No continuity or measurability of f or sigma is assumed.

The stronger pre-extension assertion is also reviewed: for arbitrary nonzero real normed X,Y there are exactly two continuous odd bijections h with h(x)∈{f(x),-f(x)}, and both preserve the given norm distance. Completeness enters only when extending h by Source322. The proof does not obtain a complex-linear operator, arbitrary complex phases, an approximate theorem, or a nonsurjective theorem.

I read the complete pinned source main.tex, its sole included references.tex, and wrapper. Its `thm:main` assumes precisely nonzero real Banach spaces and a surjective ordinary sphere isometry. It states the unique surjective real-linear extension with radial formula. The canonical folder has four blobs and the build directory; all four blob identities agree with the complete authenticated tree. There is no additional operative TeX companion hidden behind an unexamined include: the only input is references.tex at the end of main.tex.

The source's internal operations were actually read: finite-dimensional supports and radial contacts; uniform radial defect and inverse defect; ultraproduct attainment followed by completion; common-support propagation into an invariant convex face; scalar-bin refinement of the return-map estimate; Darbo and its noncompactness/compact-fixed-point appendix; the two secant/support parameter regimes and chord contradiction; finally the metric radial extension and midpoint reflection. All are stipulated true and paid, not audited here. None is applied directly to the unordered phase map. AUTHOR-PROOF section 6 supplies an ordinary sphere isometry before section 7 invokes the source once. The normed-space auxiliary claim has no dependence on these source operations.

The inspected Lean scope/comparator is an interface. The comparator's theorem ends in `sorry`; no imports were followed and no Lean proof was compiled or claimed.

## Antipodal bijectivity and quotient metric — question 2

Fix x. Onto-ness gives z with f(z)=-f(x). Applying (P) gives {||x-z||,||x+z||}={0,2}; hence z=±x. The choice z=x would make the unit vector f(x) zero, so z=-x and f is odd. If f(z)=f(x), the same zero-entry argument gives z=±x and oddness excludes -x. Thus f is bijective. This needs no topology of f and remains valid when other pairs have equal entries.

For antipodal classes put d([u],[v])=min(||u-v||,||u+v||). Fix a representative u; choose v'∈{v,-v} realizing d([u],[v]), then w'∈{w,-w} realizing d([v],[w]) relative to v'. Then

    d([u],[w]) ≤ ||u-w'|| ≤ ||u-v'||+||v'-w'||
                 = d([u],[v])+d([v],[w]).

The other metric axioms follow from norm properties and the definition of the equivalence classes. This avoids inconsistent representative choices in the triangle inequality.

For 0<r<1/2, every class at quotient distance <r from [a] has exactly one representative in B_S(a,r). Two representatives there cannot be antipodal, since their mutual distance is <2r whereas antipodal unit vectors have distance 2. If u,v belong to this sphere ball,

    ||u-v||<2r<1,     ||u+v||≥2-||u-a||-||v-a||>2-2r>1.

Thus its projection is an isometry onto B_P([a],r). The inverse image of the latter is precisely the two disjoint balls about a and -a. These are open sheet charts. Projection is continuous since d≤the original distance; it is open because each open sphere neighborhood contains such a small ball. Consequently the displayed metric topology agrees with the quotient topology, and the charts give the asserted double cover.

Oddness makes F([x])=[f(x)] well-defined, and injectivity and surjectivity of f make F bijective. Taking minima in (P) proves that F is a metric isometry. Therefore q=F∘pi_X is continuous although f may be discontinuous. The proof never treats an arbitrary choice of representatives as continuous.

## Path, grid and moving-basepoint lifts — question 3

For a path into P_Y, the inverse images of evenly covered balls form an open cover of the compact interval. A Lebesgue number supplies a finite subdivision with each closed subinterval mapping into one chart. Start in the specified sheet and continue by the existing endpoint. On an overlap endpoint the two definitions agree. Uniqueness follows locally from the disjoint sheets, and globally from connectedness of the interval. Negation commutes with lifting.

For a map of the square, pull back the same chart cover and choose a sufficiently fine finite rectangular grid. Each closed cell maps into one chart. Process cells left-to-right, then row-by-row. The already defined part of a new cell's boundary consists of its left edge, bottom edge, or both. If both, they meet at a previously agreed corner. Select the inverse sheet through that corner. On each full edge its restriction agrees with the existing lift by path uniqueness. Thus there is no overlooked second-edge compatibility condition. Finite pasting gives a continuous square lift.

If H(s,0)=H(s,1), the two lifted endpoints are in the same antipodal fiber. Their distance is continuously either 0 or 2 as s varies, hence constant. In particular a freely nullhomotopic loop lifts closed from either initial sheet. This is exactly what is needed: the constructed contraction can move its base point. No based nullhomotopy is assumed in its place.

The sphere is path connected in dimension at least two: use normalized segments for nonantipodal endpoints and an independent intermediate unit vector for antipodes. It is locally path connected as well. Normalization N(w)=w/||w|| is open onto the sphere: near a chosen w in an open ambient set, rescale nearby sphere points by ||w||. Images of sufficiently small convex balls around a unit point a are open path connected neighborhoods, with ||N(w)-a||≤2||w-a||. These can be made small enough to lie in any prescribed neighborhood. All these facts hold in incomplete spaces.

## Loops in every dimension at least three — question 4

Given a continuous sphere loop alpha, uniform continuity produces a finite polygon p whose vertices are sampled values and with ||p(t)-alpha(t)||<1/8 throughout. The polygon closes because the sampled first and last values agree. Then ||p(t)||>7/8 and beta=N(p) satisfies ||beta-alpha||<1/4. The interpolation (1-s)alpha+s beta cannot vanish, because it is within 1/4 of alpha. Normalization therefore gives a free homotopy from alpha to beta.

Each polygon edge, including its normalized values, lies in E_i=span{alpha(t_i),alpha(t_{i+1})}, of dimension at most two. These are proper subspaces when dim X≥3. A finite union of them cannot fill X. The author's finite-dimensional proof is valid: include a witness outside each E_i in a finite-dimensional V. Every V∩E_i is proper in V, so choose a nonzero linear functional vanishing on it. Their product is a nonzero real polynomial, hence has a point where it does not vanish. This yields a nonzero vector outside all E_i; normalize it to z. No compactness, completeness, countable basis or separability of X is used.

The cone (1-s)beta(t)+sz is nonzero: an interior zero would make z a negative scalar multiple of beta(t), hence a member of its edge plane. At the endpoints it is already unit. Normalizing gives a free contraction to z. Composing with q and using the square-lift result shows that every q-image of a sphere loop has closed lifts.

Fixing x_0 and y_0 above q(x_0), define h(x) by lifting q along any path from x_0 to x. A path followed by the reverse of another is a loop. Its lift closes, and uniqueness of reversed lifts gives equality of their terminal points. Thus the definition is path independent. For continuity choose a path connected open W about x contained in the preimage of one evenly covered base neighborhood. Paths within W show that h there is a single inverse sheet composed with q. This proves continuity locally everywhere, not merely sequential continuity along the selected paths.

## Dimensions two and one; parity, onto-ness and uniqueness — question 5

In a two-dimensional real normed space, normalize an auxiliary Euclidean circle to parametrize S_X by a(t), 0≤t≤2, with a(t+1)=-a(t). This is a circle parametrization because every nonzero ray meets a norm sphere once and the normalization is continuous. The half-path gamma=q∘a on [0,1] is a loop. Its lift b ends at eta b(0), eta∈{±1}. Define h(a(t))=b(t) on the first half and h(a(t+1))=eta b(t) on the second. At t=1, the two definitions are b(1)=eta b(0); at t=2, eta b(1)=eta²b(0)=b(0). Finite pasting and the circle endpoint identification give a continuous lift. No dimension assertion about Y and no simply connectedness of the projective circle was used. Even monodromy is initially permitted and is subsequently excluded, not silently assumed away.

For source dimension at least two, q(-x)=q(x) implies h(-x)=±h(x). Continuity and connectedness make ||h(-x)-h(x)||∈{0,2} constant. Thus h is either even or odd. The quotient P_X is not a singleton; since F is onto and injective, P_Y is not a singleton either, so dim Y≥2 and S_Y is path connected.

If h were even, quotient topology would give a continuous hbar:P_X→S_Y and s=hbar∘F^{-1} would be a continuous section of pi_Y over the entire P_Y. Its image is open: at a selected point choose a chart and shrink the base neighborhood by continuity of s so that it remains in the chosen sheet. On that neighborhood it is the inverse chart. The negative image is open too. These two images are nonempty, disjoint, and cover S_Y, contradicting connectedness. Surjectivity of the quotient map F is essential here and has already been proved. Hence h is odd.

If h(x)=h(z), injectivity of F gives z=±x; oddness excludes -x. If y∈S_Y, surjectivity of F gives an x with h(x)=±y, and oddness supplies y as h(x) or h(-x). Thus h is bijective. Any other continuous sign lift k has ||k(x)-h(x)||∈{0,2}, continuously, so on the connected source it is identically h or identically -h. Both choices are continuous odd bijections.

If dim X=1, oddness and onto-ness force S_Y to be exactly two points, hence dim Y=1. There are exactly two odd bijections of these two antipodal points compatible with the sign classes, f and -f. Their only nonzero distance is 2. There may be other pointwise sign selections, but they are not odd bijections; the frozen assertion counts precisely the stated class.

## Planar monotonicity and both strict regions — question 6

This is the critical global metric check. Let a,c be independent unit vectors in a plane, and b a unit vector on the positive radial arc between them. The ray through b meets [a,c] at p=lambda b with 0<lambda≤1. Indeed b is the normalization of a positive combination of a,c; normalizing the coefficients to sum to one gives that intersection and convexity bounds its norm by 1. Hence p lies on [0,b], possibly p=b on a flat face. Add lengths along those two straight segments and apply the triangle inequality twice:

    1+||a-c||
      = ||a-p||+||p-b||+||p||+||p-c||
      ≥ ||a-b||+||c||
      = ||a-b||+1.

Thus ||a-b||≤||a-c||. Equality and p=b cause no failure. Endpoints follow by continuity; when c=-a, the required upper bound is the triangle bound 2. This is exactly the unit-circle crossing-segment subcase of the fully read Martini–Swanepoel–Weiss Proposition 31. No equality characterization or strict-convexity conclusion from that reference is needed.

Fix x and take y with ||x-y||<||x+y||. If y=x the constant path suffices; y=-x is impossible, and every other y is independent of x. Set n_t=||(1-t)x+ty|| and c_t=((1-t)x+ty)/n_t. The numerator never vanishes. The preceding inequality gives

    ||x-c_t||≤||x-y||.

For the second application, with 0<t<1, the identity

    y=(n_t/t)c_t+((1-t)/t)(-x)

has genuinely positive coefficients. Thus y is the intermediate radial point between -x and c_t, rather than c_t being the intermediate point in an incorrectly ordered arc. Applying monotonicity from -x gives

    ||x+y||≤||x+c_t||.

At t=0 this is the norm bound ||x+y||≤2, and at t=1 equality holds. Combining,

    ||x-c_t||≤||x-y||<||x+y||≤||x+c_t||.

Therefore the whole path stays in A_x={y:||x-y||<||x+y||} and joins y to x. Every point can be joined through x, so A_x is path connected. B_x={y:||x-y||>||x+y||}=-A_x is path connected through -x. The one-dimensional cases are singletons. This argument permits arbitrary flat intervals and equality plateaus; it never assumes the complement of the equality locus has only the components seen in a Euclidean picture.

## Ordered metric, extension and converse — question 7

Pointwise signs preserve the unordered norm pair, so h still satisfies (P). For fixed x write a(y)=||x-y||, b(y)=||x+y|| and D(y)=||h(x)-h(y)||. On A_x∪B_x,

    theta(y)=(D(y)-a(y))/(b(y)-a(y))

is continuous and takes values in {0,1}. It is constant on each of the two connected regions. At x it equals 0, and at -x oddness gives D(-x)=2=a(-x), so it is also 0 there. Therefore D=a on both strict regions. At any point of the remaining equality locus, (P) is a singleton equality and directly forces D=a=b. No limiting argument across that locus is required. Thus h is an ordinary surjective sphere metric isometry everywhere, and so is -h. This closes the full source-free auxiliary theorem.

For Banach X,Y, Source322 now yields the unique linear extension U of h. Since h(x)=±f(x), define sigma by f(x)=sigma(x)Ux. Nonzero unit vectors make the sign unique at each point. Oddness of both f and U gives sigma(-x)=sigma(x), with no regularity assertion about sigma.

If (V,tau) is another permitted pair, V|S_X is a continuous odd bijective lift of the same q. The just-proved two-lift classification, including dimension one, gives V|S_X=±h. Linearity extends this identity to all X, and the pointwise signs give tau=±sigma with the same global sign. Conversely an even sigma and an onto linear isometry U give (P) because their signs only interchange the two entries. For any y=Uu in S_Y, set c=sigma(u). Evenness gives sigma(cu)=c and f(cu)=c²Uu=y, proving surjectivity for arbitrary even signs. An arbitrary even sign may indeed be discontinuous; the proof neither forbids this nor needs to regularize it.

## Strongest compatible operations and reading limits — correctness parts of questions 8–9

The full compatible chain has been carried out above: antipodal quotient isometry → explicit double-cover lifting in each dimension → target connectedness excludes even parity → strict planar regions fix both ordered-distance branches → Source322. Ordinary path lifting, sphere topology and planar monotonicity are treated as paid classical operations. There is no unproved residual sign-cocycle condition, global face-intersection condition, dimension-matching theorem, or radial phase identity left between them. This establishes correctness of the whole composition; it does not assign it a substantial or technical contribution grade.

The mandated primary comparisons were actual body reads, not abstracts:

- Ilisevic–Omladic–Turnsek, [arXiv:2005.02949v1](https://arxiv.org/pdf/2005.02949v1), entire extracted text. Propositions 3.4–3.7 use midpoint sets and nested symmetric subsets to recover ray midpoints; Proposition 3.8 gives homogeneity; 3.10–3.11 handle two-plane images; Theorem 4.2 uses projective geometry and orthogonality in higher dimension. Those operations require phase data on all vectors. The radial formula from an arbitrary sphere phase map has not yet been shown to satisfy those hypotheses, so this theorem is not used as a shortcut.
- Tan–Gao, [arXiv:2008.09282v2](https://arxiv.org/pdf/2008.09282v2), entire extracted text. Lemma 2 supplies the same elementary antipodal argument. The stronger C(K)-to-arbitrary-Banach construction uses face pairs and norming functionals (Proposition 2, Lemma 6), then Urysohn functions to synchronize evaluation signs (Lemma 7) before constructing its extension. The special function-space geometry is an actual hypothesis; it is not supplied by arbitrary normed-space spheres.
- Enami–Matsuzaki, [arXiv:2603.00583v1](https://arxiv.org/pdf/2603.00583v1), entire extracted text. Local face rearrangements are metric on a face because the sum norms are 2. Lemma 3.7 glues all signed overlaps using nonempty signed triple intersections (Proposition 2.10). Proposition 4.1 uses a Urysohn perturbation to retain one face while reaching another; Theorem 1.1 then derives the weighted composition formula. General normed spheres are not assumed to have those signed intersections. R198 instead uses the fully proved topological lift and planar regions. No criticism of the CL-space paper is adopted as a premise.
- Martini–Swanepoel–Weiss, [arXiv:0708.2900v1](https://arxiv.org/pdf/0708.2900v1), complete section 3.5 including Proposition 31's proof and Corollary 32, plus visual inspection of printed pages 21–22. The exact crossing inequality used in R198 is reproduced and checked above. The reference's broader radial statement is not an unstated hypothesis of this review.

A bounded additional search for general projective/sphere operations led to Gehér, [arXiv:1606.03584v1](https://arxiv.org/pdf/1606.03584v1). I read its main statement section and complete Lemmas 3.1 and 3.8 proofs. Lemma 3.1 gets a radial whole-space isometry by inner-product polarization; Lemma 3.8 recovers projective two-planes as double orthogonal complements, applies projective geometry, and normalizes the resulting semilinear map. These are actual proof operations with inner-product hypotheses, not a general normed-sphere sign-lifting theorem that can be imported without proof. The complete single-angle theorems and complex cases were not read or invoked. The ordinary topological lifting operation relevant to the present theorem is already fully proved in the frozen proof and independently checked here, so correctness has no missing external lifting dependency.

The CL-space full-PDF 403 is an inherited access record, not my reading of that proof or a novelty argument. The uniform-algebra preprint was not read. These omissions limit literature/contribution conclusions; neither source is used by any step of this correctness derivation. No essential correctness comparison remains unfinished. The exact two original-history spans were read from their originals, not only copied versions. They contain warnings and do not supply the older I12 proof scope or clear any closed target. No old stability target is retried.

The separate READING document and private receipts record exact versions, byte extents, a new access failure and recovery, selected-only navigation, and isolation limits. No output truncation occurred in this review's semantic reads. Source PDF bytes were authenticated while its full TeX supplied the source proof reading. The author's disclosed overbroad/truncated I88 materialization was not repeated or semantically admitted. Coarse guards can omit useful originals, opaque names can escape classification, and bounded search provides no exhaustive clearance. Integrity verification and tiny copied controls support artifact identity only; none supplies the mathematical PASS.

## Final disposition

Questions 1–7 and the correctness obligations in 8–9 are resolved at the entire frozen scope. **PASS, with no mathematical repair requested.** The auxiliary normed-space theorem is proved without completeness; the Banach classification uses the stipulated source at its exact interface. The frozen statement and proof remain unchanged. Contribution, acceptance, count and any downstream work remain for the parent under the separate authorized process.
