# Structural198 independent substantial-contribution review — round 1

**Verdict: TECHNICAL at the entire unchanged frozen scope, CONDITIONAL on correctness of the entire frozen statement and proof. The correctness condition is UNDISCHARGED in this role.** This is not a correctness grade, an acceptance decision, or a campaign count. Parent alone may adopt grades and counts.

The reviewed statement is the 2,013-byte SCOPE, SHA256 `9b96245518d383432e770924856a44463c118ca68289eb7d85950acf1f872e09`. The reviewed 17,317-byte AUTHOR-PROOF has SHA256 `0133cd993a29c07911b198f4553121614363a4f4c5d45c2b67b10b4b60de406d`. Neither was edited. There was no earlier independent Structural198 finding, repair response, or unresolved reviewer objection supplied for this round. The parent's questions are checks, not adopted defects. No other review was read or its verdict inferred.

The result concerns every surjective map between unit spheres of nonzero real Banach spaces preserving the unordered set of the sum and difference norms, with no regularity assumption on that map. Its conclusion is an even pointwise sign times a surjective real-linear isometry, unique up to simultaneous sign, with the converse. The frozen auxiliary statement also concerns every nonzero real **normed** space, without completeness: exactly two continuous odd bijective sign lifts exist and are metric isometries. The reduction below includes that auxiliary assertion, dimensions one and two, arbitrary infinite dimension, flat faces and equality loci. It does not substitute a restricted result.

The reason for TECHNICAL is the complete compatible reduction in sections 2–5, not the fact that individual ingredients have familiar names. It closes the putative residual by explicit elementary consequences of the classical double-cover lifting operation and planar norm-circle monotonicity. Source322 then supplies exactly its stipulated ordinary sphere-isometry extension. No additional geometric estimate, facial compatibility theorem, or global sign mechanism remains unpaid after that composition. This is a campaign contribution assessment; it does not assert that the exact formulation has previously appeared in print or that every neighboring problem is routine.

## 1. Actual source interface and paid proof operations

Source322 is [A positive solution to Tingley's problem, pinned main.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-positive-solution-to-Tingleys-problem-September-23-2026/build/main.tex). Theorem `thm:main` takes nonzero real **Banach** spaces and a surjective ordinary sphere metric isometry. It returns the radial formula as the unique surjective real-linear isometry. All four canonical blobs were independently matched to the complete pinned preprints tree by bytes, Git blob identity and SHA256. I read all 35,253 bytes of main.tex, all 5,302 bytes of the sole included references.tex and the 557-byte wrapper. The wrapper identifies no additional operative mathematical companion. The canonical PDF was authenticated; the semantic source reading was its TeX.

The entire operative proof at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is stipulated TRUE. In particular, its uniform radius defect, inversion of its sign, attainment through normalized ultraproducts and completion (`lem:attainment`), common-support propagation, invariant convex set and opposite-endpoint return map (`prop:alignment`), finite scalar-bin Kuratowski contraction and Darbo (`thm:condensing` and appendix), secant support bounds, inverse aligned configuration, perturbation and chord contradiction (`lem:secant`, `lem:large`, `prop:no-defect`), radial metric extension and midpoint reflection are all paid. I do not audit their truth or count any of those operations as the nominee's contribution.

The source uses ordered distance equalities. Its full proof contains no permission to apply the theorem to a phase map before selecting an ordinary sphere isometry. The construction below reaches precisely that interface, and invokes the theorem once, only after the source-free auxiliary assertion has been established.

## 2. Quotient and lifting operations at the full normed-space scope

Throughout sections 2–4, X and Y are arbitrary nonzero real normed spaces, not necessarily complete. Write P for the frozen unordered-set identity.

### 2.1. Antipodal bijectivity and the correct quotient metric

Given x, surjectivity supplies z with f(z)=-f(x). P gives

    {||x-z||, ||x+z||}={0,2}.

Thus z=x or -x; z=x would make a unit vector f(x) equal its negative. Therefore f(-x)=-f(x). If f(z)=f(x), the same zero-norm argument gives z=±x, and oddness excludes -x. Hence f is bijective. This is exactly the arbitrary-normed-sphere operation in Tan–Gao, Lemma 2, not a new contribution. Repeated entries cause no problem: an unordered set {a,b} equal to a singleton forces both a and b to be its sole member.

On Q_X=S_X/{±1} define

    d_X([x],[z])=min(||x-z||,||x+z||).

To prove its triangle inequality, fix a representative x, choose the sign of y minimizing its distance to x, then choose the sign of z minimizing its distance to that chosen y. The norm triangle inequality bounds d_X([x],[z]) by the sum of the first two minima. Zero distance means equality of classes. Thus this is a genuine metric.

Let 0<r<1/2. Every class in B_Q([a],r) has exactly one representative in the relative sphere ball B_S(a,r); two such representatives would be antipodal at distance 2, impossible inside a ball of diameter <2r. For u,v in this sphere ball,

    ||u-v||<2r<1,            ||u+v||>=2-||u-a||-||v-a||>2-2r>1.

Consequently the projection π_X restricts to an isometry on this ball. Its full inverse image is the disjoint pair B_S(a,r) and B_S(-a,r). These give two-sheet covering charts. The projection is continuous (indeed 1-Lipschitz) and open, since any sphere neighborhood contains such a ball. Thus its quotient and displayed metric topologies agree.

Now F([x])=[f(x)] is a bijective isometry Q_X→Q_Y by P. Hence q=Fπ_X is continuous, regardless of whether f is continuous. All subsequent lifting is applied to q, not to f.

### 2.2. The classical lifting operation, including moving basepoints

For these charts a path has a unique lift from either chosen initial point: subdivide its compact parameter interval into pieces mapping into evenly covered balls, and use the inverse chart on the sheet determined by the previous endpoint. The finitely many pieces agree at endpoints. Uniqueness follows either by this subdivision or because equality and inequality of two lifts are both locally preserved in a chart.

For a continuous square H:[0,1]^2→Q_Y, take a finite rectangular grid so that each closed cell maps into one evenly covered neighborhood. Such a grid exists by a Lebesgue number for the pullback open cover of the compact square. Choose a sheet at the first corner. Extend across the first row and then successive rows. A new cell already has its left edge, its bottom edge, or both specified. Each such edge lies in one sheet over the cell's evenly covered neighborhood. If both edges are present, their sheets agree at their common corner, hence are the same sheet. The inverse chart therefore agrees with every prescribed edge by unique path lifting. Finite pasting gives a continuous square lift.

If H(s,0)=H(s,1), the two lifted endpoints differ by a sign. Their norm distance is a continuous function of s taking values in {0,2}; it is constant. Thus a free homotopy to a constant loop makes any lift close even though the loop basepoint moves. This is the exact compatibility needed below. It does not silently replace a free contraction by a based contraction.

These are the operations in Hatcher's actual proofs of the covering homotopy property, lift existence and lift uniqueness: [Algebraic Topology, chapter 1](https://pi.math.cornell.edu/~hatcher/AT/ATch1.pdf), proof of Theorem 1.7(c) and Propositions 1.30, 1.33, 1.34. The proofs were read, not merely cited by name. The elementary grid version above exposes the hypotheses at this application.

### 2.3. Dimension at least three: a finite construction inside any normed space

S_X is path connected if dim X≥2: normalize the straight segment between nonantipodal points; for antipodal endpoints concatenate through an independent unit vector. It is locally path connected. Indeed N(w)=w/||w|| is open on X\{0}: nearby sphere points v give nearby vectors ||w||v. Small convex balls about a unit a avoid zero; their images under N are open, path connected, and arbitrarily small because

    ||N(w)-a|| <= 2||w-a||.

Suppose dim X≥3 and α:[0,1]→S_X is a loop. Choose finitely many sample points with polygon p satisfying ||p(t)-α(t)||<1/8 uniformly; uniform continuity of α suffices. Then p never vanishes, β=N(p) satisfies ||β-α||<1/4, and

    N((1-s)α(t)+sβ(t))

is a homotopy of loops: its argument stays within 1/4 of the unit α(t).

The normalized polygon lies in finitely many subspaces E_i=span{α(t_i),α(t_{i+1})}, each of dimension at most two. Choose a three-dimensional linear subspace V of X. Each E_i∩V is proper, so choose a nonzero functional ℓ_i on V vanishing there. With a basis e_1,e_2,e_3 of V, each polynomial

    ℓ_i(e_1+t e_2+t² e_3)

is nonzero and has finitely many roots. Choose t outside their finite union and normalize e_1+t e_2+t²e_3 to z. Then z belongs to none of the E_i. The homotopy

    N((1-s)β(t)+s z)

contracts β to z. A zero argument would make z a negative scalar multiple of β(t), contrary to z∉E_i. This uses only finite-dimensional algebra in V. It assumes no global finite dimension, completeness, separability, compactness of S_X, or smoothness.

Choose x_0 and one y_0 over q(x_0). Define h(x) as the endpoint of the lift, starting at y_0, of q composed with a path x_0→x. Two such paths differ by a sphere loop. Its free nullhomotopy, composed with q and lifted as above, forces zero monodromy. If their lifted endpoints differed by sign, lifting the reversed second path from the first endpoint would end at -y_0, contradicting closure. Thus h is path independent.

For continuity near x, choose a path-connected open W containing x with q(W) inside an evenly covered ball. A fixed path to x followed by paths in W shows h|W is q followed by one inverse chart. Hence h is continuous and π_Yh=q. In particular h(x)∈{f(x),-f(x)}. This is the usual covering-space construction with its source hypotheses explicitly supplied.

### 2.4. Dimension two: the monodromy is squared

A norm sphere in a two-dimensional real space is homeomorphic to the Euclidean circle by radial normalization. Parametrize it by a:[0,2]→S_X with a(t+1)=-a(t) and only a(0)=a(2) identified. The path q(a(t)), 0≤t≤1, is a loop because q is antipodally invariant. Let b be its lift, b(0)=y_0, b(1)=ηy_0 with η∈{±1}. Define

    h(a(t))=b(t),             0≤t≤1,
    h(a(t+1))=η b(t),         0≤t≤1.

At the half-circle junction both formulas give ηy_0. At the final junction ηb(1)=η²y_0=y_0. Both pieces project to q. This gives a continuous lift in either monodromy case without assuming the target dimension or simply-connectedness of the projective circle. The operation is precisely double traversal killing a two-element monodromy.

### 2.5. Odd parity, onto, injectivity, and exactly two lifts

For dim X≥2, h(-x)=±h(x) and the continuous function ||h(-x)-h(x)|| takes values in {0,2}. Connectedness makes the parity constant. Also dim Y≥2: otherwise Q_Y, hence the bijective Q_X, would be a singleton.

An even lift would descend through π_X to h̄:Q_X→S_Y. Then s=h̄F^{-1} is a continuous section of π_Y on the entire Q_Y. The image of a section is open: near a selected point, continuity restricts s to one sheet of an evenly covered neighborhood, where it equals the inverse chart. Its negative is open too. Those two images are nonempty, disjoint and exhaust S_Y. This contradicts connectedness of S_Y, proved by the same normalized-segment argument. Hence h is odd.

If h(x)=h(z), quotient bijectivity gives z=±x, and oddness eliminates -x. If y∈S_Y, surjectivity of F gives [h(x)]=[y]; either x or -x maps to y. Thus h is bijective. Any two continuous lifts of q differ by sign pointwise, and their mutual distance is a continuous {0,2}-valued function on connected S_X. They differ by one global sign. Both h and -h exist and are distinct, so there are exactly two continuous lifts, both odd and bijective.

If dim X=1, oddness and surjectivity of f give S_Y={f(x_0),-f(x_0)}, forcing dim Y=1. Exactly two odd sign lifts on the two-point sphere are possible, f and -f. They are continuous bijections and preserve the sole nonzero distance 2. This handles the disconnected small-dimensional case separately.

## 3. Global ordered distance, including flat faces

The covering argument alone yields a local sphere isometry. One must not infer the ambient chord metric globally from a length metric on the sphere. The following classical planar operation is the missing interface, and closes it explicitly.

For unit nonantipodal distinct a,c in a normed plane, let b be a unit vector on their positive radial arc. The ray through b meets [a,c] at p=λb with 0<λ≤1 by convexity. Add lengths on the two intersecting straight segments:

    1+||a-c||
      = ||a-p||+||p-b||+||p||+||p-c||
      >= ||a-b||+||c||
      = ||a-b||+1.

Thus ||a-b||≤||a-c||. This is exactly the unit-radius crossing-segment operation in [Martini–Swanepoel–Weiss, 0708.2900v1, §3.5, Proposition 31](https://arxiv.org/pdf/0708.2900v1). I read the entire proposition and proof, its two geometric cases and Corollary 32, and visually inspected pages 21–22. The application here needs only the displayed unit-radius case. It does not need the strict-convexity conclusion or the corollary. The boundary case p=b on a flat face is allowed by the same non-strict inequality. If c=-a, use ||a-b||≤2; coincident endpoints or arc endpoints follow directly or by continuity.

Fix x∈S_X and set

    A_x={y: ||x-y||<||x+y||},
    B_x={y: ||x-y||>||x+y||}=-A_x.

For y∈A_x other than x, x and y are linearly independent: the other collinear unit choice -x is not in A_x. Let

    n_t=||(1-t)x+t y||,       c_t=((1-t)x+t y)/n_t.

The numerator never vanishes. The first planar application gives ||x-c_t||≤||x-y||. For 0<t<1, the actual coefficients in

    y=(n_t/t)c_t+((1-t)/t)(-x)

are positive. Therefore y is the intermediate unit radial direction from -x to c_t. The second planar application gives ||x+y||≤||x+c_t||. At t=0 the latter inequality is the bound ||x+y||≤2; at t=1 it is equality. Consequently

    ||x-c_t|| <= ||x-y|| < ||x+y|| <= ||x+c_t||

for every t. Every y∈A_x is joined to x by a path within A_x. Thus A_x is path connected, and B_x is path connected through -x by antipodes. No assumption about the shape or size of the equality set is involved. In dimension one these sets are singletons.

Since h differs from f by pointwise signs, it still satisfies P: multiplying the two images by signs merely permutes the sum and difference norms. For fixed x, put

    a(y)=||x-y||,  b(y)=||x+y||,  D(y)=||h(x)-h(y)||.

These functions are continuous. On A_x∪B_x,

    θ(y)=(D(y)-a(y))/(b(y)-a(y)) ∈ {0,1}.

Thus θ is constant on each of the two connected strict regions. At x it equals zero; at -x it equals zero because h is odd and both D(-x) and a(-x) are 2. Therefore D=a on both regions. On the remaining equality locus, P directly implies D=a=b. Flat equality intervals do not require a choice or continuation of a sign.

It follows that ||h(x)-h(y)||=||x-y|| for all sphere pairs. Combined with section 2, this proves the complete source-free auxiliary conclusion by the stated classical composition, including arbitrary incomplete normed spaces and exactly two continuous odd bijective isometric lifts. No continuity or measurability of f or of its eventual sign function entered.

## 4. The Banach conclusion, uniqueness and converse

For Banach X,Y the h just constructed is a surjective ordinary sphere isometry. Invoke Source322's `thm:main` once to obtain its unique surjective real-linear isometry U, with U(z)=||z||h(z/||z||) for z≠0. Because f(x)=±Ux, there is a unique sign σ(x) with f(x)=σ(x)Ux. Oddness of both maps forces σ(-x)=σ(x).

If f(x)=τ(x)Vx is another such pair, V restricted to S_X is a continuous odd bijective lift of q. It equals h or -h by section 2. Real homogeneity gives V=U or -U on all vectors, with τ=σ or -σ respectively. The two-point case was already treated, so no dimension is missing.

Conversely let U be any surjective real-linear isometry and σ any even sign on S_X. For f(x)=σ(x)Ux, each pair of signs only permutes the two norms, so P holds. Given y=Uu∈S_Y and c=σ(u), evenness gives σ(cu)=c and hence f(cu)=c²Uu=y. Thus f is surjective. This recovers all conclusion clauses without extra regularity.

Completeness has been used only at the Source322 invocation. Complex spaces are included only as real spaces, with signs ±1 and a real-linear conclusion. Nothing here proves an arbitrary complex-phase, quantitative, nonsurjective or stability version.

## 5. Why the integrated construction is technical under the campaign rule

There are three interfaces to pay, and each is explicitly closed above.

1. **From discontinuous f to a continuous sign choice.** Antipodal bijectivity is already proved in the actual primary sphere literature. Taking the quotient by the free two-element action makes continuity automatic. Standard covering lifting applies because norm spheres of dimension ≥3 have the finite polygon contractions given above; the circle case is the elementary identity η²=1; the line is discrete. Oddness and onto then follow from the absence of a section of a connected two-sheet cover. This is the usual covering operation with all low- and infinite-dimensional hypotheses checked, not a new cocycle theorem.
2. **From a continuous sign lift to the ordered metric.** The two applications of the classical planar monotonicity inequality have the exact compatible angular order. They connect the strict-distance regions to their distinguished endpoints. A continuous function with two possible values is constant on a connected set. Equality loci require no additional operation. This supplies a full global distance identity, rather than merely local continuity, a list of ingredients, or an assumed radial phase identity.
3. **From the sphere metric to the classification.** The hard arbitrary-Banach extension is entirely stipulated Source322. The evenness, global-sign uniqueness and converse are immediate algebra after the lift, and are explicitly verified above.

All three work together at the unchanged quantifiers. None leaves an unpaid nonroutine residual. The author's description “global sign recovery” names the combined output but does not by itself demonstrate contribution beyond this full classical/source composition. Conversely, the fact that faces and Urysohn arguments in special spaces are more elaborate is not a reason to dismiss their substance; it simply does not obstruct the universal covering/planar route when evaluating this nominee with Source322 already paid.

This conclusion is not a claim of prior publication of the exact theorem or a theorem-by-theorem bibliographic duplication certificate. A project-new statement can be technical. The campaign rule excludes routine compatible compositions even when the final statement is broader than a particular antecedent. The complete full-scope derivation, not absence of search hits, supports the conditional grade.

## 6. Actual primary and original-history comparisons

**Whole-space phase isometries.** [Ilišević–Omladić–Turnšek, 2005.02949v1, From Mazur-Ulam to Wigner](https://arxiv.org/pdf/2005.02949v1), was read in its entirety. Propositions 3.4–3.7 transport paired midpoint sets and iterate shrinking symmetric sets on rays. Proposition 3.8 obtains homogeneity up to sign. Propositions 3.10–3.11 obtain planes and the two-dimensional representation; Theorem 4.2 then uses projective geometry and Birkhoff–James orthogonality in higher dimension. These operations take off-sphere points and unequal radii as inputs. Defining R(rx)=rf(x) does not establish their phase identity: the sphere data initially contain only r=s. The reduction above does not use this unavailable hypothesis. A radial phase identity becomes available after the linear U is obtained, so invoking the whole-space theorem then would be redundant.

**C(K), arbitrary Banach target.** [Tan–Gao, 2008.09282v2](https://arxiv.org/pdf/2008.09282v2), was read completely, including the arbitrary-target section. Lemma 2 pays antipodal bijectivity. The face/star and separable-reduction arguments identify antipodal pairs of maximal faces. Proposition 2 and Lemma 6 associate evaluation values with norming functionals in Y*. Lemma 7 uses the constant function and Urysohn-separated test functions to synchronize their signs for each input function. Theorem 2 uses the norming family to make a radial extension a metric isometry and then invokes Mazur–Ulam. Those are actual sign-synchronization operations, not just a statement about C(K). General normed spaces do not supply the constant function, evaluation faces or Urysohn tests. Sections 2–3 above use a different compatible classical route and make no claim that this primary already states the full arbitrary-source theorem.

**C0, signed overlap gluing.** [Enami–Matsuzaki, 2603.00583v1](https://arxiv.org/pdf/2603.00583v1), was read completely. Lemma 2.3 also explicitly pays surjectivity under even sign changes. The proof constructs local face rearrangements Φ_x; Lemmas 3.4–3.7 make their relative signs constant on connected face intersections and synchronize every signed case through a base point and nonempty signed triple intersections. Proposition 4.1 perturbs inside two prescribed faces using a dyadic Urysohn construction. Theorem 1.1 then recovers moduli, their signs and the weighted composition representation. Arbitrary norm spheres need not have those triple intersections. The quotient construction above does not import them; its continuity is obtained before any distance-branch selection. This paper's criticism of the CL-space proof is not adopted as an independent verdict about that proof.

**Uniform algebras, late comparison completed.** I independently obtained and read all of [Enami–Hirota–Matsuzaki–Miura, 2606.22320v1](https://arxiv.org/pdf/2606.22320v1). This is stronger evidence than the author's navigation-only reading. The proof normalizes constant-function phases on Choquet boundaries, splits identity/conjugation cases, and synchronizes scalar signs. Proposition 4.10 constructs two peak functions with a joint max-norm identity, uniformly in the chosen phases and amplitudes. Lemmas 4.11–4.14 use facewise isometries, connected overlaps, short phase chains and constants to glue input signs. Lemma 4.15 supplies a two-point perturbation; Theorem 2 obtains the boundary representation, followed by extension to Shilov boundaries and maximal ideal spaces. Pages 3, 9 and 16 were rendered and inspected to resolve conjugation bars omitted by text extraction. These operations use algebra constants, Choquet peak functions and boundary geometry. I do not assume their extension to arbitrary real normed spheres, or claim the frozen theorem includes their algebraic representation. They do not leave an essential dependency in the full classical reduction above.

**General projective/covering antecedents.** Hatcher's actual path/homotopy/general-lift proofs were read at the exact extents in READING.md and instantiated above. In addition, [Gehér, 1606.03584v1](https://arxiv.org/pdf/1606.03584v1), main statements and complete Lemmas 3.1 and 3.8, were inspected. The latter recovers projective lines by double orthogonal complementation, uses projective geometry, and then orthogonality to restrict the semilinear transformation to an isometry; Lemma 3.1 uses polarization for a radial angle-preserving map. These are actual operations for inner-product spaces, including incomplete ones. A general norm does not acquire that inner product or polarization from P. Thus I do not import Wigner's projective conclusion wholesale. The general continuous-lift comparison actually needed here is the ordinary double-cover operation, whose hypotheses and full-scope construction were verified explicitly in section 2. The complete angle-classification paper was not read, and no claim about its unread sections is made.

**CL-space access limit.** The publisher's available introduction and section snippets identify the real-CL-source/arbitrary-real-Banach-target theorem. A fresh bounded request for its full PDF returned HTTP 403, matching the author's disclosed access failure. Its full proof was not read. This is neither a novelty premise nor an unresolved essential dependency of this TECHNICAL verdict: no step in sections 2–4 uses a CL theorem, a disputed face-gluing claim, or an assertion that CL authors failed to find the present route. Were the task to certify priority or compare every proof variant, that access failure would prevent such a certification; no such certification is given here. [Publisher page](https://www.sciencedirect.com/science/article/abs/pii/S0022247X23005711).

**Original project history.** I read the actual original I13 bytes [1311,4107) and I88 bytes [1160,6224), by binary seek before decode. These are the admitted heading sections, ending at the next equal heading. They warn about spent Tingley-ultraproduct and coordinate-spiral stability routes; they do not contain the original I12 theorem/proof scope. No linked directory, excluded original, old stability target or closed Structural195/196/197 body was read, reopened, cleared or retried. The present conditional comparison does not use those warnings as mathematical lemmas or old grades. No additional original-history selection was essential to the explicit exact, non-stability reduction.

## 7. Parent questions, obligations and limits

Question 8 is resolved by the actual integrated full-scope derivation above: **TECHNICAL, conditional on full correctness**. Questions 1–7 are represented by the explicit source interface, quotient charts, square lifting with moving basepoints, arbitrary-dimensional polygon contractions, circle/line cases, parity/onto/uniqueness, planar flat-face analysis, ordered-distance identity and converse. This is the mathematical content required to assess contribution; it is not a substitute correctness review or a repair of the frozen author proof.

No essential comparison remains unfinished for this conditional contribution determination. The indispensable outstanding condition is independent adoption of correctness of the entire unchanged statement and proof by the parent. It remains **UNDISCHARGED** in this role. No PASS label, correctness discharge, acceptance decision or campaign increment is assigned here. If the independent correctness review requires a repair, this review does not license silently changing the frozen proof and carrying this verdict to the changed object.

Question 9 is addressed in [READING.md](READING.md): exact versions and extents, one output truncation and recovery, one UTF8 boundary failure and recovery, late primary reads and queries, access limits, protected rights, prospective guards and original byte/mode controls. Bounded navigation is not exhaustive project or literature clearance. Coarse exclusions can omit useful originals; opaque aliases can escape classification. No broad authored-history rerun or peer inspection occurred. The Lean comparator ends in `sorry`; it supplies no formal proof coverage. Artifact checks are not mathematical gates.

Authorized provenance: Codex / GPT-6 Astra / xhigh / default service tier. The user-supplied Campaign19/20 and latestR041 were not independently polled or changed. Publication, uploads, submissions, contacts, browser UI, formalization, manuscript and release work remained stopped. All outputs are confined to this exclusive review root.
