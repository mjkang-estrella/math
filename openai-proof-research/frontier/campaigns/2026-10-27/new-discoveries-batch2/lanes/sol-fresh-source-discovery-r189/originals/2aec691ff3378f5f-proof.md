# AGM063: complete author proof

This proof assumes the pinned source truths at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. It does not audit their proofs. Classical inputs below are identified separately. The fixed statement is in fixed-scope.md.

## 1. Inputs and conventions

For a family of rational curves, “family” always means a full irreducible component of RatCurves^n(X), and “unsplit” means that this component is proper. We use the associated proper Chow family when forming chains. A curve in such a family is an irreducible rational image, not a parametrized multiple cover. Numerical curve spaces have real coefficients.

**S1 (pinned family063, introduction thm:main).** For every smooth positive-dimensional complex Fano manifold, r(i−1)≤n, with equality precisely for (P^(i−1))^r.

**S2 (pinned family063, trace.tex prop:independent-correspondences, supplied by spectral.tex prop:spectral).** If i≥2, there are r linearly independent numerical stable-map degrees γ_1,…,γ_r such that

    S_(γ_1)…S_(γ_r) ≠ 0,       Σ_j(d_j−1) ≤ n,

where d_j=−K_X·γ_j≥i. The operators act on even cohomology, and S_γ lowers complex codimension by d_γ−1. As defined in setup.tex, S_γ is induced by the algebraic two-evaluation pushforward of the genus-zero virtual class, of cycle dimension n+d_γ−1 on X×X. The finite numerical-degree convention sums the finitely many actual curve classes.

**P1 (proper rational-chain quotient).** For finitely many proper Chow families on a smooth projective X, there is a dense open X^0 and a proper surjective morphism π:X^0→B^0 whose point fibers are entire rational-chain equivalence classes in X. In particular X^0 is saturated for this equivalence relation. After restricting to a dense open in the base, the fibers can be taken pure of dimension n−dim B^0. This is Kollár, Rational Curves, IV.4.16, as stated in Fujita's primary paper, Theorem 3.2. The final restriction preserves saturation. Proper fibers are compact closed subvarieties of X, even though X^0 need not equal X.

**P2 (minimal-family construction).** Fujita Construction 3.5 begins with a minimal dominating family and then takes a minimal horizontal dominating family for the proper rational-chain quotient of those already selected. It terminates with finitely many numerically independent families and rational-chain connectedness. The degree is minimized among full families with the specified property, in the sense of his Definitions 2.1–2.2.

**P3 (Fujita Corollary 6.4).** In the range of fixed-scope.md with r≥2, if every family in Construction 3.5 is unsplit, there is an extremal ray whose contraction has every fiber of dimension at most i−1. Its proof uses the inequality in Lemma 3.6 to obtain at least r−1 independent dominating unsplit families, followed by Theorem 6.1. It does not assume that all of the original S2 families dominate.

**P4 (Fujita Proposition 5.3(b)).** Such a contraction, together with the advanced generalized Mukai classification for its base dimension and one less Picard number, yields the five types in fixed-scope.md. His proof uses Theorem 5.2 to obtain a P^(i−1)-fibration, Lemma 4.2 for a Fano base Y with ρ(Y)=r−1 and ι(Y)≥i, then the rationality of the listed bases and the explicit bundle classifications in Corollaries 4.6–4.7. The full proof and those bundle arguments were read. No new vector-bundle classification is asserted here.

**P5 (rank-one base case).** A smooth Fano n-fold with pseudoindex at least n is P^n or Q^n. Use Dedieu–Höring, Numerical characterisation of quadrics, Theorem 1.3, rather than relying on the incomplete original argument noted in that primary paper. Q^2 has Picard number two. Dimension one is P^1.

We also use the standard algebraic virtual-cycle and refined-intersection construction of the S2 correspondences, and the facts that a nonzero effective divisor on a smooth projective variety is not numerically trivial and that a finite union of proper closed subsets cannot cover an irreducible variety. All uses are explained below.

## 2. Low degree gives full proper families

Let i≥2 and let γ be a positive numerical stable-map degree with d_γ<2i. Every genus-zero stable map of that degree has exactly one nonconstant component, and it maps birationally to its image: two nonconstant components, or a multiple cover of degree at least two, would contribute at least 2i to the anticanonical degree. After forgetting all markings and stabilizing, no contracted component remains. Indeed, any contracted subtree would have a leaf with fewer than three special points. Thus the unmarked map has domain P^1 and is birational to its irreducible rational image.

Properness of the unmarked stable-map spaces, and this absence of reducible or multiple-cover limits, imply that every full RatCurves component of numerical degree γ is proper. This is exactly the degree argument of source equality.tex lem:minimum-degree-incidence, with “degree i” replaced by the still sufficient strict inequality d_γ<2i. It is a technical extension of that operation, not the main contribution.

There are only finitely many such full components in any of our finitely many numerical degrees. Bounded anticanonical degree bounds every numerical coordinate by setup.tex; the proper finite-type stable-map spaces in those degrees have finitely many irreducible components. The unmarked spaces surject onto the unparameterized rational-curve loci, and normalization does not add infinitely many components. Let V be the finite collection of ALL full RatCurves components in the selected degrees. Keeping all these components avoids making any unjustified choice of one incidence component from a virtual class.

For each selected degree γ, let R_γ⊂X×X be the union of the two-point incidence relations for these families. This is closed: each relevant universal family is proper, and its two-fold fiber product maps properly to X×X. The two marked points of a stable map with this degree lie on its unique rational image, including when markings are carried by contracted bubbles. Therefore the two-evaluation virtual correspondence is supported on R_γ. Every pair in R_γ is connected by a curve from V.

## 3. A support-dimension connectivity lemma

**Lemma.** Let X be a smooth connected projective n-fold, n≥2. Let V be finitely many unsplit full rational-curve families whose numerical classes span N_1(X). Suppose a closed set Z⊂X×X consists entirely of pairs connected by chains from V and has dimension at least 2n−1. Then X is rational-chain connected by V.

**Proof.** Apply P1 and shrink the base to make the proper saturated quotient π:X^0→B^0 equidimensional. Put b=dim B^0 and E=X\X^0. If a pair in Z has one endpoint in X^0, its other endpoint lies in the SAME entire equivalence class, hence also in X^0 and in the same π-fiber. This is an actual support inclusion, not a generic statement:

    Z ⊂ (X^0 ×_(B^0) X^0) ∪ (E×E).

The first set has dimension 2n−b and the second at most 2n−2. These are constructible pieces of the indicated dimensions. Consequently b≥2 would force dim Z≤2n−2, a contradiction.

If b=1, choose one rational curve C_a from each of the finitely many families. Any C_a which meets X^0 is wholly contained in a single π-fiber: all its points are chain equivalent, and that fiber is the full class. Curves not meeting X^0 are disjoint from every fiber. Choose a closed point t of the positive-dimensional base different from the finitely many fiber values just encountered. Then F=π^−1(t) is a nonempty compact closed subvariety of X, pure of dimension n−1, and is disjoint from every C_a. Let D be any prime component of F. Since X is smooth, D is a nonzero effective Cartier divisor. We have D·C_a=0 for every a, so the spanning hypothesis implies D is numerically trivial. But D·H^(n−1)>0 for an ample divisor H, a contradiction. This argument neither extends π across E nor presumes that the whole family is covering.

Thus b=0. The fiber X^0 of the proper map to a point is proper; its inclusion into separated X has closed image. As X^0 is also dense and open in irreducible X, X^0=X. P1 now says that all X is one chain equivalence class. ∎

The divisor argument only needs finitely many representatives, not a simultaneous avoidance assertion for all curves in each family. Their fixed numerical classes supply the necessary conclusion.

## 4. The quantum word supplies the large closed support

Under the fixed hypothesis, S1 gives

    0 ≤ δ := n−r(i−1) ≤ 1.

If i=1, n≤1 and the Fano-curve classification contradicts i=1, so i≥2. For the S2 degrees, putting s=Σ_j(d_j−1),

    r(i−1) ≤ s ≤ n,        Σ_j(d_j−i) ≤ δ ≤ 1.

Thus every d_j is at most i+1<2i. Section 2 supplies the finite proper family collection V. Its numerical classes span N_1(X), since they include representatives of the r independent degrees from S2.

Compose the algebraic virtual correspondences defining the S2 word. Refined pullback along consecutive diagonals, intersection, and proper projection give a Chow cycle class of pure dimension n+s on X×X. Its action on even cohomology is the nonzero operator in S2, so its cycle class, and hence any cycle representative of that class, is nonzero. Refined intersection preserves support on the incidence fiber product. Therefore a representative is supported on the closed set Z of endpoints of the corresponding ordered chains, obtained as a proper image of the product incidence variety. No positivity of virtual classes is used.

If dim Z<n+s, the group of cycles of dimension n+s supported on Z is zero. Thus

    dim Z ≥ n+s ≥ 2n−1.

Every pair in Z is chain equivalent for V, including every pair in the closure, because the incidence relations and their composition were proper closed images to begin with. This avoids an illicit closure of a merely generic chain relation. The lemma in Section 3 applies and proves that V rational-chain connects all of X. For n=1 the fixed classification is already P^1, so that case does not require the lemma.

## 5. A bounded connecting collection controls minimal horizontal degrees

We prove the precise interface required by P3.

**Lemma.** Suppose a smooth projective X is rational-chain connected by finitely many unsplit full families V_a of degree at most M with respect to a fixed ample divisor. Then the minimal dominating family, and every minimal horizontal dominating family arising in P2, have degree at most M.

**Proof.** Since dim X>0 and every point is chain equivalent to every other, each point lies on a curve of at least one V_a. The finitely many loci Locus(V_a) are closed by properness. Their union equals irreducible X, so at least one is X. This proves the bound for the initial minimal dominating family.

Consider an intermediate proper saturated quotient ψ:U→B with dim B>0. For any full irreducible V_a, either its general member meeting U is horizontal, or every member meeting U is contained in one ψ-fiber. To justify the latter assertion, the condition that two points of one member lie in U and have distinct ψ-images is open on the two-fold universal curve over V_a. If it is nonempty, it dominates a nonempty open of the irreducible family and the general member is horizontal. If it is empty, ψ is constant on the nonempty open C∩U of every member meeting U. Properness of its fiber makes that fiber closed in X, so it contains the entire irreducible curve C. Thus no exceptional horizontal member can be hidden in a generically vertical family.

Suppose no horizontal V_a dominates B. For each horizontal V_a, the closure in B of ψ(Locus(V_a)∩U) is then a proper closed subset. Choose t outside the finite union of those subsets. No horizontal family meets F=ψ^−1(t). Every other V_a member meeting F is contained in F by the preceding paragraph. Hence every chain made from V starting at a point of F remains inside F. This contradicts rational-chain connectedness by V, because F is a proper subset of X. Some V_a is therefore horizontal and dominant over B. Its degree is at most M, and the defining minimality in P2 gives the same bound for the chosen minimal horizontal dominating family. ∎

Apply this lemma with M=i+1 and the V of Section 4. At every step of P2 the chosen degree is at most i+1<2i; Section 2's unsplit argument applies to that chosen full component as well. Consequently ALL families in P2 are unsplit. In particular this proof does not identify the initial correspondence families with Fujita's minimal horizontal families, does not declare all of them covering, and does not replace horizontal dominance by mere nonconstancy on one special curve.

## 6. Classification by Picard-number induction

For r=1 the fixed inequality gives i≥n. P5 gives P^n or Q^n; the actual Picard number excludes Q^2. These are the stated types. The dimension-one convention was already handled.

Suppose r≥2 and assume the fixed classification for all smaller Picard numbers. Section 5 gives the exact unsplit-family premise of P3, so there is an extremal ray R whose contraction f:X→Y has every fiber of dimension at most i−1. Fujita Theorem 5.2 makes f a P^(i−1)-fibration; in particular the base is smooth, and Lemma 4.2 gives that it is Fano with

    dim Y=n−i+1,      ρ(Y)=r−1,      ι(Y)≥i.

Its dimension is positive: n≥r(i−1) and r≥2, i≥2 imply n−i+1≥i−1≥1. Moreover

    (r−1)(ι(Y)−1) ≥ (r−1)(i−1) ≥ (n−i+1)−1.

Thus the induction hypothesis applies to Y at its actual invariants. This supplies precisely the smaller-Picard-number classification premise of Fujita Proposition 5.3(b). That proposition and its explicit bundle classification give the five types for X.

For clarity about a possible increase of pseudoindex on the base: in the defect-one case, S1 on Y gives (r−1)(ι(Y)−i)≤1. If r≥3, then ι(Y)=i. For r=2 the base may be P^i, of pseudoindex i+1, or Q^i, of pseudoindex i; Fujita Corollary 4.7(d) is exactly the P^i case and includes the two nontrivial bundles. This is not an omitted constant-pseudoindex assumption. In the equality case the source S1 already gives type 1 directly.

## 7. Verification of the list and boundary cases

For products, the Picard numbers add and the pseudoindex is the minimum of the pseudoindices of the factors: an irreducible rational curve projects to rational curves or points, and anticanonical degrees add with nonnegative terms; a line in a factor attains the minimum. P^m has pseudoindex m+1. Q^i for i≥3 has Picard number one and pseudoindex i. Q^2≅P^1×P^1 has Picard number two, explaining its exclusion from type 2 at actual r.

For E=O^(⊕(i−1))⊕O(1) on P^i, let ξ=c_1(O_(P(E))(1)) and H be the pullback hyperplane class. The projective-bundle canonical formula gives

    −K_(P(E)) = iξ+iH.

Both ξ and H are nef, ξ+H is ample, and every rational curve has positive integral (ξ+H)-degree. Lines in fibers have anticanonical degree i, so this bundle is Fano of pseudoindex i, Picard number two and dimension 2i−1.

For E=T_(P^i), the same formula gives −K_(P(E))=iξ. The tangent bundle of projective space is ample, so ξ is ample; fiber lines have ξ-degree one. This bundle again has pseudoindex i, Picard number two and dimension 2i−1. Multiplying either by (P^(i−1))^(r−2) gives the displayed invariants.

Type 5 has the stated pseudoindex only when at least one P^(i−1) factor is present, hence r≥2. All defect-one types have dimension r(i−1)+1. Type 1 has dimension r(i−1). This proves both completeness and the converse and verifies every boundary convention in fixed-scope.md. ∎

The formulation using actual r also recovers Fujita's version with a lower Picard parameter r_0≤r. If r_0(i−1)≥n−1 and r>r_0, S1 implies (r−r_0)(i−1)≤1. Necessarily i=2, r=r_0+1 and n=r; S1 gives X=(P^1)^r. In Fujita's parametrized list this is Q^2×(P^1)^(r_0−1). Thus keeping actual invariants and excluding Q^2 from the actual-r defect-one list does not omit a case of the named classification.

Author conclusion: the full fixed theorem is proved conditional on the stipulated source input and the stated classical contracts. Independent reviewers must assess both the support/connectivity bridge and its substantiality; no acceptance is inferred from this author's proof.
