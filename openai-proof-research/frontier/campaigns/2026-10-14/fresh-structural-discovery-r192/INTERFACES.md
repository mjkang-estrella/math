# r192 — actual source and primary interfaces

Source316 and all operative proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. This document records their applicability, not a source-truth audit. The twelve canonical blobs authenticate against the complete pinned tree. All eleven text objects were read completely. The compiled PDF was authenticated only.

## The actual sphere statement and its limits

For d>0 the map is h_d:π_d^S=π_d(Q_0S^0)->H_d(Q_0S^0;F_2), induced by the mod-two fundamental class of an actual sphere representative. It is not the ordinary spectrum Hurewicz map π_dS->H_dS. Theorem thm:curtis gives the span of the images of η,ν,σ and of Kervaire-invariant-one representatives θ_j whenever they exist. The source defines the latter by the Arf invariant of the corresponding framed manifold. It does not posit a new Kervaire class.

The full introduction also ALREADY proves finite support in degrees {1,2,3,6,7,14,30,62,126}, using HHR's nonexistence input. This is an upper support bound, expressly not an assertion that each degree is nonzero or an exact image dimension. The separate Lin–Wang–Xu endpoint existence citation is not needed for that bound and is not a new consequence of our work.

For n>0, cor:eccles-spheres describes a nonzero spherical class of QS^n as the bottom e_n or a nonzero n-fold suspension of one of the three Hopf images. Adjunction gives h(f)=σ_*^n h(f_0) for positive excess dimension; Kervaire squares die under the first suspension; π_n(QS^n)=Z supplies the bottom, and connectivity excludes lower degrees. This only treats positive-dimensional spheres. It does not give Eccles for other spaces/manifolds or unstable sphere targets. Prime two supplies Frobenius, binary Steenrod/Dyer–Lashof formulas, parity and Arf detection throughout. Stability supplies the QS tower, stable counit and Adams input. Positive degree excludes component phenomena and the degree-zero Hopf alternative.

## Actual includes, products and weights

paper.tex has 762 bytes and Git blob eb74588690f456774d93e1abbd7b495e56ead5d6. It includes preamble, then introduction, weights, cones, powers, algebra, conclusion, and references.bib. Introduction includes figures/proof-route.tex. The figure summarizes the two terminal cases and explicitly says the root need not be spherical; it supplies no independent lemma. There is no further nested mathematical input or additional same-family blob.

The source distinguishes additive Pontryagin product *, spectrum block pairing ∘, ordinary space coproduct, and the auxiliary linear coproduct. At positive levels the structured reduced free-monoid splitting identifies Σ∞_+C(X) with P(Σ∞X), and for connected X group completion is already an equivalence. Its weight-one projection is the counit. A pointed family using one common suspension coordinate proves weight-preserving suspension, not just unrelated stable splittings.

For a suspension the ordinary coproduct is linear; its weight components are transfers to two-block subgroups. Restriction to regular elementary abelian groups kills proper transfers and identifies primitive duals with M_0(n)=Σ^nF_2 and M_k(n)=Σ^n d_0^nD_k. The proof includes the Dyer–Lashof dimension count, invariant restriction, Thom Euler class d_0^n, and actual ideal inclusion dual to suspension. Polynomial exponent degrees must be combined with the outer shift.

At level zero t=1+u distinguishes the particle from the reduced generator. The source constructs R=Σ∞_+QS^0≃P(S{u})[(1+u)^-1] and maps to each finite weight truncation. Polynomial numerators prove joint detection and independence of leading weight from component translation. The true diagonal is Δu=u⊗1+1⊗u+u⊗u; only the associated leading coproduct is linear. An odd-degree leading functional survives restriction to d_0D_k because D_k/(d_0) is even. These are established operations, not assumptions that the level-zero algebra splits into actual independent space factors.

The suspension kernel is exactly the positive decomposables. Injectivity is into FULL target homology, which retains square words; projecting target to indecomposables would invalidate it. In the polynomial connected Hopf algebra a decomposable primitive has a unique primitive square root; Frobenius and Cartan also preserve Steenrod annihilation of the root.

## Cones and the fourth-power argument

lem:cone-square assumes an actual g:S^(2m-1)->T with h(g)=0 and loop image x². For any square-zero u∈H^mT, its unique extension has square <u,σ_*x>a in the cone. The source proves the universal fiber calculation, uses a convergent cobar argument with connectivity to make the bottom loop square nonzero, and handles connected rather than necessarily simply connected T. The nonzero top relative class follows from h(g)=0.

For T=QS^n, n>0, cohomology is exterior. The source quotient removes square-free products of DISTINCT lifted generators, preserving the possible square equal to a. Cartan and the annihilated detector make this subspace an A-submodule. The resulting extension yields Sq^m⊗v≠0 in I⊗_A M_k(n) whenever the detecting functional sees v. This retains actual realization information, beyond an algebraically possible primitive.

The fourth-power exclusion does not assume the j_i are additive infinite loop maps. The actual correction is J_i(A²)=(J_iA)²+(J_(i/2)A)^(∘2) for even i. Spectrum pairings satisfy a Dyer–Lashof/Steenrod formula; primitive classes with zero stable counit evaluation have triple block product zero. These remove the extra correction at the chosen leading weight. Even Stiefel–Whitney detectors have squares with integral torsion Pontryagin lifts. The cone extension then gives contradictory values of Sq^(b+1)=Sq¹Sq^b for even b. The source explicitly credits earlier higher-square exclusions to Eccles–Zare. No new fourth-power theorem is proposed.

## Algebra and final assembly

algebra.tex proves the exterior quotient B, exact Milnor monomial coinvariants including the floor, and Cartier map

    d_0^c∏d_j^b_j -> d_0^((c+k-2)/2)∏d_j^((b_j-1)/2).

The functional lives at floor n-1, while the nonzero tensor lives at floor n. Repeated halving forces n≡k modulo 2^ν₂(m) and c>=n+2^ν₂(m)-2. The even-total-degree Tor_1 injection uses Laurent projectivity and deletes low-exponent filling terms. The final b=2 case keeps a genuine floor correction, including Sq²(d_0d_2w²) and its explicit q_0-hit error. These are the paid algebraic operations from which DERIVATIONS starts.

The resulting obstruction needs BOTH a nonzero tensor and a lifted annihilated functional. It permits only n=k=1, m a power of two. Odd m>=3 is excluded without the functional hypothesis.

For an actual α, the last nonzero homology suspension exists because H_(d+j)QS^j is zero for j>d between bottom and twice bottom. Its class is w². Positive terminal level uses the preceding spherical suspension and a floor functional to prove |w| odd; terminal zero uses fourth-power exclusion. In either case σ_*w≠0. Cone detection and the algebra obstruction force bottom weight at positive terminal level, yielding d=e and stable Hopf detection via the counit/two-cell cofiber. Adams gives d=1,3,7.

At terminal zero, the root has leading weight two and its square leading weight four. Kuhn's actual Adams-stage lift, followed by the source truncation through seven, annihilates derived eighth powers. Thus the element's Adams filtration is at most two; no equality of weight and filtration is asserted. The even stem and classical Ext calculation identify h_j². Browder's elementwise theorem gives Arf invariant one for this actual element, including the low cases. Odd primary parts are removed using finiteness/convergence, not silently equated with mod-two completions.

Finally, subtract a chosen Hopf/Kervaire representative in that degree. Additivity of the appropriate invariant makes the difference invariant-zero. If its Hurewicz image were nonzero the already proved necessity would force invariant one. Hence the difference has image zero. The chosen representative's image belongs to the image by definition. This proves the span without claiming any new existence/nonexistence or an explicit nonzero formula for every named image. No Brown–Gitler or Mahowald theorem is independently extracted: those operations are not used in the read source proof as a missing license for another family.

## Strongest primary operations actually read

Kuhn, arXiv:1403.7501v3, supplies actual natural lifts I(X(s))->HF_2∧I^(2^s)(X), the TAQ nullhomotopy, and its iterative composition. We read the construction and proof, the suspension compatibility and the Lannes–Zarati discussion. His statements distinguish stable spectrum evaluation from zero-space Hurewicz, and a filtration map from a realization theorem. The arXiv version page identifies v3 as the latest posted version; journal identity is not asserted.

Kuhn–Pereira, final AGT article, supplies the actual derived bar filtration, (I^j)^i->I^(ij), the finite-window arity bound N<=min(ij+n-j,mj), coefficient change, and the proof of the lifting composition. Relevant deferred bar proofs were read; not every underlying model-category theorem was separately reread. These are stronger payments than a mere informal ideal-power analogy.

Hunter, final AGT 2025 article, Sections1–4 and opening of5, supplies the Nakaoka width filtration, its D_k/(perfect squares) quotients, and actual Bousfield tower-detector calculation including which cycles are boundaries. The quotient is by the vector subspace of squares, NOT the ideal generated by them. Its desuspension and unstable Ext were verified against rendered page3323. The J-splitting proof later in Section5 was not read or used. Charts were not independently reconstructed.

Sum, arXiv:2001.02138v5, was read in full. The determinant/derivation proof gives the primitive actions and later recurrence; the paper's initial focus on odd primes does not authorize an odd-primary extension here. Hưng's final six-page CR note was read in full: its partial derivatives, directional integrations, critical elements and their relations show why a single-primitive homology calculation cannot be replaced by a free monomial list. The earlier VIASM note differs in its presentation of critical-element sums and is not substituted for the published version. Its contents were inspected only for identification/version limits, not used to prove a claim.

Giambalvo–Peterson's body could not be retrieved at the surfaced link (direct404; web403). Its construction is credited at the source's read scope; independent full-body reading or complete strongest-literature clearance is NOT claimed. Classical Adams/Browder/HHR and the remaining bibliography are used only through the fully read stipulated source applications; their entire original proofs were not independently read. Exact extents, late reads and failures are private.
