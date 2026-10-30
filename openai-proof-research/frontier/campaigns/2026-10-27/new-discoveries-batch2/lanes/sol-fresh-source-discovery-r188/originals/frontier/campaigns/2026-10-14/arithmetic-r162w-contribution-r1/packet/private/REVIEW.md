# Independent full-scope contribution review r1 — PRIVATE / LOCAL

**Assigned verdict: TECHNICAL, conditional on correctness of the entire unchanged frozen theorem.** This is solely the independent substantial-contribution comparison. It is not a correctness PASS, acceptance decision, campaign-count assignment, priority claim, or authorization to publish. All earlier scopes and dispositions remain unchanged. The parent alone integrates or adopts gates.

The reviewed statement is the existence, for every integer n ≥ 2 and every compact origin-symmetric full-dimensional convex body K, of one C∞ symplectic embedding of the entire open ball B(4) = {π|z|² < 4} into int K × int K°. Frozen statement SHA256: `fb4e7ccbddfb38a0908622f3c166cce9327d1b91cea0df335ec80b332a4f8bff`. The unchanged author proof is 23,212 bytes, SHA256 `54095012312b54b7c3ddeb33ab75ab66cdec950557ef63d3bd9fd39be32957c3`. The complete proof was read, including its proposed parametric lemma and all scheduling and gluing steps. This review does not substitute another theorem or an edited author proof.

## 1. Basis and meaning of the comparison

The pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` and every operative source proof result are stipulated true. I checked applicability and the new compositions, rather than auditing those stipulated results. I authenticated all 55 admitted canonical blobs independently against the complete 13,223-entry tree, including byte lengths, Git blob hashes and SHA256. Authentication is not semantic reading or a mathematical gate.

For precise local citations below, S is *Symplectic Balls in Symmetric Polar Products*, G is *The Mahler Conjecture for General Convex Bodies*, and M is *The symmetric Mahler conjecture and its equality cases*, all September 22, 2026 at that pin. The exact selected copies are under `inputs/packet/private/canonical/preprints/` in this private directory. A is `inputs/packet/private/author-proof.md`. The six primary sources are the exact versions under `inputs/packet/private/primary/`, not later versions inferred from current titles. The machine-readable reading ledger records original paths and exact line/byte extents; the reading record explains partial reads and recovery. Neither an author reading ledger nor an admission summary was used as independent proof evidence.

The strongest reduction here is **explicit arbitrary-body source formulas plus a parameterized version of their own construction plus the actual compact-trace Hamiltonian gluing proof**. It is substantially stronger than the headline “width equals 4.” Separate subcritical embeddings, without compatible paths, do not imply critical open-ball attainment. Conversely, the fact that compatibility needs several pages is not a nonroutine operation by itself. The question is whether compatibility calls for a new theorem or mechanism after the formulas have been used at their full strength.

My answer is no: the mixed powers and moving rows preserve the very inequalities and strict injectivity used in S; a tail choice orders the finite approximation and exponent parameters; the parameterized Moser choices lie in open, one-sided sets of admissible scalar values; enlarged source balls give the exact compactness needed by the paid primary gluing argument. The integrated derivation in Sections 4–7 below closes this comparison at the full frozen scope. No residual is parked as an unproved “endpoint bridge.”

## 2. All three Source087 companions and their actual interfaces

### 2.1 S: planar estimates, ball construction, realization and arbitrary bodies

I read the actual wrapper, all six included sections, and the nested planar figure wrapper and image. In `planar.tex`, the inverse conformal lens coordinate g is defined on a bounded lens D with imaginary coordinate in (−1,1) and horizontal sections containing the imaginary-axis point. The signed horizontal primitive J_k has

    ∂a J_k(a,b) = k² |g(a+ib)|^(2k−2) |g′(a+ib)|² ≥ 0,
    |J_k(a,b)| ≤ k[(π/4)|g(a+ib)|^(2k) + ε_k],   ε_k → 0.

The uniformity in the planar argument includes the tips. The proof changes from the horizontal coordinate to the disk radius, splits away from and near the outer radius, and bounds the endpoint integral uniformly before taking the exponent large. This is a uniform tail estimate; there is no restriction to a prechosen compact part of D. That distinction is what allows the author to choose exponents after the next finite row count.

In `ball.tex`, a finite holomorphic tuple with isolated common zero and vanishing order at least k gives a ball of every capacity below πk in the form ddᶜ(|z|²+τ) on {τ<1}. The operative proof uses a convex cutoff of log τ, glues a radial logarithm by a regularized maximum, uses a compactly supported Moser field, and inverts an explicit radial map. The strict capacity loss supplies room for the choices. This is not merely an existence citation whose dependence on parameters is inaccessible. The complete construction displays the quantities that have to vary smoothly.

In `realization.tex`, the holomorphic potential is built from finitely many real linear rows. The momentum map is the sum of the corresponding J_k primitives. Its pullback form is computed term by term. For a fixed position coordinate, its real-coordinate derivative has a strictly negative identity term plus negative semidefinite row terms. Consequently it is globally injective on each fiber, without requiring the potential sublevel fiber to be convex. The fixed lens horizontal interval is the domain on which the monotonicity comparison takes place.

In `approximation.tex`, finite spanning polar rows approximate every symmetric convex body from outside, with K ⊂ K′ ⊂ λK for arbitrary λ>1. Support-function bounds keep the momentum in a controlled multiple of the polar of the **same K**. This is an arbitrary-body mechanism, not a passage restricted to smooth bodies or a cube normal form. The scalar source/target rescalings cancel their conformal factors. S already pays all subcritical embeddings, the same-body approximation, strict injectivity and width 4 as a supremum. Its historical section and introductory limitations do not add an endpoint theorem on their own.

### 2.2 M: geometric equality and functional limits

I read all actual included mathematical sections: convex preliminaries, lens, holomorphic mass, feasibility, simplex, median and zero-deficit arguments, and the introduction carrying the functional statements; both nested images were inspected. The geometric statement is |K||K°| ≥ 4^n/n! for every symmetric convex body, with equality exactly the invertible linear images of Hanner polytopes.

The proof mechanism is relevant to the comparison of what Source087 already pays. The concave lens boundary function and its uniform boundary law feed the high-power holomorphic construction. The isolated-zero mass bound comes from the actual Stokes/homogeneous-flux and determinant calculation. The high-power limit and upper-Fatou argument produce the simultaneous projection feasibility inequality. The simplex integral and its nonnegative deficit convert feasibility into the sharp volume bound. Equality is treated by the zero-deficit mechanism and the segment lift: the lifted body and its polar product yield a simultaneous representation, the endpoint lens law gives the limiting coefficient, and support separation implies the metric median/three-ball property used for the Hanner classification. These are paid geometric results, not a new contribution of A.

The functional statement is for proper lower-semicontinuous even convex φ with 0 < ∫e^(−φ) < ∞, allowing the dual integral to be infinite, and gives the sharp product bound 4^n. The argument uses an all-dimensional geometric-to-functional limiting implication with additional dimensions. It does **not** transport the geometric equality classification through that limit. The further entropy statement assumes full-dimensional log-concave probability measures symmetric about the origin, proper lsc convex potentials and essentially continuous densities (zero at almost every support-boundary point for the (n−1)-dimensional Hausdorff measure). It concludes finite first moments of the gradient-pushforward moment measures, finite entropies, and H(η₁)+H(η₂) ≤ −n log(4e²)+T(ν₁,ν₂), where T is the infimum of the sum of convex-conjugate integrals and may be infinite. These are not a functional equality classification. I do not infer functional equality cases or use a volume equality to infer surjectivity of a symplectic embedding.

### 2.3 G: general sharp geometry, equality and functional bounds

I read the wrapper and abstract, the entire sequence `00-introduction.tex` through `09-consequences.tex`, including all 1,012 scalar-appendix lines and all 1,196 segment-appendix lines, and the proof-map figure source. The general sharp geometric statement is |K||(K−s(K))°| ≥ (n+1)^(n+1)/(n!)², with equality exactly for simplices.

The actual chain passes from cone Laplace transforms to biased Moreau projections, their Gaussian covariance and simultaneous-coordinate normalization, then to the entropy/quadratic estimate and the layer defect. The derivative matrices are not initially assumed nested or commuting. The spectral pair measure and strict scalar/segment inequality control that defect. Equality forces the simultaneous diagonal/orthant structure giving the simplex. The scalar appendix supplies the finite rational and interpolation bounds; the segment appendix covers short intervals, tails, middle widths and large widths, with positive polynomial coefficients and strict budget margins. I read those arguments and their seams; I did not rerun their computation programs or treat their outputs as an independent proof gate, since their operative results are stipulated true.

The general functional statement is for proper lsc convex φ with 0 < ∫e^(−φ) < ∞, without evenness, giving the product lower bound e^n (again allowing an infinite dual integral). The all-dimensional limiting route does not classify functional equality cases. The translated polar/infimum in the geometric input cannot silently be replaced by a claim about a unique functional extremizer. Its entropy consequence assumes full-dimensional log-concave probability measures with proper lsc convex potentials and the same essential-continuity condition, without symmetry. It concludes finite moment-measure first moments and finite entropies, with H(η₁)+H(η₂) ≤ −3n+T(ν₁,ν₂). Neither companion supplies an arbitrary-body symplectic embedding merely from its sharp volume bound. Their substantial paid content is preserved rather than being credited anew to the endpoint assertion.

## 3. Actual primary comparison, with scope restrictions

**Pelayo–Vu Ngoc, arXiv:1210.1537v2, `arxivPeVNnew.tex`, lines 549–777, bytes [20808,30075).** I read the complete operative section “Families with singular limits and Hamiltonian dynamics,” including its proof, through the next section boundary. This is the essential primary operation. A smooth target-contained family on nested simply connected source domains, with relatively compact trace on finite parameter intervals, supplies compactly supported Hamiltonians matching consecutive embeddings on smaller domains. The inverse corrections are composed so the corrected maps agree exactly on successively larger domains. The resulting embedding is locally a finite composition; no convergence of derivatives of the original maps is required. A bounded trace in ambient Euclidean space would not suffice for a nonclosed target: A supplies compactness **inside** U_K using larger source balls. I rely on the operative compactness hypothesis, not an overbroad reading of a boundedness remark.

The extra lines 968–1008 in that paper state an area-Moser consequence in a surface construction. They were read as supplementary context, not as a proof of a general parameterized Moser theorem. The essential parameterization here is derived from S's displayed construction in Section 6 below.

**Pelayo–Vu Ngoc, arXiv:1304.5250v1, `CylindersPeVNApril4-2013.tex`, lines 240–295 and 740–793.** The smooth-family definition/gluing interface and the final cylinder-limit argument were read. The latter normalizes a family and uses the previous gluing mechanism. Its specific spiral/surface construction is not an arbitrary convex-polar-product construction, and it is not an independent compact-subset-to-embedding principle. I did not read the whole spiral proof or invoke it. The exact local version is v1; the author's recorded v3 access failure is not evidence of a nonexistent theorem in another version.

**Ramos–Sepe, arXiv:1710.01753v1, `polybilliards.tex`.** I read the hypotheses and toric interface at lines 148–365 and the full operative Section 3, lines 631–1917, with the following commented appendix boundary. A balanced open bounded region A contains the coordinate box of every one of its points. The theorem constructs a symplectomorphism B∞^n ×_L A ≅ X_(4|A|). Its proof regularizes the one-coordinate strip using H_ε(x,y) = (y² + ε/(1−x²))/2, obtains the action integral

    I_ε(c) = 4 ∫[0,sqrt(1−ε/(2c))] sqrt(2c−ε/(1−x²)) dx,
    I_ε(c) → 4 sqrt(2c),

passes to products and toric coordinates, and uses balancedness to arrange compact exhaustions and isotopy-extension corrections. The whole operative construction, not just the statement, was read. For A=B1^n it already gives the cube/crosspolytope critical open ball, with a stronger surjectivity conclusion. But coordinatewise balancedness and the cube factor do real work; a general K cannot be inserted into that theorem by replacing a symbol. S supplies the general-body row construction instead. The action-angle, normal-form and isotopy-extension antecedents cited by this comparison paper were not all independently acquired. They are not essential unverified dependencies of the integrated reduction here, which uses the directly read 1210.1537v2 gluing proof.

**Karasev, arXiv:1902.08971v3, `hyperplane-mahler4.tex`, lines 228–321.** The complete relevant ℓp section and its Alexander remark were read. For 1<p<∞, with conjugate exponents, the separable Hamiltonian 4 max(|q|^α,|p|^β) is regularized to a strictly convex area-normalized model; its planar maps and products yield all subcritical balls with controlled concentric images. This is a strong explicit special-case construction. Its Alexander family h_t=t^(−1)φ(tz) is an ambient symplectic isotopy, but arbitrary target containment does not follow. It does not pay a prescribed-prefix theorem in a general polar product. The present reduction uses its own same-target family and the paid compact-trace gluing operation, not that invalid inference.

**Vicente, arXiv:2505.07572v2, `main.tex`, lines 89–622.** The actual mathematical body, including the enlarged-target embedding proof, was read, not just the abstract. The construction is separable in a tuple of Young functions. Its functional dual body must be distinguished from the geometric polar; Young's inequality gives a factor-2 comparison, producing a √2 enlargement and the corresponding reduced polar-product lower capacity, whereas the functional-product capacity has the factor 4. These distinctions prevent promotion of a special functional product result to the exact arbitrary-body theorem. The displayed embedding statement has B^4 notation while the proof uses 2n dimensions; I record that notational limitation without silently treating it as a general arbitrary-body theorem. None of this is an essential step in the integrated reduction. Illustrative dual/polar figures were inspected and do not supply a proof beyond the text.

**AAKO, arXiv:1303.4197v2, `main.tex`, lines 257–340 and 866–995.** I read the exact capacity interfaces and the final proof. The billiard mechanism pays c_HZ(K×K°)=4; paired supporting slabs give the cylinder upper bound. These are not lower ball-embedding constructions, and equality of those capacities alone is not an attainment theorem for Gromov width. Earlier billiard lemmas and their ancestors were not all reread and are not invoked to manufacture a lower embedding. S already includes the relevant capacity comparison among its stipulated results.

Thus the strongest arbitrary-body input is S, augmented by the actual general gluing proof. The other primary constructions show why endpoint attainment and exhaustive gluing are established mechanisms, but none is falsely generalized across its geometric hypotheses.

## 4. Integrated derivation I: interpolate the actual source models

Fix any K in the frozen scope. The review is pointwise in K; it does not ask for continuous choices as K varies. Take the source lens D and g, and finitely many spanning rows b_i∈K°. Set ℓ_i(z)=b_i·z, Ω={ℓ_i(z)∈D for all i}. For an integer k≥2 and 0≤θ≤1 put

    τ = Σ_i [(1−θ)|g(ℓ_i)|^(2k) + θ|g(ℓ_i)|^(2k+2)].

Use θ=sin²α and the holomorphic tuple (cosα g(ℓ_i)^k, sinα g(ℓ_i)^(k+1)); this avoids nonsmooth square roots at interpolation endpoints. The tuple's common zero remains zero because a fixed spanning list is retained. Its order is at least k. The scalar inequality

    r^(2k+2) ≤ (1−θ)r^(2k)+θr^(2k+2),   0≤r<1,

puts each row of every sublevel τ≤s<1 in the compact lens subset g^(−1)(closed disk(s^(1/(2k+2)))). The spanning rows bound z. This is a direct convex-combination extension of the source formula, with **unit total coefficient on each row**, not an assertion that arbitrary weighted sums preserve boundary properness.

Likewise put J=(1−θ)J_k+θJ_(k+1), and

    Φ(u+iv) = (v, −u − Σ_i J(b_i·u,b_i·v)b_i).

The source pullback identity is linear in the row potentials, so Φ*ω₀=ddᶜ(|z|²+τ). For u₁,u₂ in a fixed v-fiber, the source horizontal interval permits every scalar monotonicity comparison and gives

    (p(u₂)−p(u₁))·(u₂−u₁) ≤ −|u₂−u₁|².

This pays injectivity on all fibers, including disconnected sublevel fibers. Nondegeneracy then gives an embedding. No new global inverse theorem or equality-case classification is required.

Retain one initial spanning list forever. Boundedness of its lens domain gives C≥h_K(−u) independent of added rows and exponents. Since h_K(±b_i)≤1, subadditivity plus the source estimate gives

    h_K(p) ≤ C + (π/4)(k+1)τ + m(k+1)max(ε_k,ε_(k+1)).       (1)

All these estimates concern the **same** τ and Φ, so there is no mismatch between a ball-producing potential and a momentum-bounding potential. This is the relevant compatibility test. A failed naive interpolation of embeddings would not negate this direct formula interpolation.

For a new row b, use b(t)=r(t)b with a smooth flat ramp from 0 to 1. Intermediate vectors remain in K°. At r=0 its potential and momentum vanish and the row imposes no restriction; old spanning rows remain. Full row coefficient is maintained as the vector moves. A disappearing coefficient on a fixed boundary row could destroy compactness of its sublevels, but that is not the operation used here.

On any compact parameter interval only finitely many rows and exponents occur. An upper bound L for their powers puts every row image of τ≤s into one fixed compact subset of D. The old spanning list bounds z. Limits of such pairs (t,z) stay inside the total open row domain, including at a zero-row birth. Consequently these are compact sublevels in the **joint** domain, exactly the support condition needed later. This follows from finite-dimensional compactness and the displayed inequality, not from an additional compactness theorem about spaces of symplectic embeddings.

## 5. Integrated derivation II: all-body approximation and the full tail schedule

Choose nested finite polar lists B_j whose strip bodies K_j satisfy

    K ⊂ K_j ⊂ λ_j K,   λ_j=1+2^(−j),   η_j=2^(−j).

Successive unions preserve the source approximation and spanning property. Let m_j be their lengths. First fix the next finite count m_(j+1), then choose strictly increasing integers k_j≥max(4,j) such that **every** integer l≥k_j satisfies

    C + m_(j+1)(l+1)max(ε_l,ε_(l+1)) < (π/4)η_j(l+1).       (2)

Existence follows by dividing by l+1 and using the actual uniform ε_l→0. A bound at only k_j would not pay the intervening exponent steps; (2) is the full tail statement. It requires no rate or bound uniform in K, precisely because the frozen theorem has no such assertion.

Within a unit-length stage j: birth the next rows at power k_j while retaining λ_j and η_j; decrease λ only after all those rows have arrived; traverse the finitely many adjacent integer powers by the mixture above; then decrease η at pure power k_(j+1). The last decrease uses the next tail condition, which allows at least the current row count. Flat ramps make all junctions smooth. Arbitrarily many but finitely many steps in a stage are harmless: stage endpoints escape to infinity, so no finite-time accumulation occurs.

During a pure k phase set h=k+1; during l-to-l+1 interpolation set h=l+1+θ. These agree to all orders at the flat junctions. Set

    S=(π/4)(1+η)h,    κ=h−3.

The safe lower order κ is positive and stays below the smallest active integer holomorphic order with a spare unit locally, including at endpoints. Thus locally uniformly τ_t(z)≤C_I|z|^(2κ(t)) near zero. Equation (1) and (2) give h_K(p)<S on τ<1; the positional inclusion is int K_t⊂λ(t) int K. This is a simultaneous budget for all four parts of every stage, not just an estimate at the stage endpoints.

Finally

    d(t)=πκ/(λS)=4(h−3)/(λ(1+η)h) ↑ 4,
    c(t)=d(t)(1−1/(t+2)),
    c₊(t)=d(t)(1−1/[2(t+2)]).

Here 0<c<c₊<d, c is strictly increasing, and c→4. All n≥2 and all nonsmooth K are covered by the same finite-net argument. No smooth approximation of K requiring an additional limiting embedding is hidden in this stage.

This schedule is a diagonal choice of an integer tail after a finite row count, together with scalar monotone ramps. It is real work in the exposition, but it is paid by the uniform source error and elementary parameter choices. It supplies no independent new analytic estimate beyond them.

## 6. Integrated derivation III: parameterized source Moser construction

It would be insufficient to say “Moser is parametric” without checking the supports and choices. Here the actual source construction makes that check possible. Set a(t)=λ(t)S(t)c₊(t)/π<κ(t), b=(1+a/κ)/2 and μ=(a+bκ)/2, so a<μ<bκ. Use the source logarithmic cutoff H_t=χ_t(logτ_t), with slope b near −∞ and agreement with τ_t above a smooth sublevel s₀(t)<1. The same derivative inequalities make χ increasing and convex, hence H plurisubharmonic off zero, with the local bound

    H_t(z) ≤ b(t)κ(t) log|z|² + C₁.

Choose an outer radius r₂ with its closed ball inside {τ_t<1}. Choose a large smooth M so P=μ log(|z|²+δ)−M is below H−2 on that outer sphere, for every 0<δ≤1. Then choose r₁<r₂ **before δ**. Since μ−bκ<0 with a locally uniform strict margin, P−H>2 for 0<|z|≤r₁, uniformly in such δ. Last choose 0<δ<min(1,r₁²(μ/a−1)). These choices can be made smooth along the ray: locally valid positive radii have downward-closed admissibility; M has upward-closed admissibility. A locally finite partition of unity combines the valid constants while preserving the corresponding one-sided constraint, after earlier choices have been fixed. Compact spheres give continuous extrema; no selection from disconnected spaces of embeddings is involved.

The source fixed regularized maximum glues H and P. The strict annular comparisons remove all moving-radius seams and make the new potential H̃ jointly smooth. Choose σ(t) between max(s₀,max_(closed B_r₂)τ_t) and 1. The change H̃−τ is supported in τ≤σ. On every compact parameter interval the maximum of σ is strictly below 1, so Section 4's joint sublevel compactness gives one compact support inside the total open domain.

Interpolate ω_(t,s)=ddᶜ(|z|²+(1−s)τ_t+sH̃_t) and solve

    ι_Y ω_(t,s) = −dᶜ(H̃_t−τ_t).

The Euclidean term makes the forms positive and nondegenerate. The field extends smoothly by zero outside each moving sublevel domain: locally in t its support is separated from that boundary in the total domain. On compact t intervals it has bounded spatial support and derivatives. The ordinary parameter-dependent ODE theorem then supplies its s∈[0,1] flow smoothly in t. This is the same compactly supported Moser operation as S, with its support checked, not an unverified global parametric embedding theorem.

On the inner ball the radial map is R_t(z)=sqrt(1+μ/(|z|²+δ))z. Its squared radial function x+μx/(x+δ) has derivative 1+μδ/(x+δ)²>0, so the inverse is jointly smooth, including at zero. The δ choice ensures that its image contains B(πa). Composing that inverse with the inverse Moser map gives E_t on B(λSc₊) with E_t*ddᶜ(|z|²+τ_t)=ω₀.

Thus every essential operation of A's parametric lemma is either the paid source construction or a local strict-choice/ordinary smooth-ODE consequence of it. No uniform bound for all t is required. The potentially troublesome changes of domain and integer order have already been handled by joint compactness and the spare order in κ.

## 7. Integrated derivation IV: one map on the entire open ball

Define T_t(q,p)=(q/λ,p/S), D_t(z)=sqrt(λS)z and

    f_t = T_t ∘ Φ_t ∘ E_t ∘ D_t : B(c₊(t)) → U_K.

The strict positional and momentum bounds give the same fixed target U_K, even when K has nonsmooth boundary. The conformal factors of T and D cancel; together with the pullback identities above this gives a smooth family of symplectic embeddings. The derivation concerns that family, not unrelated choices for each c<4.

For a compact time interval I the set Q_I={(t,z):t∈I, π|z|²≤c(t)} is compact and lies inside the total domain π|z|²<c₊(t), since the continuous gap has a positive minimum on I. Its image under (t,z)↦f_t(z) is a compact subset of U_K. This is the actual finite-interval compact-trace hypothesis of the primary gluing proof. No boundary extension at c=4 and no common compact support for infinitely many times is asserted.

For clarity the final paid gluing operation can be derived directly. Put V_j=B(c(j)) and e_j=f_j|V_j. On a fixed source ball B(r′), with c(j−1)<r<r′<c(j), the path j≤t≤j+1 has velocity X_t along its image. Differentiating f_t*ω₀=ω₀ shows α_t=f_t*(ι_Xω₀) is closed. Its radial primitive is A_t(z)=∫₀¹α_t(sz)[z]ds. With convention ι_Xω=−dH, use H_t=−A_t∘f_t^(−1), multiply by a transported source cutoff equal to 1 on B(r) and compactly supported in B(r′), and extend by zero to U_K. The compact-trace property makes the finite-time Hamiltonian flow complete inside U_K. It agrees with the given path on V_(j−1).

If ψ_j is its time-one inverse, then ψ_j∘e_(j+1)=e_j on V_(j−1). For z∈V_(n−1), define F(z)=ψ₂∘⋯∘ψ_(n−1)∘e_n(z). These definitions agree on overlaps by that identity. Their domains exhaust B(4). Near each point F is exactly one finite composition, hence smooth and symplectic. Any two points lie in a common finite stage, where injectivity holds; being a local diffeomorphism, F is an embedding. This is attainment by a single map on the entire **open** critical ball, not a limiting map asserted from a supremum. It is exactly the previously paid gluing mechanism applied to the compatible source family.

## 8. Old mechanisms, conditional limitations and the assigned verdict

The exact original i38 excerpt concerns geometric stability from a local remainder and fixed-dimensional compactness, not functional equality transfer. The exact i70 and i74 excerpts preserve the old prescribed-prefix relative packing scopes. They already explain why a genuine target-contained path can be Hamiltonianized and why a generic Alexander path can leave a target (including the explicit polynomial shear example). The later restricted linear-shear and derivative-controlled mechanisms do not solve the old unrestricted prefix problem. Here no prefix is prescribed: one chooses a family from the start, and the local finite corrections need not preserve any arbitrary initial embedding. Nothing in this review changes those older scopes or dispositions. No linked review, metadata or other history body was followed.

The possible superficial reasons for SUBSTANTIAL do not survive this comparison. Endpoint attainment is not alone a contribution criterion; all-body scope is already present in S's row and polar formulas; and failure of a weighted-row or uncontrolled Alexander shortcut does not rule out the compatible construction above. Conversely the comparison has not collapsed all endpoint questions into routine limits: it explicitly supplies the needed family, compact support and exact stabilization.

**Decision: TECHNICAL, conditional on correctness of the unchanged full theorem.** The residual proposed by A is fully accounted for by a compatible composition and smooth parameterization of the actual source construction, an elementary tail schedule and the actual primary Hamiltonian gluing proof. I find no essential closed nonroutine operation unpaid after this reduction. There are no remaining essential contribution-comparison obligations and no required author repairs proposed by this review. This is not the separate correctness verdict, and nothing here replaces that review.

The comparison is scoped to the supplied sources, the six exact primary versions and three exact original-history excerpts, with limitations stated in `READING-ISOLATION-LIMITS.md`. It is not an exhaustive literature or project-history clearance and makes no worldwide-priority assertion. Protected bodies and their named metadata remain private/local under their original rights. The author's freeze chronology is reported as such; neither chronology nor the author FINAL/REPORT proves correctness, novelty or independent reading.
