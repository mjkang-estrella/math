# Second-pass mechanisms and source/proof depth

All statements and inherited objections are retained verbatim in results.json. This pass does not establish a new exact MathDB solution. The following are mathematical investigations, not accepted discoveries. Original AIM problem bodies remain unavailable; one validated HTTPS request failed hostname validation. No TLS bypass, MathDB request, Palomar request, author contact, browser tab, or upload occurred.

## 385513 — full classification is subsumed by known theorems

Read Monks–Nixon, arXiv:2506.22214v1, definitions of generic configuration, rigidity matrix, rigidity-matroid independence, and 3-sparsity; Theorems 1.2 and 1.3; Section 4.3 opening and Lemma 4.5; the main proof opening and closing core-enlargement argument. Theorem 1.3 states precisely: a 5-regular graph is R3-independent iff it is 3-sparse. Theorem 1.2, attributed there to Jackson–Jordán Theorem 3.5, states for connected graphs with minimum degree at most d+1 and maximum at most d+2 that independence is equivalent to d-sparsity. This is a related actual primary paper; not restoration of the original AIM page or independent reading of Jackson–Jordán's paper. Publisher-version identity not checked.

A complete ordinary bridge for finite simple k-regular graphs:

* For 0 <= k <= 3, every graph of maximum degree at most 3 is 3-degenerate. Insert vertices in reverse deletion order. At each insertion there are at most three old neighbours. In a generic configuration the at most three displacement vectors are linearly independent, so the new rigidity rows have independent new-vertex columns and cannot participate in a row dependence. This proves independence inductively.
* For k=4, work component by component. Every subset of s>=6 vertices has at most 2s <= 3s-6 edges; for s=3,4 the simple-graph edge bounds suffice. A five-vertex subset violates the count only if it induces K5. Since degrees are four, such a K5 is an entire component. Thus every connected component other than K5 is 3-sparse, and Theorem 1.2 applies with d=3; K5 has 10>9 edges and is dependent.
* For k=5, apply Theorem 1.3. If desired, checking 3-sparsity reduces to vertex subsets of sizes 3 through 11: for s>=12, 5s/2 <= 3s-6. This is a criterion, not a newly claimed combinatorial simplification.
* For k>=6, any nonempty component on n vertices has kn/2 >= 3n > 3n-6 edges, so the rigidity-matrix rank bound implies dependence. The empty graph has no rows and is independent, separately.

Independence splits over connected components because the matrix splits into blocks. These four cases settle the literal finite-simple classification by existing results and elementary bridges. No Lean needed for exclusion. No novelty credit. Original graph conventions remain a source-correspondence limitation, rather than an invitation to widen scope.

Proof-depth limit: no independent replay of the millions of base-case computations of Lemma 4.5. The paper reports 7848 connected 5-regular graphs on 12 vertices and 3459383 on 14 vertices, using Nauty and symbolic rigidity ranks. The final proof invokes this lemma to force a minimal counterexample to have at least 16 vertices, then uses reducible pairs and maximal proper cores. Only the indicated main-proof portions were read; not all eleven claims or all dependency proofs. This is an existing stated-and-proved endpoint, not a fresh certified theorem from this lane.

## 385502 — sustain singular construction, then retain global-contact obstruction

Read Connelly–Gortler–Theran, *Rigidity for sticky discs*, published PMC full text: Section 1 packing/flex definitions, Definition 1.4, Theorem 1.5, discussion of nongeneric Figure 3 examples; Definition 2.2 distinguishing ordinary stress from edge-length equilibrium stress; Lemma 2.10 with its proof; concluding proof of Theorem 1.5. The last proof uses the smooth packing space and generic-fibre dimension 2n-m, so generic radii forbid the requested singular rigid example at <=2n-3 contacts. It does not forbid nongeneric examples. In particular the introduction already records nongeneric rigid packings with fewer than 2n-3 contacts. Singular rigidity alone is not a new answer.

Three concrete mechanisms were checked:

1. **Generic-radii shortcut fails.** Genericity gives the all-packings contact bound but also forces rigidity iff infinitesimal rigidity, by Theorem 1.5. Thus this otherwise attractive route cannot produce the requested flex.
2. **Double-tangency insertion can create singular sticky rigidity.** Suppose a rigid, infinitesimally rigid frame of N disks has two disk centres fixed at (-a,0) and (b,0). Insert a disk of radius r centred at 0, with a=R_left+r>0, b=R_right+r>0 and no other overlaps. Its two tangency equations are x^2+y^2+2ax=0 and x^2+y^2-2bx=0. Subtraction forces x=0 and hence y=0: exact local rigidity. Linearisation only forces x'=0, leaving y' free. If the frame has 2N-3 independent contact rows, the enlarged system has n=N+1, m=2n-3 and rank 2n-4. The new disk has one nontrivial infinitesimal flex. Rank-nullity also gives a one-dimensional ordinary equilibrium-stress space. The frame can balance the insertion's opposite collinear loads because these loads annihilate every rigid motion and its rigidity matrix has full rank modulo rigid motions. This is a conditional construction with an exact second-order mechanism, not an exhibited admissible disk collection.
3. **Changing to unsticky jamming or nonspherical particles changes the question.** Read Connelly–Dickinson Section 1.5, Theorems 2–3: fixed-torus strut rigidity is equivalent to infinitesimal rigidity; bar flexes alone therefore cannot certify jammed disks. Read Donev et al., *Underconstrained jammed packings of nonspherical hard particles*, pp.3–4 conceptual construction: flattening contacts blocks rotational modes at second order. This is an existing mechanism for nonspherical particles, not evidence for a new exact disk solution. The record allows objects in general, but an old known construction without the required uniform contact bound is still ineligible.

Precise remaining lemmas for the insertion route: exhibit a disk frame with the required separation and free gap, prove all noncontacts remain disjoint, and prove that **every** packing of the same radius multiset has at most the permitted isostatic contact number. A local rigidity-matrix calculation proves none of the last uniform claim. A codimension-one relation among radii is insufficient: the generic-radii theorem no longer applies, and dimensional heuristics could allow one extra contact elsewhere. The original sticky/boundary/isostatic conventions also remain unverified. Park; do not call the conditional insertion a solution.

## 385582 — actual slab formula/proof, two diagnostics, analytic discriminator

Read arXiv:2603.25643v1, definitions of slices/slabs and width parameter, Theorem 2 discussion, Section 2.2 barycentric chamber construction, Lemma 6 and proof. Its actual proof fixes edge-intersection vertex data in a slicing chamber, uses rational vertex parametrisations and determinants of a fixed triangulation, and extends to chamber boundaries by continuity. This supplies a finite algebraic method, not a theorem that any named direction minimizes. The article's unit norm ball/width conventions are not presumed identical to the unavailable AIM page. Its dimension-four formulas are not asserted to solve the MathDB question. Published-version correspondence not checked.

Work in an explicitly stated diagnostic convention: Q=[-1/2,1/2]^n, unit normal a, total width t, V(a,t)=vol{ x in Q : |a.x| <= t/2 }. For k equal nonzero weights 1/sqrt(k), inclusion-exclusion gives

V_k(t)=2/(k!) sum_{j=0}^k (-1)^j binom(k,j) ((k+t sqrt(k))/2-j)_+^k - 1.

Derivation: translate each uniform coordinate by 1/2, scale the sum by sqrt(k), compute a simplex volume below its sum threshold, and remove all upper-coordinate violations by inclusion-exclusion. The convolution law is symmetric, so a central interval is twice the CDF at t/2 minus one. No Lean volume/convolution bridge is claimed.

First tested the concrete omitted-support hypothesis: in n=5, could four equal coordinates beat all three proposed supports 2,3,5? Decimal evaluation at t=.83,.84,...,2.00 found no strict improvement. Then used the general positive-weight inclusion-exclusion formula (denominator k! product weights) to test the unequal patterns (1 repeated m times,r), m=2,3,4, normalized to length one, r=.05,.10,...,2.00, t=.85,.90,...,1.80. Again no strict improvement beyond 1e-30. Full outputs and both scripts retained. These finite tests neither prove global minimality nor certify exact signs.

An analytic discriminator goes beyond these grids. Perturb the three-coordinate diagonal to a(e)=(sqrt(1-e^2)/sqrt3 repeated three times,e,0,...). On a smooth density chamber, conditioning on the new uniform coordinate and Taylor expansion gives

V(a(e),t)=V_3(t)+e^2[(t/2)V_3'(t)+(1/6)V_3''(t)]+o(e^2).

Indeed scaling the first three weights contributes t V_3'/2; convolution by e U with Var U=1/12 contributes V_3''/6. On 1/sqrt3<t<sqrt3 the corner formula is V_3(t)=1-(sqrt3/8)(sqrt3-t)^3. Thus the coefficient is

(sqrt3/16)(sqrt3-t)[3t(sqrt3-t)-2].

It is negative for t>2/sqrt3 in that chamber. Therefore the three-coordinate diagonal loses transverse local minimality above 2/sqrt3. This does not refute the conjectured global phases: the full diagonal may win already before that point. A viable refutation would need a rigorously isolated t within the **claimed** three-support winning interval and an actual better direction, or a source-scoped failure of the phase structure. Neither is supplied by these computations.

Precise remaining work: restore n, width scale, admissible t range and threshold ordering from the original source; determine the relevant diagonal crossing relative to the stability threshold; certify a counterexample or solve all chamber inequalities. Original-source gap is material, so park rather than formalize the diagnostic formula as a surrogate endpoint.

## 385446 — current registry already supplies the alternative Fourier endpoint

The complete preprint path screen found *A sharp Fourier certificate for planar circle packing*. Retrieved at immutable head 4eaee87548250b2682affda7d05d947c05554bae and read introduction's complete theorem and normalization bridge; signs proposition with its final proof and unbounded-region estimate; certificate section's finite-matrix/residual and Bernstein error accounting. The theorem asserts a real radial Schwartz f on R^2 with fhat(0)=1, f(0)=2/sqrt3, fhat>=0 globally, f<=0 beyond radius 1. This is the standard sharp planar packing auxiliary function, exactly the alternative requested by the literal record. Its density ratio is (pi/4)(2/sqrt3)=pi/(2sqrt3). It is not a proof of A2 universal optimality, and that separate endpoint remains untouched.

Proof-body evidence: the global-sign proposition deduces finite-region signs from certified Taylor quotients and infinite-region signs from a positive .00448 distance-squared margin; multiplying by positive Gaussian factors gives the required physical/Fourier signs. The certificate section records matrix defect <.001, geometric-series inverse bounds and propagated analytic moment errors before Bernstein comparisons. This is proof-section reading, not independent execution of its Arb computations or a complete interpolation/Fourier/normalization dependency audit. Per project instructions, the upstream theorem is accepted as true for exclusion purposes. No need to formalize an already known alternative. The immutable manuscript is dated September 23, 2026, before this pass; its relation to our earlier publications is not independently reconstructed. Original AIM contextual correspondence remains held.

## 385892 — original theorem missing, no invented quantitative target

The original AIM hostname failure applies to this route too; no further same-host request was made. Bounded title/phrase searches did not restore the specific second theorem. General amenable-group sumset leads were not read as substitutes: a piecewise-Bohr/product-set theorem does not identify the missing subgroup in this arithmetic product question. No new primary-body review is claimed. Retain the old obstruction and move on, rather than optimize an unidentified index bound.

## Other 35 IDs

No additional primary-body or proof-body reads. Each keeps the actual old disposition, literal statement, source gap, registry-clearance hold and precise missing mechanism in results.json. They are not reclassified as newly reviewed or newly excluded. The stale reviewed:false routing metadata is not used as a coverage claim.
