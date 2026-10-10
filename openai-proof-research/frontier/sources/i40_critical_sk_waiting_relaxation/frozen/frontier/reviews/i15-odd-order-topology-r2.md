# I15 resumed odd-order topology: independent proof review R2

**Verdict: PASS, relative to the stipulated pinned corpus.** The complete construction, including the six-tip geometric extension, the exact cyclic manifold-model spectrum, and Theorem 10.1's exclusion of every representing homeomorphism, passes this review. I found no proof-blocking gap. This is not merely a PASS for the conditional height lemma. Section 8 below gives precise quotient-level wording for one compressed sentence; the required argument is supplied without an additional hypothesis or a change of construction.

This does **not** accept the candidate as a substantial finding, certify literature novelty, or change the count. The four accepted findings remain R006, R008, R009, R010. I07's independent proof PASS and subsequent technical-only judgment remain intact. Significance of this new mechanism belongs to the separately requested round.

The audited candidate is `frontier/iterations/i15-odd-order-topology-resumed.md`, **477 lines**, SHA-256 **`98c1af96f05ba27ba56598e6422fb621627828357226267aaf2c1a5c24d66874`**. I read the complete revised report, complete interrupted original, complete I07 proposal and both specified reviews, AGENTS.md, the original task JSON, resumption task JSON, and retained resumption brief. Historical counts and pauses in those inputs do not override the present brief. The [full R2 brief](../sources/i15_odd_order_topology_r2/review-brief.txt) is retained.

The exact conclusion reviewed is the existence of a **closed connected oriented aspherical topological four-manifold** M with an injected C3 in Out(π1 M) whose intersection with the image of Homeo(M) is the identity. A prospective representing homeomorphism may have infinite order and either orientation. The construction also proves that Q_d has a closed topological four-manifold model exactly when 3 divides d, for every positive integer d. No finite-action-only substitute, higher-dimensional stabilization, or arbitrary-law geometric realization premise is used.

## 1. Premises, source reading, and provenance

The immutable premise is every applicable result of `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. I checked applicability of the imported results and the new deductions; I did not audit upstream truth or use external literature to challenge that premise.

The following manuscript abbreviations refer to `build/` inside the indicated pinned directories under `preprints/`:

- **B:** `Nonhomeomorphic-closed-aspherical-four-manifolds-with-the-same-homotopy-type-October-4-2026/`.
- **MT:** `A-marked-tensor-obstruction-to-four-dimensional-disk-embedding-September-24-2026/`.
- **PD:** `A-PD4-group-without-an-aspherical-manifold-model-September-24-2026/`.
- **BO:** `A-boundary-only-obstruction-to-four-dimensional-disk-embedding-September-24-2026/`.

I compared the candidate with the **complete** B chamber, formal, and reflection sections and its complete cyclic-criterion proof; B's actual assignment theorem; MT's marked-annulus, placement, framing and exterior-dual proofs; its based edge slice, marked algebraicity, trace-comparison statement, residual correction, adjoint-span and product-ideal proofs; PD's complete chamber section, including side markings and topological cuts; and BO's actual main theorem and framed-ribbon/stage construction. Main statements of all four were read. These source proofs, not the candidate's summaries, determine the permissible extensions.

The [source contracts](../sources/i15_odd_order_topology_r2/source-contracts.json) retain all 149 exact extracted statements, including labels, immutable raw URLs, line ranges and hashes. The [source proof passages](../sources/i15_odd_order_topology_r2/source-proof-passages.json) separately retain 17 explicitly scoped passages inspected for this review. Retaining the 149-statement inventory is not a claim to have audited the proofs of all 149 statements. B `refl:input` is itself an accepted general chamber theorem; its upstream assembly and controlled-removal proof need not be re-proved here.

The independent [audit](../experiments/i15_odd_order_topology_r2/audit.py) verified:

- 403 live dependencies against R2 byte snapshots; the reviewed report has the supplied hash.
- All 253 cached pinned TeX/BibTeX files against size, SHA-256, exact pinned raw URL and independently calculated Git blob SHA-1 in the complete inventory.
- The complete, untruncated inventory: 13,223 entries, 10,373 blobs and no duplicate paths.
- All 149 original and resumed contract records against actual source lines, labels and hashes.
- All 324 old dependencies and all 69 resumed sealed artifacts against the resumed seal.
- All 23 successful resumed retrieval records and all 22 retained primary-text records with their 29 exact passages against retained bytes.

These results are recorded in [audit-results.json](../sources/i15_odd_order_topology_r2/audit-results.json). Literature passage identity verification is not a fresh novelty review or a claim to have independently reread all 22 primary texts. No new literature retrieval was needed to settle the correctness interfaces in this round. The complete 9,340-text broader cache was not needed and was not modified. The old report's historically missing seal/reading-index claims are not treated as evidence; the present proof review has its own seal.

## 2. Complete hypothesis and dependency ledger

The following ledger distinguishes actual imported contracts from the new work. All entries were checked, rather than treating acceptance of the last height lemma as acceptance of their premises.

1. **Finite uncolored plumbing input.** MT's plumbing construction and B `ch:plumbing-chart`, `ch:plumbing-group`, `ch:outside-piece` require product-framed mutually paired cancelling handles, no self-plumbings, free extra loops, and exposed unlink exteriors. Candidate §5 uses m=30, p=9 with exactly that chart. Port colors alter only the finite installation list. The unplumbed block and its tree development are unchanged. **Met.**
2. **Marked six-tip thickening.** B `ch:four-tip-model` is only a four-tip statement; MT `lem:marked-body` supplies the old-primitive-annulus operation and its marked disk-system proof. Candidate Lemma 4.1 repeats that operation at two disjoint terminal annuli and carries the entire lower surface. Section 3 below verifies this new step, including the root marking. **Met by new geometric argument, not by `ten:assignment`.**
3. **Finite placement, paths and frames.** Six distinct ports per body, a finite list, independent exterior paths and individually primitive terminal annuli are needed. Candidate (3)–(4) installs every independent conjugator/sign choice with separated tracks and fixes the initial link only after transport. **Met.**
4. **Three-way framed compression.** MT `lem:exterior-duals` gives one-sided contraction and its inherited outgoing frame. It must be iterated, not merely cited with a six-tip conclusion. Candidate Lemma 4.2 performs one or two such operations, using 2 or 4 terminal cap sheets. Section 3 verifies the iteration and selected-family quantifier. **Met.**
5. **Based Brunnian word.** The root must be a word in the six installed tips, trivial upon deleting any one, with a nonzero specified degree-six initial tensor; internal basings may not introduce an independent extra generator. Candidate Lemma 4.3 follows from the five punctured-torus commutators and transported marked handlebody. **Met.**
6. **Side-marked exterior.** PD/B `ch:exterior-model` needs actual proper boundary pushes and their product trivializations, not just abstractly nullhomotopic surfaces. Lemma 4.1 supplies these. Both bottom generators die in X. The cofiber therefore gives H free on 30 plumbing loops, nine extra loops and k normal circles, and exactly 2k sphere summands. **Met.**
7. **Algebraic duals in the exterior.** B `ch:exterior-duals` requires equal group labels for opposite inner sheets before bottom normal circles are killed. Candidate §5.1 selects shallow caps and replaces the old unused-cap nullhomotopy by the W contraction inside E. Section 4 checks the difference loop and fixed outer index. **Met.**
8. **Full middle basis and full framed Wall invariant.** B `ch:poincare-chamber` needs all 2k generators, a group-ring hyperbolic basis and zero full framed self-intersections. Candidate §5.2 checks even identity diagonal coefficient, absence of nonidentity involutions in H, direct finiteness and the identity coefficient of μ. **Met.**
9. **PD pair and boundary surjectivity.** Three-cells attach on that whole basis; regular-coefficient cap-product duality descends to all local systems; graph type gives π1 S onto H. The source's algebraic argument uses exactly the data just verified and is unchanged by upper-stage depth. **Met.**
10. **All lifted chambers.** Each replacement's image under w is zero, so the individual bodies and their normal circles lift; restriction of scalars gives d copies of each basis sphere; the Wall projection retains identity and inverse pairs. Boundary surjectivity makes S_d connected. **Met for every d≥1.**
11. **Positive marked filling.** Every branch contains one tip of the selected color; no plumbing has two selected ends. The embedded framed hyperbolic pairs exhaust the whole middle module. Interior replacement by balls preserves boundary and group marking; the lifted Mayer–Vietoris calculation gives an aspherical graph-type filling and a map equal to identity on S_d. **Met whenever 3 divides d.**
12. **Undoing surgery and connected cuts.** B `for:cuts`/PD chamber construction needs dual handles on the specifically marked lifted normal-circle free factors, a graph-type W_d, a compatible map to the universal plumbing tree, and cocore disks protected in vertex pieces. Candidate §7.1 retains these data; the connected-component-tree proof tolerates 30 types and d=2. **Met for d≥2.**
13. **Linear and smooth/formal cut inputs.** The cut is a compact smooth oriented connected three-manifold with one torus boundary; vertices use filled punctured forms. H²(W_d)=H³(W_d)=0, b1(W_d)=38d+1, and the 9d extra-loop evaluations identify the degree-one kernel. The two longitudes force a coordinate boundary line. **Met.**
14. **Mixed-endpoint formal data.** B `for:edge-input`, `for:vertex-identities`, MT's based slice, and marked algebraicity require full Artinian flat quotients, torus-identity gauges, common central edge coordinates, exact polarized boundary cancellation, injective tangent maps and a unit full-column residual-gradient minor. Candidate §§7.1–7.2 retains each; colors and arity are unused in these steps. **Met.**
15. **Six-slot actual ideal.** Independent logarithm blocks, all independent external adjoints, Brunnian higher terms, vanishing at the recentered origin, and disk relations in the actual flat quotient are required. Candidate §7.3 supplies them; Section 5 verifies Nakayama and the quotient-interface wording. **Met, including full mixed nilpotents.**
16. **Final tensor-assignment hypotheses.** B `ten:assignment` already allows arbitrary nonempty local edge sets on a finite loopless multigraph. Candidate has six distinct edges per law even at d=2, algebraic germs over C((σ)), centered formal graphs, injective transverse central tangents, exact zero potentials and memberships in actual restricted gradient ideals. The nilpotent correction preserves them. **Met.**
17. **Negative spectrum and degree one.** The assignment forces singleton deficient colors advancing by one, so d must be divisible by three. At d=1 a marked filling would lift to the excluded d=2 filling; no loop-containing tensor application is made. **Met.**
18. **Closed reflection and full-label comparison.** B `refl:input` requires the full chamber package in entries 8–10 and independent panel labels. Positive gluing may reuse downstairs labels locally; the negative implication first passes to the full independently labeled reflection of P_d via a connected finite cover. Candidate §8 proves the local cover comparison and uses the correct contract. **Met.**
19. **Any-homeomorphism height transfer.** Candidate Lemma 9.1 changes the positive degree in B `cyc:criterion` from two to three. It must prove proper height, free proper cocompact quotient, exact kernel action and a faithful normal form. Section 7 checks all of these, with no finite-order or finite-extension splitting assumption. **Met.**
20. **Exact order and final injection.** α³ is inner, but order three is not inferred from that alone. The obstruction excludes the identity class, so α has exact order three; a representative for α² would yield one for α on squaring. **Met.**

The dependence chain is entries 1–5 → 6–11 and 12–16 → 17; entries 8–11,17 → 18 → 19–20. No entry imports BO's existence theorem as an arbitrary six-tip construction, or treats PD's one nonmanifold group as the desired cyclic spectrum.

## 3. The new geometry: strongest objections checked

### The relative handlebody replacement is legitimate

The dangerous mistake would be to call the initial boundary of W primitive in W×[-1,1]. It represents a commutator and is not primitive. The candidate does not make that mistake. The annulus that is primitive is the **old terminal annulus A** in its solid-torus collar N. In the marked boundary-join description, N is A×[-1,1]. Gluing N onto the initial annulus of W×[-1,1] only lengthens a collar of the latter. It requires no primitive initial annulus on the W side.

The rest of the old body meets this summand through finitely many small joining-tube feet. The two product disks of the W thickening extend across the collar. Their finitely many strips leave room for these feet; their repositioning is performed while the entire old surface marking is carried. The old disk dual to A is replaced by two disk duals. The remaining old dual disks are untouched. Replacing a vertex of the connecting tree by a two-leaf tree adds no connecting cycle. Cutting along the resulting disk family gives a ball, with each terminal annulus a rectangle joining just the two copies of its own disk. Standardizing the disjoint rectangle-and-disk-face neighborhoods on the boundary sphere and reattaching handles gives the marked boundary join. Two replacements change four disks into six.

This is the same explicit local disk-system argument in MT `01-geometry.tex:261–310` and B `chambers.tex:138–182`, now performed twice. It is a proof of this particular extension, not an inference from the genus or an arbitrary free basis. The five surface stages have Euler characteristic -5 and their thickening genus six, consistent with the actual complete disk system. The Euler characteristic alone would not establish the marked statement.

The initial root curve, root surface and all lower attaching data travel with the identification. The initial link has not yet been fixed. Once the final body is placed in the exterior of thin attaching solid tori, that transported bottom surface is literally pushed inward from the surviving boundary, with the transported product trivialization. Thus PD's side-marked exterior hypothesis survives. Requiring the transport to fix a previously chosen boundary link would be a materially different problem and is not a hidden assumption here.

### Independent conjugators and framings survive

For each body there are six separated terminal neighborhoods and a connector tree. The six path classes c_i κ_pi can be realized by finitely many arcs in a three-manifold, separated away from their prescribed common root and endpoints. Shared portions get separate parallel tracks. Their thin regular neighborhoods are disjoint from other body neighborhoods. A tree contributes no independent internal cycle: a path change inside a body is a word in its six terminal generators, whereas the specified exterior paths supply the six independent extra-loop conjugators. Those internal words become identity at the flat background even when the exterior extra-loop holonomies are nontrivial.

The list is finite: 20·19 ordered choices for the two occurrences of each color, independently across three colors, times 10^6 conjugator choices and 2^6 signs gives

    k = 380^3 · 10^6 · 64 = 3,511,808,000,000,000.

Its enormous size creates no compactness or accumulation issue. There is no lower bound on track widths, and all widths can be fixed after the complete finite multiplicity is specified. No actual enumeration of k bodies is necessary to define this finite construction.

The six primitive terminal collars admit the six independent integral ribbon twists. The twists are constant near connector feet, transport the whole marked body, and are made before final initial-link selection. The return collar is then chosen with the source's normal quotient frame (φ, r′∂u−u′iφ); its terminal integer winding matches the cap's product framing while fixing its terminal circle. This controls the ordered normal frame, not just its parity. Opposite normal sides at all five symplectic pairs separate the attaching collars. Caps meet body sheets only at their own attachments and have crossings only at opposite plumbing branches.

### Repeated compression gives the required chosen family

For color 0, cutting U and inserting two oppositely oriented copies of its shallow cap produces a disk. W is not a component of that disk. For color 1 or 2, compress W first, then compress U with two parallels of the resulting W disk. The final disk has four copies of the selected terminal cap and no copies of the other terminal caps.

MT's framing calculation fixes the first normal vector and rotates the second from the radial to angular direction in the rounded surgery corner. Its text explicitly identifies the earlier surface compression as the same framed operation, with the inherited outgoing boundary framing (`01-geometry.tex:526–541`). Apply it to W while preserving its attaching product collar. Its output is consequently a framed cap at the specified U attachment. The next operation uses that very product frame. The two operations agree on the overlap; no unaccounted integer twist is added at the handoff. The terminal twists have already transported all the relevant attaching data.

Reserve parallel copies in nested product neighborhoods. Different bodies are disjoint, and the two bottom branches are separated on opposite outgoing sides. Within each resulting branch disk, only one terminal core type occurs, which has no self-plumbing. An intersection with an unused cap or unused subtree is not a self-intersection of the chosen disk, nor an intersection with another chosen disk unless that other disk actually uses the opposing plumbing branch. Not using W in one body does not remove sheets from another body: bodies and tracks are separately reserved.

The relevant assertion is simultaneous construction after choosing **one terminal tip per bottom branch**, not simultaneous disjointness of every alternative disk along a given branch. This is how §6 uses Lemma 4.2. The ambiguity can be removed by the wording in Section 8.

At a positive-cover vertex all branches choose the same color. Opposite selected endpoints never occur. Therefore the entire required family is disjoint apart from each prescribed bottom rim intersection. Exactly one selected endpoint per plumbing is unnecessary: ten of thirty edges at each step have neither end selected, and their unused caps simply do not appear in the family.

## 4. Chamber algebra, positive filling, and their markings

The upper stages add no new cofiber summands because only the bottom punctured tori are removed and replaced. Each bottom map is nullhomotopic in the graph-type X. With the actual tube-side marking, the replacement cofiber kills b, leaves z and leaves two trivial two-cell attachments. Thus D has free group H and full middle module (ZH)^(2k), as claimed. The new six-tip topology is not confused with six additional middle spheres.

For the algebraic calculation downstairs, use the **shallow** cap on each branch. This preserves the source's two-inner-sheet calculation. At a fixed outer rim-copy index and fixed opposing sheet, the two paths differ by the other basis loop of U. Here that loop bounds W. A contraction of W using either terminal cap is a nullhomotopy inside E: only bottom tubes were removed; W, its cap tracks and its caps remain. The nullhomotopy can intersect selected disks because equality in π1 E does not ask it to be disjoint from them. A small normal loop about the undeleted upper surface also contracts inside E.

Consequently the two labels are equal before passing to H, and the opposite inner signs cancel. The argument never equates the two outer-copy labels, whose difference can contain the bottom normal circle. It proves λ(f_i,g_j)=δ_ij and λ(g_i,g_j)=0 over Z[π1 E]. Each g_j uses just one core type and is individually embedded and framed. Closing f_j against the unchanged replacement meridian disk gives the source's matching frame on u_j.

The hermitian u-matrix can be cleared by triangular g-combinations: the identity diagonal coefficient is even, and nonidentity elements of a free group have no order two. For framed representatives, symmetrization in the additive Wall quotient is injective on inverse-pair coefficients and doubles the identity coefficient over Z. Hence zero self-pairing gives zero **full framed** μ. Using only reduced μ would not meet this obligation.

The hyperbolic pairing yields a one-sided inverse for the square matrix of these 2k classes. Residual finiteness of H separates the finite support of any nonzero reverse-identity error; each finite quotient has a finite-dimensional complex regular representation, where left inverses are right inverses. Thus the matrix is invertible over ZH. This proves a basis of the entire module, not merely a direct collection of hyperbolic planes.

The source's regular-coefficient cap-product argument therefore applies to these exact absolute and relative summands. Attaching the 3-cells yields graph type and the collared oriented PD4 pair with all local coefficients. Its low-degree relative regular homology implies π1 S surjects onto H. This also makes every S_d connected. Restriction of scalars and coefficient projection retain all lifted basis elements and full framed Wall invariants, so no lifted reflection hypothesis is missing.

For 3|d, the selected deeper disks instead give *geometrically* hyperbolic embedded pairs. They need not equal the original shallow immersed basis. Their nonsingular pairing and the known full rank again make them a full basis. The disjoint pair neighborhoods are standard punctured S²×S², and replacing them by balls is an interior operation. Van Kampen preserves the group; paths can be rerouted along each connected S³ boundary, so the complement remains connected.

In the universal cover, the neighborhood H2 summands map isomorphically onto all old H2. Mayer–Vietoris gives zero complement H2 and identifies its H3 with the direct sum of boundary S³ classes. Balls kill precisely those classes without creating H4. Local finiteness of the lifted finite family justifies these direct sums. The new simply connected acyclic CW-type universal cover is contractible. Boundary group maps are unchanged. Since P_d is aspherical, the boundary restriction of the classifying equivalence is homotopic to the prescribed inclusion; collar homotopy extension makes it literally the identity on S_d. This supplies the exact positive marked filling required by reflection.

## 5. Formal obstruction: the six-slot ideal passes

Undoing the surgeries uses the specified normal-circle free factors, not just homology classes. This gives graph-type W_d and disjoint cocore law disks with their original based boundary markings. The relevant covering target is the universal **tree of the plumbing multigraph**. It is not the real line: the 30 edges at each step create many graph cycles downstairs.

In its regular cut decomposition, every extra-loop generator lies in a single component, so the component graph is a tree. The prescribed faces and collars form its principal plumbing subtree. An off-principal component has a unique attaching principal vertex and trivial stabilizer. Distinct vertices of the same off-principal branch cannot be identified by a deck translation: their attaching principal vertex would be fixed. Finite quotient component orbits therefore bound the entire branches, not just their valence. Discarding their closed cuts and merging them gives the connected cuts and vertex pieces claimed. The protected disks stay in their vertex pieces.

The graph Betti count is (30d−d+1)+9d=38d+1. Mayer–Vietoris supplies the required signed degree-two isomorphism and degree-one surjectivity; extra evaluations remove its kernel. Half-lives/half-dies gives one boundary line per cut, and surjectivity together with the two distinct bounding longitudes forces a coordinate line. Thus analytic plus/minus choices can be arbitrary relative to port colors.

For topological vertex pieces, the imported punctured-form complex computes the filled cohomology. Every fixed positive-degree coefficient vanishes near the punctures, so Stokes can be applied with zero extra end contribution. No simultaneous vanishing neighborhood for an infinite formal series and no global smoothing of a filling is assumed. The edge theorem sees only compact smooth three-dimensional cuts.

The free outside-face strip representatives accommodate all plus and minus boundary polarizations at once. On each torus, the slice gauge is identity on the *whole* torus after normalization. Hence there is no missing peripheral conjugation at a join. The plus-end action adjustment cancels exactly the fixed-u boundary variation; the minus-end variation is zero in the fixed polarization. These are the actual formulas of B `for:vertex-identities`. The linear pairing gives a unit full-column minor against the residual list even if that list has syzygies. Neither the six-tip depth nor its law enters these calculations.

The initial correction uses the source's quadratic residual-order and vanishing-Hessian hypotheses at the joint origin. Those are not incorrectly assumed after recentering. Marked algebraicity concerns the entire critical scheme, including nilpotents. The plus-end coordinate change is identity at its own parameter zero and retains common central coordinates with the minus end. Recentring takes place in the joint σ-adic ring before passing to K=C((σ)); no later translation of arbitrary Laurent-coefficient series by a nonzero σ-dependent constant occurs.

Here is the independently checked six-slot argument. Write R=T_v[[y_v]], m=(y_v,t), and choose the same logarithm lifts X_i for all laws on a fixed six-set. They vanish at the recentered origin. With **independent** logarithm-coordinate blocks z_i, let P_i be the ideal of the ith block. Brunnianity gives each law entry in every P_i. The variables are disjoint, so a monomial lies in every P_i exactly when it contains a variable from every block; hence intersection P_i = product P_i. Each term beyond degree six has an additional variable and lies in (z) product P_i. Substitution into the possibly nonreduced R therefore puts it in m J_L. One must not assert equality of the intersections of the six *image* ideals after substitution; that equality is generally false.

External conjugators have the prescribed independent constant adjoints. Their higher-order deviations and internal body-word conjugations contribute only to m J_L. Overall conjugation is an invertible linear change on matrix entries. The leading tensor is

    T(U1,...,U6) = [[U1,[U2,U3]],[U4,[U5,U6]]],
    T(e,h,f,h,h,e) = [-2h,4e] = -16e.

For each of the 3^6 scalar coordinate products, rank-one endomorphisms send those six selected coordinates to the six displayed vectors. The source's nine adjoints span End_K(sl2), so expanding these six endomorphisms independently expresses that product as a linear combination of installed scalar law tests. The independently conjugated laws thus span J_L/m J_L. A single unconjugated law would not suffice.

Every installed boundary word bounds a disk in the vertex piece. Evaluate its fixed word matrix on the chosen off-shell lifts; it agrees with its geometric based holonomy **in R/I_v**. Hence its entries minus identity lie in the actual I_v. There is no assertion of off-shell homotopy invariance. For the ideal Q_L of these word entries, this proves

    Q_L ⊂ J_L ∩ I_v,       J_L = Q_L + m J_L.

J_L/Q_L is a finitely generated R-module, and R is local with all individual-square-zero parameters retained. Nakayama gives J_L=Q_L⊂I_v. The conclusion is membership in I_v itself, with no radical or power replacement.

To pass to the mixed endpoint product, do the remaining comparison in R/I_v. A plus logarithm is −t_i T_i, with a nonzero scalar coordinate of T_i. A minus algebraic marked matrix satisfies G_j(M_v)=exp(X_j) in that quotient. Therefore its entries minus identity are in the quotient ideal generated by entries of X_j. Products with one factor from each slot vanish in the quotient by J_L⊂I_v, so all lifted mixed products in (8) belong to I_v. This argument needs only the quotient equality, as the source explicitly states. Section 8 gives wording that makes this scope unambiguous in the candidate.

The polynomial perturbation has no constant term in G−1. Setting just the plus edge's own t_e to zero gives G_e−1 in (I_v,t_e), while all other parameters remain. The logarithm remainder is cubic, its derivative quadratic. Multiplication by t_e kills the terms with another t_e, yielding t_e I_v³ and t_e I_v² respectively. The full-parameter correction changes the section by (t)I_v, preserves the fixed residual ideal and its unit minor, and terminates by powers of the nilpotent ideal. It does not set (t)² to zero. Thus both potential vanishing and actual gradient membership survive, and the final graph reparametrization preserves the central tangent isomorphism.

These verify every hypothesis of **the actual** B `ten:assignment`. It already permits six-element local laws; none of this argument claims that it supplies their geometric realizations.

## 6. Finite constraint and reflection

Avoiding every two-of-each-color six-set makes each deficient-color set D(v) nonempty. If a∈D(v) and b∈D(v+1) is not a+1, the five edges of that forbidden type would have to be assigned to endpoints that together can receive at most two. Thus D(v)×D(v+1) lies in the successor graph. Since both sets are nonempty, each is a singleton and its value advances by one. This is periodic exactly when 3|d.

Conversely choose s(v)=v mod 3 and select the ports of that color. Two endpoints can both be selected only for the omitted ordered successor pair. Every actual edge therefore has an unselected end, to which it can be assigned. Vertices receive no edge of their selected color. Of the six forbidden color pairs per step, four have exactly one selected end and two have neither, producing the stated 20/10 counts after replication. This proves the all-degree statement independently of the diagnostics.

At d=2, the two directed lifts of a type are distinct unoriented edges with their own specified ports. Each vertex has 60 distinct incident edges, 20 ports of each color. No loop is used. At d=1, lifting a hypothetical marked filling to degree two is the valid way to conclude nonfilling. The majority lemma for binary selection is also correct: coordinatewise majority of the odd orbit of a satisfying assignment preserves every binary clause, is invariant, and descends. Its scope remains binary cap-selection formulas, not all topological fillings.

For reflection, every input of B `refl:input` has already been checked for the base and all lifted chambers. Its application gives a finite oriented aspherical PD4 complex Q with a folding retraction onto P. Pullback of P_d gives the connected height cover Q_d. On a positive cover, reuse of downstairs panel labels is valid *locally*: incident lifted panels have distinct images, giving the standard manifold sectors. Label parity orients the gluing. Relative boundary-identity homotopy equivalences glue by the collared cofibration diagrams, giving a closed connected four-manifold model M_d.

For the converse the candidate correctly changes to independent labels on **every lifted panel**. A clique upstairs lifts the simplex determined by its distinct downstairs images, using uniqueness of the incident edge lifts; thus the lifted triangulation is flag. The label map A_d→A_0 is onto and injective on every incident-panel subgroup. Its kernel acts freely on every chamber sector, producing a finite covering of Q_d, with connected domain because each panel coordinate can be crossed. A manifold model for Q_d lifts to one for this full reflection. B's accepted contract now gives the precisely marked filling excluded above. Reusing labels directly in the converse would omit an actual hypothesis; that shortcut is not taken.

The oriented PD4 dualizing module forces any aspherical manifold model to be orientable, so the negative conclusion excludes unoriented models as well. No preservation of chambers or panels by a hypothetical self-homeomorphism is assumed. Consequently Theorem 8.1's full spectrum, not just its positive direction, follows.

## 7. Height transfer and exact order three

Let h represent [Ad(γ^j)] on G3, j=1 or 2. Adjust a lift u by a G3 deck transformation so that its action on G3 is exactly Ad(γ^j). K=ker w is preserved. On X=K\M̃, the resulting h′ commutes with T induced by γ³, because uγ³u⁻¹=γ³. No action of γ outside G3 on M̃ is presumed.

A lift of M→S¹ representing w/3 gives τ(Tx)=τ(x)+1. Compactness of M supplies a compact set C whose T-translates cover X. A bounded closed height band meets only finitely many translates of C, so τ is proper. The continuous difference τ(h′x)−τ(x) descends to compact M and is bounded by c. For R>c+1, F_R=T^R h′ has everywhere positive displacement between R−c and R+c.

Iteration proves freeness and bounds the exponent of any translate meeting given compact sets. It gives a proper cyclic action. Each orbit meets the compact band τ⁻¹([0,R+c]), proving cocompactness. Properness and freeness allow an evenly covered small neighborhood at every point, by separating the finitely many possibly meeting translates of a relatively compact neighborhood. Thus the quotient is Hausdorff and a closed connected topological n-manifold, with the original contractible universal cover. This is not an assumption that arbitrary bounded-displacement maps generate finite actions.

The lift Z_R=γ^(3R)u is defined using an actual G3 deck transformation. For k∈K it has conjugation Ad(γ^(3R+j))(k). The full deck group over the quotient is generated by K and Z_R. Its quotient by K is the freely generated infinite cyclic action of F_R. Accordingly k Z_R^a has a unique normal form: the exponent is detected on X, then faithfulness detects k. The target G_(3R+j) has the corresponding unique forms kγ^((3R+j)a), detected by height. The conjugation identity gives exactly the same multiplication in both normal forms. This is an isomorphism, not merely an identification of outer actions.

Only the extension by an infinite cyclic height group is split here. The finite C3 extension need not split, and h and u need not have finite order. The quotient manifold would be an aspherical model for Q_(3R+j), contrary to Theorem 8.1. This proves Lemma 9.1 in its stated generality.

Finally conjugation gives C3→Out(G3), and α³ is inner because γ³∈G3. Nonrepresentation of α implies α≠1, since identity has an identity-homeomorphism representative. Its order is therefore exactly three. If α² had a representative, the square of that representative would represent α. This proves the full injected subgroup assertion for M3. The elementary counterexample G=Z shows why merely knowing G/G3=C3 would not have proved injection; the candidate uses the valid order of reasoning.

## 8. Exact wording clarifications; no unproved repair substituted

No change of construction, new hypothesis, or unproved repair is needed for the PASS. The following wording makes two scopes precise. I have **not** edited the candidate.

At candidate line 294, replace the compressed minus-input sentence by:

> In the flat quotient R/I_v, the image of G_e(M_v) is exp(\bar X_e). Hence every entry of G_e(M_v)−1 belongs, in that quotient, to the ideal generated by the scalar entries of \bar X_e. The product-ideal inclusion J_L⊂I_v therefore gives (8) after lifting back to R.

This is the exact interface supplied by marked algebraicity, not an asserted equality of arbitrary off-shell lifts. The complete deduction is in Section 5: multiply the quotient ideal inclusions with the plus logarithms, use the zero image of J_L, and lift zero to I_v. Thus (8) and every subsequent step follow even if the stronger literal off-shell membership in the original sentence is not chosen. The surrounding flat-quotient argument already supports this interpretation; it is a clarification of that interface, not a new geometric or analytic lemma.

In Lemma 4.2, an optional first-sentence addition is:

> For any choice of one terminal tip on each bottom branch of the finite family, perform the following constructions simultaneously. The intersection assertion concerns the resulting chosen family, not all alternative disks along the same branch at once.

Section 3 verifies that family, which is exactly what the positive filling needs. Neither clarification enlarges a source's quantifiers. No other repair is required by this review.

## 9. Independent diagnostics, limits and handoff

The new [checks.py](../experiments/i15_odd_order_topology_r2/checks.py) was written for this review; no candidate-writing script was executed. It uses only the standard library. Its [retained output](../experiments/i15_odd_order_topology_r2/checks.json) checks:

- All 49 pairs of nonempty deficient-color sets using actual integer allocations in five-edge bundles; precisely the three singleton successor transitions survive.
- Exhaustive cyclic color assignments through degree ten and full distinct-edge incidence in degrees 2–60, including all positive cap/endpoint assignments at multiples of three through 60.
- The exact body count, tree leaf/genus bookkeeping and recursive cap multiplicities (2,4,4).
- A degree-seven Magnus expansion: 32 degree-six and 192 degree-seven terms, all containing every slot; all six exact Brunnian specializations. Additional cross-tip conjugations retain the same degree-six part and yield 444 degree-seven terms, still containing every slot.
- T(e,h,f,h,h,e)=−16e and an exact nine-adjoint determinant +512 at σ=1 in row-vectorized (e,h,f) convention. The author's −512 uses a different ordering; only nonvanishing is relevant. No source statement is rejected over this sign convention.
- Preservation of mixed squarefree parameters and explicit invalid-shortcut diagnostics: intersections need not equal products after identifying slots, a single unconjugated tensor can vanish, and the full nilpotent ideal is not square-zero.
- 8,750 height normal-form multiplication cases with a nonabelian free kernel and the nontrivial Nielsen action x↦xy, y↦y. This tests the kernel action rather than only abelian exponent arithmetic.

All passed. They are diagnostics, not proofs of smooth placement, framing, topology, all-degree necessity, actual-ideal membership, Poincaré duality or closed manifold realization. Those conclusions use the arguments and exact contracts above. In particular the finite tree Euler calculation does not replace the six-disk marked-handlebody construction, and the finite Magnus calculation does not replace Brunnianity and Nakayama.

Reproduce the retained-byte checks from the project root:

```sh
python frontier/experiments/i15_odd_order_topology_r2/audit.py
python frontier/experiments/i15_odd_order_topology_r2/checks.py
python frontier/experiments/i15_odd_order_topology_r2/seal.py --verify
```

The first two commands deterministically write only R2 outputs; the last is read-only. The [artifact manifest](../sources/i15_odd_order_topology_r2/artifact-manifest.json) includes the report, scripts, results, contracts, proof excerpts, full brief and dependency snapshots, excluding only itself. Its verification also checks every live dependency remains byte-identical to its R2 snapshot. None of the original or resumed artifacts was modified.

Remaining limits are substantive but outside this proof verdict: the construction depends on the stipulated corpus, no complexity bound is proved, no full outer automorphism group is computed, no smooth structure on the closed result is asserted, and worldwide priority is unverified. The separate significance review should decide whether the marked arity extension and odd-order consequence meet the user's substantial/nonroutine threshold. The finite successor gadget, elementary height transfer and formal tensor expansion are not separately countable findings.

Only this review and `frontier/{sources,experiments}/i15_odd_order_topology_r2/` were written. No subagents, shared-index/candidate edits, staging, commits, pushes, or unrelated-project work were used. **Handoff: full proof PASS on the stated premises; significance/novelty still pending; accepted count unchanged at four.**
