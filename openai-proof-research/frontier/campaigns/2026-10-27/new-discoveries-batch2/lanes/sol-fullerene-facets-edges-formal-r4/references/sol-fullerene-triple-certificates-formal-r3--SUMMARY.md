# Actual fullerene triple certificates and real vertices/hulls

30 October 2026. Implementation component CLOSED for actual G/H vertex completeness, convex hulls and all indexed supporting sections. Full source, novelty and acceptance remain HOLD. Counts remain9 additional /39 total / next40; root alone accepts/counts. Solo work, no children, manuscript, shared/git/public/browser/MathDB changes or analytic/facet-edge-cubic next stage.

## Literal real endpoints

`CompleteG.lean` and `CompleteH.lean`, namespace FullereneGeometry, prove:

* `complete_triples_G/H`: every real x feasible for the actual qG/qH, satisfying the equations of any independent active triple, belongs to the range of the actual pG/pH.
* `listed_vertices_G/H`: each of the60 actual listed real points is feasible and has an active triple whose equations uniquely determine that point among ALL real points.
* `complete_vertices_G/H`: `(poly qG/qH).extremePoints ℝ = Set.range pG/pH`, by applying the inherited `complete_vertices_of_triple_certificates` with both actual premises discharged.

`HullG.lean` and `HullH.lean` apply the inherited bridges to those actual equalities and actual compact_G/H:

* `hull_G/H`: `poly qG/qH = convexHull ℝ (Set.range pG/pH)`.
* `section_hull_G/H`: for EVERY i:Fin32, `facetSection qG/qH i = convexHull ℝ {x ∈ Set.range pG/pH | dot (qG/qH i) x = 1}`.

These are quantified real statements, not rational table-validity surrogates. No affine dimension, facet/edge exhaustion, cubic adjacency, analytic exponential or full SourceClaim follows in this packet.

## Checked finite certificates and transport

There are4960 sorted distinct triples per graph, split into310 modules of16 arithmetic certificates each (620 arithmetic modules total). All have a checked nonzero integer determinant and a positive-denominator rational point satisfying the three active equations. The untrusted generator obtains this point by rational Cramer arithmetic. Every identity is subsequently kernel-checked: the generator's assertions are not axioms. For each graph60 records identify an actual listed point by exact cross-products;4900 identify one explicit strictly violated inequality. The converse60 listed-point certificates check all32 inequalities and a nonsingular active triple.

DataG/H express integer normals scaled by a positive common D. BindingsG/H prove their coordinatewise equality with the actual real qG/qH and pointwise equality with pG/pH. RealCore proves determinant uniqueness by three polynomial linear-combination identities over ℝ, so active equations force EVERY real x to equal the rational witness. A bad witness then contradicts feasibility; a good witness equals the literal listed point. CompletionCore sorts every independent triple from Rank using injectivity and six order cases. Coverage of every sorted triple is an exact reflexive equality with the finite-index domain; no monolithic4960 arithmetic decide is used.

The new record tables are explicitly noncomputable to suppress unnecessary executable code, preserving their values and kernel proofs. Literal, InstanceG, InstanceH, Rank, Hulls and Geometry remain BYTE-IDENTICAL to the frozen inherited sources. The inherited785-declaration strict audit required no annotation repair.

## Replay, audit and provenance

The final deterministic source archive is `source.zip`, SHA256 `da84a4e3c3e46cc3e01eaad05d2331356fc007101a2c2c2f7875cbf901945811`. Its clean source-only extraction is replay/fresh. All775 completed serial compiler calls passed, with728 mathematical module origins and4552 actual declarations reconciled against individual axiom reports. Private/generated names are included. Both partial and unsafe flags, and every transitive type/body dependency, are hard-fail checked; only propext, Classical.choice and Quot.sound occur. No ignorelist. One interrupted audit had no completion receipt and was rerun successfully; its log remains unaccepted evidence. The earlier candidate extraction and all rejected attempts remain evidence; they are not used by the final clean replay. See audit.json, owned-declarations.json, replay-receipt.json, RUN.md and FAILURES.md/failures.json.

All Lean calls use the pinned compiler and9 unchanged package pins with j1 M2700, groupRSS2800MiB CPU210s wall230s, warningAsError=true autoImplicit=false. Helpers use the required512MiB guard with CPU210s wall230s. No caps were raised. Owned compiled objects are removed before final manifest generation. Separate guarded verify.py checks scientific original/copy hashes, inherited source/name preservation, all pins/compiler hash, extracted/archive/source equality, deterministic ZIP regeneration, manifest exclusion of itself/receipt, and absence of owned compiled objects.

Sources were frozen before scientific reading, with original/copy hashes checked before and after. The root r5 disposition, exact r2 sources/summary/failures/harness, original rational realizations and pinned Krein–Milman/finite-convex-hull proof bodies are bound locally. Administrative files are snapshots only. No external retrieval was attempted; denied GitHub/ScienceDirect/Google routes and inaccessible historical intervals remain parked. No current literature/priority clearance is claimed. Novelty/full-source HOLD and independent root acceptance remain outstanding.
