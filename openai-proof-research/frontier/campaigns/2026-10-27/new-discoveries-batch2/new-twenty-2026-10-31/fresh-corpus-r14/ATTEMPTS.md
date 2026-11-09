# Exact attempts and obstructions

## 333840: six unit vectors

Literal target: maximize D(V)=min over all 20 triples of absolute 3×3 determinants of six unit vectors in R³. A rigid rotation can place one vector at the north pole; independent sign flips preserve D. Fincher arXiv:1608.06011v1, introduction and §5.4, gives precisely the icosahedral conjecture. §5.2 Theorem 15 and its proof solve the plane case only; the n+1-vector simplex theorem does not solve six vectors in R³. Relevant source passages were read, not the entire manuscript or its journal counterpart.

**Exact restricted calculation.** Put v₀=(0,0,1), and vⱼ=(sqrt(1-t²)cos(2πj/5),sqrt(1-t²)sin(2πj/5),t), 0≤t≤1. Let s=sin(π/5). The minimum determinant among triples containing v₀ is s(1-t²). The minimum among triples entirely on the ring is sqrt(5)s t(1-t²): expanding the determinant gives (2sin(2π/5)-sin(π/5))t(1-t²)=sqrt(5)s t(1-t²). The other ring triple type has larger coefficient. Consequently, for x=t²,

D²=s²(1-x)² min(1,5x).

If x≥1/5, (1-x)²≤16/25. If x≤1/5,

16/25-5x(1-x)²=(1/5-x)(5x²-9x+16/5)≥0,

because the second factor is ≥16/5-9/5=7/5. Thus the ring family has its maximum at x=1/5, and D²=2(5-sqrt(5))/25. This is the icosahedral configuration. This restricted proof is a parameter-family calculation, **zero discovery credit**, and not the full literal statement.

**General route attempted.** For a 3×6 matrix V of unit columns, Cauchy–Binet gives sum of the 20 squared determinants =det(VVᵀ). The trace is 6, so the product of the three nonnegative eigenvalues is ≤8. This only proves D²≤2/5, strictly above 2(5-sqrt(5))/25≈0.22111456. Thus this moment certificate cannot close the target. Tight frames do not remove this gap; a bound on the smallest minor, using additional Plücker constraints, is required. No justified symmetry reduction from arbitrary V to the pentagonal ring was found.

**Diagnostic route.** `diagnostics.py` runs 160 deterministic-seeded constrained optimizations over all five free spherical vectors with a fixed pole, with signed determinant inequalities in each initial sign chamber. Forty starts perturb the icosahedron; 120 start globally. Best numerical D=0.4702282018339783, matching the icosahedral value to displayed precision. SLSQP is local, sign chambers are not exhaustively covered, and numerical equality is not proof. No counterexample emerged to rationalize or carry into a Lean semantic bridge.

**Precise outstanding obligation.** Prove that every six unit vectors have some triple with squared determinant ≤2(5-sqrt(5))/25, or produce six exact unit vectors with all 20 minors strictly larger. Lean feasibility: a finite explicit witness would reduce to algebraic real inequalities plus a matrix/minimum bridge; the general upper bound requires substantial geometric reasoning not supplied here. No full Lean endpoint or acceptance packet exists.

## 334220: three total dominating sets

Literal target: every finite simple planar triangulation of minimum degree ≥4 has three disjoint total dominating sets. Goddard–Henning arXiv:1609.09684, §5.5 Conjecture 35, retains this exact scope. Lemma 29 and its proof give the sharp known U(G) construction. The same passage states that the punctured icosahedron (a triangular disc with a pentagonal outer face) fails the three-set property. This is **not** a counterexample to the closed triangulation statement.

Read the later Francis–Illickan–Jose–Rajendraprasad arXiv:2205.06464 Theorem 1, Corollary 2, §2 proof (Observations 5–20, Lemma 18) and conclusion passages. Their proof solves the two-set target 334218, and explicitly leaves progress on the three-set question open. Its color-merging argument does not establish three sets. In particular a proper four-coloring guarantees all three colors of a triangle survive a merge to two, but no map from four colors to three can preserve all four possible three-color subsets. The local repair in Observation 13 also relies on a uniquely missing color for two-color neighborhoods; for three colors different neighbors can lack different colors. The existing proof is therefore not an available full-scope shortcut.

**Finite witness route.** Three disjoint total dominating sets are equivalent to a coloring c:V→{0,1,2} in which every open neighborhood contains every color. Unused vertices may be assigned arbitrarily to one set. `diagnostics.py` uses a recursive exact integer coloring search, pruning any neighborhood with fewer unassigned vertices than missing colors and propagating single forced colors. It samples 12 degree-preserving planar-flip states at every order 6..30, starting from bipyramids. All 300 samples yielded explicit colorings; no timeout. Sampling is not enumeration, and repeated/isomorphic samples are not claimed distinct.

**Structured obstruction route.** `structured.py` first verifies the known punctured-icosahedron control fails: exhaustive recursive search rejects it in 128 nodes. It then doubles that punctured patch along its pentagonal boundary for all ten dihedral identifications. All ten resulting 17-vertex closed triangulations admit a coloring (some are isomorphic). It additionally glues 1,2,3,4 icosahedra along triangular faces, giving orders 12,21,30,39; all admit colorings. The constructive patch-obstruction mechanism therefore fails on these explicitly tested assemblies. Planarity and edge-count/minimum-degree diagnostics are checked for the pentagonal gluings; no formal planar embedding certificate is claimed.

**Precise outstanding obligation.** A genuine counterexample needs a closed sphere triangulation with δ≥4, an exact unsatisfiability certificate for all 3-colorings, and a Lean proof of its embedding and coloring equivalence. Alternatively a new extension invariant must handle three different missing colors, beyond the published two-color proof. No such invariant or finite counterexample was found. These routes are parked, not resolved.

## Prior-result exclusions

333968: read the primary definitions/Conjecture 4.3 and published Majstorović, MATCH 90 (2023), 673–684, DOI 10.46793/match.90-3.673M, definitions and Theorem 4 proof, with the cited majorization reduction (Theorems 2–3). It explicitly states every bounded-maximum-degree maximizing tree is the almost dendrimer. The n−2 rather than sqrt(n−2) normalization printed in parts of that successor does not affect maximizers at fixed n; no new result claimed. This is a published prior resolution, not a fresh discovery.

334218: later Corollary 2 and complete relevant proof chain above directly subsume the literal two-set target. Zero credit.

334437: later arXiv:1611.06557 Theorem 1 directly states the bound for g≥5; the older paper states known g≤6 cases. Only the later theorem passage was reviewed here, not its full proof. This is sufficient reason not to invest in rediscovering it, but is not a newly independently audited proof.

334540: primary-author arXiv:2111.08111 and 2207.03941 publicly state the earlier bow-tie counterexample has index 4. Only search-returned primary passages inspected; original proof body and published-body comparison not audited. Excluded from new discovery investment; no fresh Lean reproof pursued.

333946: primary Conjecture 3.3 and α=2 proof context read. α=2 is already Theorem 3.8, so an integer quadratic-moment certificate cannot be new full-scope work. Even normalized star-spectrum majorization fails as a general approach: for P₄ the sum of the two largest normalized eigenvalues is (4+sqrt(2))/6>5/6, whereas for K₁,₃ it is 5/6. No full all-α proof follows from that attempted shortcut; no claim of counterexample to entropy itself.
