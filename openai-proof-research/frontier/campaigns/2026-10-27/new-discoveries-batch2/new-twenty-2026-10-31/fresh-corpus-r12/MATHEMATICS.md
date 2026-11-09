# Mathematical handback — r12

## 332204: complete ordinary counterexample; eligibility/source HOLD; no Lean

Use vertices 0,...,11 and edges e_i={i,i+1 mod12}. Let G=C12 and let H delete e_2,e_5,e_8,e_11. Thus H is four disjoint paths P3, a proper **spanning** subgraph. Both graphs have at least three vertices, no isolated edge and no isolated vertex, as required by Definition2 in arXiv1601.00883v1. Neither has equal closed neighborhoods at distinct vertices. Connectivity is not imposed by that paper's ambient definition or Conjecture4; H is disconnected. No claim about an additional connected-subgraph version is made.

In the source, the four palettes are E_i (incident edge colors), V_i (own vertex and neighbor vertex colors), T_i=E_i union {v_i}, and N_i=E_i union V_i. Injectivity of each palette on the vertices implies all eight C1–C8 conditions: each even-numbered condition restricts the preceding all-pairs condition to adjacent pairs.

Color the vertices, in order, by

    2 5 2 0 4 3 5 0 1 6 4 6

and the edges e_0,...,e_11 by

    0 1 4 5 1 2 6 4 3 5 2 4.

All colors belong to {0,...,6}; translation by1 gives source colors {1,...,7}. The following table lists the four palettes (digits denote set elements).

|i|E_i|V_i|T_i|N_i|
|---|---|---|---|---|
|0|04|256|024|02456|
|1|01|25|015|0125|
|2|14|025|124|01245|
|3|45|024|045|0245|
|4|15|034|145|01345|
|5|12|345|123|12345|
|6|26|035|256|02356|
|7|46|015|046|01456|
|8|34|016|134|01346|
|9|35|146|356|13456|
|10|25|46|245|2456|
|11|24|246|246|246|

Each column has twelve different sets. Consecutive vertices have different colors; consecutive edges have different colors; e_i differs from both incident vertex colors. These direct finite checks prove this is a proper total coloring satisfying all eight conditions. Hence chi''_(8)(G)<=7.

The leaves of H are 0,2,3,5,6,8,9,11. Their incident edges are respectively e_0,e_1,e_3,e_4,e_6,e_7,e_9,e_10, eight distinct edges. At each leaf E_i is a singleton. C1 therefore forces these eight edges to have eight distinct colors in **every** (8)-distinguishing total coloring of H. Thus chi''_(8)(H)>=8. Its value is finite: give all vertices and present edges globally different colors. E palettes are different because no component is K2; V,T,N palettes are different because the own vertex's unique color identifies the closed vertex neighborhood or its vertex, and distinct vertices of P3 have distinct closed neighborhoods. Consequently

    chi''_(8)(G) <= 7 < 8 <= chi''_(8)(H).

This proves the exact negation of the literal all-simple-graphs monotonicity conjecture. It does not require determining either chromatic number exactly. The randomized annealing merely located the two finite arrays; the table, properness checks and universal leaf lower bound are the proof. `verify_coloring.py` deterministically rechecks the table independently of the search.

**Not a new accepted solution.** Original definitions, Lemmas2–4 and their proof bodies, and Conjecture4 read. Later Ma–Yang2023 definitions, Lemmas1.2–1.3 and Sections2–3 selected construction/proof passages read: these concern four related invariants, not an authenticated exact (8) endpoint. The source explicitly credits prior nonmonotonicity constructions in [13] and discusses [14]'s many-constraint colorings. [14] is Yang–Yao–Ren, IPL116(6)(2016)396–400, DOI10.1016/j.ipl.2015.11.014. Its actual theorem/proof body was not obtained: DOI opening returned inaccessible. [13]'s full body likewise not located. No further formal investment is justified before that comparison. A finite optimized witness need not supply a nonroutine consequence if existing palette constructions and leaf-count lower bounds already give the same universal refutation. This is a concrete unresolved subsumption question, not empty-search novelty clearance. Recommend root assess source/significance first; no acceptance review or formal-completion assertion.

## 333041: three-column full-scope proof route, exact gap

The current arXiv1605.00180v5 Section6 Lemma4 proof gives the lower bounds. For odd n the construction uses one long column plus two points in its end row; for even n it uses the long column without its endpoints and two other points at each endpoint. These are source results, not discoveries.

An integer grid is encoded by row masks in {0,...,7}. A forbidden triple consists of three distinct selected lattice points with nonzero determinant and a repeated squared pair distance. Enumerating these triples is exact integer arithmetic. Equal squared distances with unequal absolute vertical displacements satisfy |a^2-b^2|<=4 when the horizontal width is2. The unequal absolute displacements are consequently small: if |a|>|b|, (|a|-|b|)(|a|+|b|)<=4, so |a|<=2. But equal absolute vertical displacements can be arbitrarily large. Those yield the unbounded-span symmetric triangles that a bounded-row automaton forgets.

Diagnostics solve the actual full forbidden-triple MILP for n=5,6,7,8,9,10,15,20 and match the conjectured values. Solver bounds are not kernel certificates. A separate exact-integer transition experiment retains only forbidden triples within w consecutive rows. Four rows already suggest an n+2 upper bound for all tested n>=6, but this is not a proof for all n. The local relaxation permits n+2 points for odd n. At n=7 its two extremal words are (6,1,1,1,1,1,6) and its horizontal reflection (3,4,4,4,4,4,3); each has a long isosceles triangle. At n=9 there are16 locally extremal words, at11 there are58, at13 there are302, and at15 there are1388. Thus a claimed simple two-word equality classification is false for this relaxation.

**Decisive next lemmas:** (A) prove an inductive potential on the four-row transition graph giving |S|<=n+2, with initial and terminal potentials, for every n>4; (B) classify the equality walks enough to show each odd-length equality walk has a long symmetric forbidden triple. Neither lemma is proved here. Even completing A would leave the exact all-n MathDB question unresolved. A finite-state upper-bound family at tested lengths must not be called the full conjecture.

**Later-source bridge tested:** Georgiev–Gomez-Serrano–Tao–Wagner, Mathematical exploration and discovery at scale, Section39, studies square grids and forbids **possibly flat** isosceles triangles. Its 64x64 and100x100 numerical constructions give no three-column upper bound, and the stronger forbidden-triangle condition cannot be substituted for Wu's nonzero-area condition. That actual body passage was inspected. Published Forum Geometricorum2017 body remains unread; current OEIS A271914 keeps both conjectures but is not novelty clearance.

## 333040: even-grid route

The actual forbidden-triple MILP reaches10 on4x8 and12 on4x10, the conjectured bounds. The6x12 and8x16 runs hit20-second limits with large gaps; their incumbents certify only feasible lower bounds15 and16, not optimality. Subadditivity T(n,k+m)<=T(n,k)+T(n,m), supplied by source Lemma4, does not propagate n+k-2: adding two such bounds duplicates the n-2 overhead. A successful recurrence needs a uniform low-occupancy removable strip or another global charging argument. No such lemma was proved. No counterexample found and no positive proof claim.

## 332288: hull-generator route

Actual source Section5 Lemmas5.1–5.2, Corollary5.3 and Theorem5.4 proof bodies reduce all kernels to minimum-rank idempotents in one L-class, forming a left-zero semigroup. This is a known reduction. The new required step is to select <=n-1 such kernels covering every nonedge. A union-find spanning-forest argument fails: nonedges must be covered by actual individual kernel classes, not by the equivalence closure of the union. Transitivity of the union is unavailable; composing left-zero maps creates no new kernels. The paper's MOLS and Hamming graph constructions are special families, not a selection theorem for arbitrary hulls. No full proof, counterexample or Lean endpoint. Next lemma would be an n-1 covering theorem for the full family of minimum-rank kernels, exploiting more than just pair coverage.

## 332426: finite-field mechanism

Read full Section4, including Proposition4.1's four-way equivalence and actual proofs of Propositions4.4–4.5. The binomial mechanism x^l-a with a primitive gives the prescribed coefficient property only under the stated prime-divisor and mod4 conditions. The Artin–Schreier construction x^p-x-a uses nonzero trace and handles l=p. Neither mechanism treats arbitrary l and k; adjoining roots in a tower need not preserve the requirement that **all nonconstant coefficients lie in the original F_q**. This is the exact obstruction to a purported tower proof. Known k1/l1/l=p/binomial cases receive no credit. No tractable full-scope extension survived.

## Exclusions and semantic traps

* 332485: actual source Theorem4 proves the stronger alpha_1+tau_B<=n^2/4. Every bipartizing deletion also meets every triangle, so tau_1<=tau_B gives the literal endpoint. Read theorem and the recursive partition proof setup; do not formalize as a new solution.
* 332556: Huang–Li–Qin–Magnant–Ozeki Theorem3.2 states the exact diameter-three theorem. Read its proof's 2-edge-cut case analysis and spanning-subgraph extension. Existing 2017 result, not new.
* 332975: actual source explicitly says Conjecture3 at H=G is equivalent to Steinberg. To see the reverse bridge concretely, the circular6 target allows color differences2,3,4; its vertices split into three independent pairs {0,1},{2,3},{4,5}. Any circular2-backbone6-coloring with H=G therefore gives a proper3-coloring. Conversely scale proper3-colors to0,2,4. Cohen-Addad et al. arXiv1604.05108v2 Theorem3 constructs a planar non3colorable graph without4/5cycles; actual gadget Lemmas1–2 and Theorem3 proof read. The refutation is a routine already-explicit equivalence, zero credit.
* 332890: normalized C(a,b) omits lines; current source Section4 explicitly includes circles **or lines**. For collinear n equally spaced points the literal circle-only C is2 and equal-midpoint pairs produce Omega(n^3) bisector energy, defeating O(2n^2), but intended C=n excludes this shortcut. Do not count a transcription refutation. The intended circle-or-line energy estimate remains unproved.
* 333018: source f is strictly increasing with positive values, H is inclusion-free, and the empty hypergraph has a convention making all weights isolating. Constant or negative objectives and an empty-H obstruction violate intended conditions. Source Theorem2.9 gives only the weaker lower bound, and special M2/linear cases are already proved. No general layer-one proof.
* 333020: small n endpoint contradictions to the displayed normalized exact formula are not substantive extremal discoveries. Need source asymptotic quantifiers and full generalized-cycle definition before any counterexample. No such normalization shortcut used.
