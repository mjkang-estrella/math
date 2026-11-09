# Ordinary attempts and precise stopping points

No qualified candidate. No Lean, solver, numerical search, or heavy enumeration was run. These are mathematical notes, not acceptance decisions.

## 370439: synchronize copies, then complete each fibre

Read all three versions of Conjecture 3.1 and the latest proof of Theorem 1.10, Corollary 2.3, Theorem 3.3, and Proposition 3.4. Distance means minimum distance between endpoints, not distance in the line graph. The larger part is called n in the record/v1 and m in v2/v3; this is a harmless interchange.

The complete-factor proof first colors one copy of G and copies it across all factor coordinates. A prescription on a G-edge can occur in at most one factor coordinate because distinct coordinates of a complete graph are adjacent. A prescription inside a factor fibre removes its color from incident G-edge lists. The list-degree theorem then produces a common coloring, and each complete fibre has the same remaining palette at all its vertices. This is an actual source proof and not a new mechanism.

For K_(a,b), two coordinates in the same part have distance two. Prescribe the same base edge uv at two such coordinates, with different colors. The prescribed edges have endpoint distance two, so they are permitted. A single common coloring of G cannot satisfy these prescriptions. This defeats the proposed synchronization extension but is not a counterexample to the question: different G-copies could use different colors.

Second approach: synchronize separately within the two parts. The same example already defeats synchronization within a part. Allowing different palettes on individual copies leads to a genuine compatibility problem: for each base vertex, the residual lists on K_(a,b) must support a proper b-edge-coloring that agrees with the prescriptions. No theorem read supplies this with arbitrary palettes induced by all G-copies. Merely having the right number of available colors per vertex does not prove the requisite edge-list condition or simultaneous extension.

Third approach: use the published local obstruction of Proposition 3.4. It needs each factor to have a maximum-degree vertex whose entire neighborhood is covered by an induced matching. In K_(a,b), an induced matching has at most one edge: two disjoint edges have cross edges. Thus it cannot cover a neighborhood of size at least two. The only remaining complete-bipartite case is a star at its high-degree center, already positively settled by Theorem 3.3. The printed recipe does not furnish a new counterexample.

Stopping point: no full extension lemma and no explicit nonextendable instance in the conjectured class. Do not send a generic coloring-search architecture to Pi. The journal URL returned 403; its body was not read and no alternate denied route was attempted.

## 337975: matching cuts, orientations, and the source gadgets

Read v1 Conjecture 6 (3-edge-connected), v2/v3 Conjecture 6 (3-connected), the source's Lemmas 3–5 and final computational discussion. Read the independent author PDF's corresponding statements. Rendered and visually inspected v3 PDF p.6: this is Figure 3, despite the local image filename saying figure4. It depicts the a-arc gadgets, not a new witness.

First route: choose a non-Hamiltonian bipartite cubic graph, then orient its matching cuts to make every perfect matching bad. Non-Hamiltonicity is necessary for such an obstruction: if the complement of a perfect matching is a Hamilton cycle, no edge cut can be contained in the matching. But non-Hamiltonicity is not sufficient. For each perfect matching a cut must be selected and all selected cuts must admit compatible directions. Shared edges impose coupled direction constraints; an arbitrary orientation of a non-Hamiltonian graph does not certify anything. The paper reports failure on its tested small bipartite non-Hamiltonian examples. No new explicit graph or compatible family was obtained here.

Second route: reuse the a-arc amplification. The printed construction from a partially oriented Petersen graph proves the unrestricted cubic statement false. It cannot answer the reserved bipartite question: the Petersen seed is nonbipartite. The second amplifier preserves bipartiteness if supplied a bipartite seed but does not manufacture such a seed. Constructing a 3-connected cubic bipartite graph with the needed a-arc remains an unsolved obligation of this route. Copying the amplifier itself would additionally fall under the source-recipe exclusion.

Third route: use the 1-factor decomposition of a cubic bipartite graph. It partitions its edges into three perfect matchings, but it does not follow that one of the three avoids all directed cuts. Different cuts could be contained in different matchings; fractional matching coverage is not a simultaneous cut-avoidance proof. No integrality/exchange lemma eliminating this problem was established.

Stopping point: no concrete full counterexample certificate plan; no Pi task. The general-source refutation already screened in r87/r249 is not the reserved question.

## 360294: contraction and the excluded literal counterexample

Read the mixed/bi-hypergraph definition, Lemmas 4–5 with proofs, and Conjectures 3–4. A proper bi-coloring has 1 < number of colors on each r-edge < r. In particular it forbids both monochromatic and rainbow triples.

The contraction route requires two vertices in no common edge. Lemma 5 obtains this from n >= floor(rm/(n+1))(r-1)+1. Without this inequality, pair-covering hypergraphs obstruct the contraction route. Identifying adjacent vertices can shrink an r-edge and loses the literal r-uniform problem. Deleting a vertex and assigning it an old color also need not preserve both the nonmonochromatic and nonrainbow conditions. Source Theorem 2 already resolves the small-m r=3 range; repeating it would be source work, not a solution of the all-r implication.

There is an exact full negation of the unrestricted printed statement through a vacuous antecedent. Set r=3, n=5, m=11. The class BiHyp(5,3,11) is empty since a simple 3-uniform hypergraph on five vertices has only C(5,3)=10 possible edges. On V={0,1,2,3,4,5}, take all ten triples of {0,1,2,3,4} plus {0,1,5}. This has order six and exactly eleven distinct triples. Its K5^3 subhypergraph is uncolorable: any color occurring at least three times makes a monochromatic triple; if each color occurs at most twice, five vertices use at least three colors and choosing one vertex of three colors makes a rainbow triple. Thus the consequent fails, and n=5=(r-1)^2+1 satisfies the bound.

This is explicitly EXCLUDED as a vacuous-domain correction, using a classical complete hypergraph and one added edge. It does not address the intended nonempty-class extension question, and is not a significant new solution. No credit and no CANDIDATE.md. Under a repaired hypothesis m <= C(n,r), the route remains open here. For r=3,m<=9 the source already proves colorability for all relevant orders; larger m and higher r still need a substantive mechanism.

## 381125: explicit classical bridge and public stronger attempt

The literal record defines proper by avoiding other vertex positions, rather than all lattice points. Every ordinary noncrossing straight-line integer drawing satisfies that definition, and the polynomial O(n) by O(n) grid embeddings cited in the source therefore answer the literal weakened record immediately. In the paper Definition 25 means primitive planar; primitivity forbids unused lattice points in edge interiors too. Neither claiming the ordinary grid theorem nor exploiting the missing definition earns credit.

A public ProbXiv comment dated 2026-08-17 gives an actual stronger proof attempt, not just a claimed answer: after a polynomial integer embedding and shear, perturb in polynomially small boxes; use a four-coloring for residues mod 2,3,5; order vertices with at most five earlier neighbors; avoid their y-residues modulo each prime >=7 dividing an x-difference. CRT gives a modulus at most 30 times the product of at most five polynomial x-differences. Uniform polynomial vertical refinement realizes every needed residue inside its box. No prime divides both coordinate differences, so every segment is primitive. I read this argument body. It is a public machine-authored attempt with machine review, not independent human or Lean validation; I have not audited all geometric perturbation bounds. It is nevertheless concrete prior art that precludes presenting this same mechanism as new here.

## Other exact-scope obstacles

333576: averaging strip area gives a bounded occupancy scale, not g(N) tending to infinity uniformly over all point sets. No multiscale concentration alternative established.
353676: stable homogeneous ternary structures and the source's conditional finite-language expansion route do not prove the all-k set-homogeneous assertion; the expansion obstruction in Problem 5.2.5 remains.
335653: complete multidigraph domination does not supply the stable-set cover for arbitrary union-of-quasi-order digraphs. The paper's extension depends on bounded stability number, not solely k.
374507: dense orchard cores are not ambient cubic containers. No passage from many rich lines to a positive-density patch with the strict blocker coefficient was obtained.
381928: orbit divisibility permits exceptional short orbits; it is not a contradiction. The source prints cyclic base systems through v=30. No recurrence settling all four residue families, including 2-split conditions, was found.
369109: replacing a loop (degree contribution two) by semi-edges changes locally bijective cover constraints. The source semi-edge hardness theorem is not a reduction for arbitrary loop completions. No gadget preserving simple input and every target choice was produced.
325668: Lemma 5.1 characterizes when a spread gives a hyperoval. It does not classify projective equivalence among all eligible regular spreads. The exact database wording was not located verbatim in the fetched v1 discussion; its ambient C assumptions must be reconstructed before any candidate.
372550: read scatteredness as every f(x)+a x having at most q roots, Theorem 1.1's norm/P_s conditions, and Conjecture 6.3 in all four versions. A finite sufficient example or a singular parameter is not a classification. h=0 causes negative-power issues, and missing gcd/odd-q conventions must not be exploited. No admissible scattered example outside the sufficient families was derived.
335182: a rainbow 2-factor on 2n vertices has 2n edges but only 2n-1 colors, so that option is impossible; the actual work is a rainbow union of cycles on 2n-1 vertices. This counting observation alone does not refute the disjunction. Small n endpoints are not candidates. Earlier rainbow-path literature already discusses this Ryser-related question.
336404: a fixed Hist is needed to define outer cycles. An ordinary cycle double cover without the specified outer cycles does not answer the record; the source already knows up to three outer cycles. No extension from three to arbitrary many obtained.
343137: Baire arguments for countably many values and special words do not cover every word and all cardinalities below the continuum. No uniform open law subgroup established.
350737: all distinct and all admissible orders are both obligations. Odd-cycle threshold separation in a sibling record does not construct graphs realizing every order.
347216: source Theorem 1.1 gives a partite presentation, but no equivariance for an arbitrary prescribed transitive group follows. The exact displayed cover/homomorphism request was not located in the fetched v1; no source-fidelity clearance.
374916: two-color and rational versions, and the triple {x,x+y,xy}, do not imply the four-point assertion for arbitrary finite colorings of positive integers. No full route.
373058: the main theorem separates every proper immersion-closed class from all graphs. It does not compare every pair of distinct classes. No pairwise separator theorem or two classes with proved identical homomorphism equivalence was obtained.

## Current-source addendum for 350737

The fetched September 2026 primary arXiv:2609.20237 explicitly identifies Fox–Wigderson's all-distinct conjecture as Conjecture B and derives its Corollary 1.2 from its new homomorphism-threshold bounds together with previous chromatic/removal-threshold results. For odd m>=5 the four thresholds form the strict chain 0 < delta_hom < 1/m < 1/4, with delta_chi=0. Thus an all-distinct construction is public already. This does not realize all admissible relative orders from the literal record. Only this deduction and the stated new bounds were read; their entire proof chain is not independently audited here.
