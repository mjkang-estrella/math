# Ordinary attempts and exact unpaid bridges

This is discovery/ordinary ideation only. No Lean, solver, numerical search, or enumeration was run. None of these arguments establishes a new full-scope result. Source and registry qualification remains incomplete. The three sustained routes below were selected after literal extraction and historical source-family screening. They are not Pi assignments.

## 360924: cycle packing, core joins, and source block families

The forbidden family is three VERTEX-disjoint cycles of arbitrary lengths at least three. Saturation means the graph itself has no such packing, while EVERY missing edge creates one. Counting only triangles is insufficient.

First route: give every cycle access to a small complete core. For K2 joined to an independent set, every cycle uses core vertices. Even after adding an edge between peripheral vertices every cycle still meets the two-vertex core, so three disjoint cycles remain impossible. Thus the apparent sparse obstruction is not saturated; one cannot infer saturation merely from having packing number two.

Second route: increase the core. For K5 joined to an independent set, each cycle before an insertion needs at least two core vertices, so there cannot be three. Adding an edge xy in the independent part allows a triangle on x,y and one core vertex; the four remaining core vertices and two other peripheral vertices give two further disjoint triangles. At n>=14 enough peripheral vertices exist. Its edge count is 10+5(n-5)=5n-15, exactly n+1+4(n-4), the top endpoint already printed in the conjecture. More decisively, it is the source's S(n,5) in Observation 2.1(i). This is a complete published-recipe reduction, so no candidate or separate credit.

A proposed intermediate core, K4 joined to one peripheral edge ab and isolated peripheral vertices, also fails. Insert ax with x formerly isolated. The peripheral graph now has only edges ab and ax, which share a. Any cycle using just one core vertex must use a peripheral edge, so at most one cycle of a disjoint packing can use one core vertex. The other two each need at least two, demanding five core vertices. No three-cycle packing appears. This refutes this construction route without computation.

Third route: add a peripheral cycle or glue one-cycle blocks. K2 joined to C_(n-2) has 3n-5 edges and is precisely the source W(n,2) in Observation 5.2. Gluing complete blocks, split cores S(b,2j-1), wheels and path-augmented wheels along the prescribed vertex is the source's Lemma 2.2. Its proof uses residual cycle packings avoiding attachment paths. The construction equations in Theorem 2.3 and the two special examples before Conjecture 5.3 already account for their displayed counts. No unprinted block satisfying the residual path property was found. Varying sizes in those same recipes cannot be called source-new based on degree sequence alone.

Unpaid: a specific graph outside all compared recipe families, a graph-wide no-packing argument, a packing after each nonedge, an exact count outside the conjectured spectrum, and latest-journal/citing-body comparison. The 2025 journal body returned 403; no alternate access attempted. No witness or meaningful bounded executable search assignment exists yet.

## 379886: an actual graded integer presentation

Let A_m=Z[x]/(x^m), with deg x=1. Use the unreduced chromatic cochain complex of Definition 2.3 with M=A. For K5 and j=3m-2, a two-edge spanning subgraph has three components, so its degree-j cochain module vanishes: each component contributes degree at most m-1, totaling at most 3m-3. Consequently H^(1,j)=C^(1,j)/im(d0); there is no unpaid kernel-of-d1 computation at this grading.

For each of the ten edges e, a basis vector in C1 has four component exponents b in [0,m-1] with sum 3m-2. Set deficits c_i=m-1-b_i. Their sum is m-2; the upper bounds are then automatic. Thus there are binomial(m+1,3) basis vectors per edge, or 10*binomial(m+1,3) overall. A basis vector of C0 is a five-tuple a in [0,m-1]^5 with sum 3m-2. Its d0 image is the sum over edges uv whose a_u+a_v<m, replacing those two exponents by their sum and leaving the other three unchanged. The empty-state incidence signs are all positive. This describes concrete integer relations and the literal source-to-presentation bridge at the ordinary level.

A rational rank computation would establish only the free rank, not the torsion. Even torsion orders would not specify the isomorphism type. The proposed answer has a parity transition between five and ten Z2 summands and ten Z_m summands, plus exceptional m=2 and m=3 behavior. It needs actual integer unimodular reductions or equivalent bidirectional presentation maps, uniformly in m. Symmetrizing the presentation over S5 by averaging introduces denominators and can destroy exactly the 2- and m-torsion at issue.

The m<=9 cases are already printed as checks; reproducing them gives no discovery. The rendered original page 35 confirms Conjecture 8.12's cases, including m=4, not an OCR-based exponent repair. Neither a uniform reduction nor a discrepancy at m>=10 has been proved. The source's known m=3 theorem and other complete-graph conjectures must not be conflated with this all-m problem. No Smith calculation or matrix enumeration was executed. This presentation is useful mathematical localization, but not a qualified Pi certificate plan: no finite obstruction is predicted, no all-m reduction is ready, and later chromatic-cohomology gluing literature remains uncleared.

## 317236: preserving two composition restrictions

E_I^J is the coefficient of L_I(q) in S^J(q), not a generating polynomial defined to equal the conjectured answer. The source actually defines the bases and prints transition matrices in Section 3.8. Defining E by the right-hand side would therefore formalize a tautology rather than the MathDB assertion.

First route: standardize words and use a permutation statistic. The source already gives the bijection from packed words to pairs (sigma,J) with recoil-composition refinement; 21-1 and 31-2 merge into the 31-2 statistic after standardization. This is printed Conjecture 6.2, equivalent to 6.1. It does not prove the algebraic transition coefficient equals that statistic.

Second route: induct by inserting/deleting the largest letter. This changes its descent-top membership, can remove the descent of its predecessor, and changes adjacency in the generalized patterns. The state (I,J) alone does not specify the neighboring values needed for the weight change. An insertion recurrence must retain more local information and then prove that forgetting it agrees with the algebraic basis recurrence. No such closed recurrence was derived.

Third route: use an inv/major-index equidistribution or reverse complement. Ordinary Mahonian equidistribution does not preserve both the Genocchi composition and evaluation restrictions. Reverse complement changes descent tops to bottoms and 31-2 to 2-31; the source itself notes that the J=1^n specialization is related to already known tableau enumeration. That special case is not the full composition-refined theorem.

The five printed words for I=(3,1), J=(2,1,1), namely 1132, 1231, 1312, 2311, 3112, have printed weights 0,0,1,1,2, giving 2+2q+q^2. This is a source control, not a new finite witness. No discrepant coefficient or full bijection is established. All three arXiv versions and the author manuscript retain the conjectural appendix; journal/citing proof qualification is incomplete.

## 318839: explicit classical/source reduction and scope caution

Assume C is the vertex set strictly selected by a separating linear functional l on a realization of P, as in the source definition of a realizable cutset. Choose the sign so selected vertices have l>c and unselected have l<c. For any selected vertex of a facet F that is not l-maximal on F, an incident edge of F improves l: the feasible tangent cone at a vertex is generated by its incident edge directions, so absence of an improving edge would imply global maximality of l. Following improving edges terminates at a maximizing vertex because the graph is finite. Every vertex on the path remains selected. The maximizing face has connected graph; its vertices are selected whenever C intersects F. Hence all selected vertices in F lie in one component of the induced graph. This is stronger than the conjecture's common-subfacet antecedent.

This is the linear-programming edge-ascent argument plus the source's own Theorem 3.1/footnote convexity observation. It is an explicit complete classical/source bridge, not an exclusion based on shortness. If instead C is any abstract subset passing three combinatorial tests, no separating functional is available and the argument does not prove that reading. The source's surrounding purported nonrevisiting/Hirsch proof cannot serve as a trusted general theorem. This ambiguity blocks a literal candidate; an endpoint correction or broader automatic definition is not new credit.

## Remaining dispositions

Per-ID exact source locations, failed mechanisms and missing lemmas are in results.json. In particular: 318554's cheap pebble extraction is unproved for arbitrary configurations; 318555 is the source's own complete bridge from 318554 and pi(G)<=1.5n+2, not an independent achievement. 318757 is only proved at k=2 by Keith, so no all-k published-resolution claim was made. 377673's conditional hypergeometric sum and ASM total do not prove its nest distribution. Infinite Sprouts, tournament, triangulation and representation targets have no credible uniform route here. Six targets have actual published-resolution/refutation evidence and are not promoted.
