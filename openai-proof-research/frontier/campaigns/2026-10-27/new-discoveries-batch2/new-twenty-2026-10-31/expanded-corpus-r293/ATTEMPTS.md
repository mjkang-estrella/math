# Ordinary proof attempts and exact gaps

No complete new endpoint survives. These are mathematical deductions, not execution requests. No Lean, numerical diagonalisation, enumeration, solver or child agent was used.

## 360537: star Hamiltonian

The actual Hamiltonian is the unnormalised sum H = sum over edges of (I minus the Haar moment projector on that edge), acting on k copies and k conjugate copies of each local space. The source's Definition 5, not the average moment operator alone, fixes the gap normalization. Conjecture 1 requires gap greater than 1/2 for both k = 2 and k = 3 at every star size. Local dimension is another parameter suppressed by the MathDB wording. The n = 1 zero-operator convention is not exploited for credit.

First route: propagate the exact n = 3 and n = 4 formulas using source Theorem 2. Its bound is

    Delta_n >= ((n - 2) Delta_m - (n - m)) / (m - 2).

For a fixed m with Delta_m < 1 this tends to minus infinity as n grows. To obtain Delta_n > 1/2 from this inequality one needs

    Delta_m > 1 - (m - 2)/(2(n - 2)).

The right side tends to one. Thus even an exact fixed-size bound strictly above 1/2 is inadequate. This is an algebraic failure of the route, not missing numerical precision. The source itself flags this limitation. Reading the square-H proof confirms that its loss arises from the combinatorial multiplicities of overlapping edge pairs, not a normalization typo that could simply be removed.

Second route: add one leaf and use positivity. Although H_n >= H_(n-1) tensor I, the latter has a larger kernel. A vector orthogonal to the new kernel can have a large component in the old kernel, so its Rayleigh quotient is not bounded below by the old positive spectral gap. Reducing the problem to two projectors illustrates the obstruction. In a nontrivial two-dimensional principal-angle block, delta(I-P) + (I-Q) has smaller eigenvalue

    (delta + 1 - sqrt((delta - 1)^2 + 4 delta c^2))/2,

where c is the relevant overlap cosine. As c tends to one this approaches zero. Positivity alone cannot establish a uniform inductive bound. A useful next lemma would explicitly control these overlaps for the Haar moment ground spaces at both moments, including all permutation sectors and all local dimensions. No such lemma was proved.

Third route: exploit symmetry of the leaves. Appendix B writes the second-moment Hamiltonian in terms of a central Pauli spin coupled to collective leaf spins. It then replaces the latter by classical variables and selects the maximal total spin, obtaining the heuristic asymptotic value 1 - 1/q^2. This does not prove an operator inequality in every spin sector. Even a rigorous asymptotic statement would leave every finite intermediate size and the third moment. Needed: an exact sector decomposition plus a lower bound on every nonzero sector eigenvalue, with ground multiplicities identified. No finite counterexample or full bound was obtained. Park; no Pi plan.

## 339877: identity fibers of word maps

The literal endpoint is N_w(1) >= |G|^(d-1) for every word in d variables on every finite nilpotent G. Nonidentity fibers are outside this endpoint. A current search exposed an Amit-Ashurst nonidentity-fiber counterexample lead; it is not a refutation here and its construction was not adopted.

First route: reduce by Sylow products and then by central quotients. Word evaluation on a direct product is componentwise, so solution counts multiply. It suffices to solve finite p-groups, but this is a reduction, not a solution. Let Z be a central subgroup of order p, Q = G/Z, and e_j the exponent sums of the variables. For central z_j,

    w(g_1 z_1, ..., g_d z_d) = w(g_1, ..., g_d) product z_j^(e_j).

If some e_j is nonzero modulo p, the map Z^d to Z given by those exponent sums is onto, and exactly p^(d-1) lifts of every quotient identity solution evaluate to 1. Quotient induction then yields |Q|^(d-1) p^(d-1) = |G|^(d-1) solutions. This is compatible with the source's already proved uniform/surjective case (Lemma 7 and Theorem 8), so it is not a new full result.

If all e_j vanish modulo p, central changes leave w unchanged. Each quotient solution tuple either has all p^d lifts solving w=1 or none. Its central obstruction in Z is well-defined. If M denotes the quotient solution set and M_0 the tuples with trivial obstruction, the needed inequality is

    |M_0| >= |Q|^(d-1)/p.

The induction hypothesis only gives |M| >= |Q|^(d-1). It supplies no lower bound on the identity obstruction fraction. Central translation cannot balance these classes because it fixes their obstruction. A balance lemma for this obstruction is the exact missing step, not an assumed uniform-fiber theorem. No proof of it was obtained.

Second route: use character positivity. If the counting function N_w is a character with nonnegative multiplicities, then |N_w(g)| <= N_w(1). Summing N_w(g) over G gives |G|^d, so |G| N_w(1) >= |G|^d. This closes the desired inequality under the character hypothesis. The actual source records class-two results, and a primary 2020 companion search likewise limits the general claim. No justification was found for arbitrary higher-class words. It would be circular to impose that missing positivity as an axiom. No source-qualified full proof; park.

## 354997: pyramidal and quasi-pyramidal growth

Definition 4.1 requires the closure of the added region to be a pyramid attached along a facet, with the larger object a polytope. Finite chains generate pyramidal growth. Transfinite growth additionally allows limits of ascending chains. Definition 4.2 permits intermediate smaller polytopes P_i' inside P_(i-1), still containing the initial P, followed by a pyramidal extension to P_i. The defect is an infimum of accumulated approximation costs; mere existence of one chain does not establish zero defect.

First route: insert vertices of Q one by one into P. The new cap conv(P,v) minus P is the union of pyramids over facets visible from v. Inserting the full cap is not generally a single pyramidal extension. Triangulating the cap produces a decomposition of the difference, but an arbitrary partial union of its cells with P can be nonconvex. Hence a triangulation is not a valid chain in this poset. Shellability of a triangulation, without convexity of these partial unions, does not fix this failure. Needed: a convex stacking order or an explicit pair proving no such finite order exists. Neither was obtained.

Second route: use quasi-pyramidal approximation to bypass convexity losses. This must give, for every positive eta, an admissible finite chain whose total defect is below eta while keeping the original P inside every intermediate smaller object. Local small perturbations alone do not bound the accumulated cost or preserve that containment, especially when P and Q share boundary faces. No such construction was proved.

Third route: induct on dimension using Theorem 4.3(c). Its premise is that *pyramidal* growth equals inclusion in dimension d; its conclusion concerns *quasi-pyramidal* growth in dimension d+1 with zero defect. One cannot feed the conclusion back as the next premise. In particular the source already proves dimension-four quasi-pyramidal growth; that does not prove all dimensions or the negative dimension-four pyramidal assertion. The field-of-definition strategy after Conjecture 4.4 also lacks its proposed field constraint; arbitrary real pyramid apices cannot simply be assumed rational. v1 and v2 were retained; the original cited pyramidal-growth proof and all later citing bodies remain unread. Park.

## Explicit known-result reductions

348040: Dey Definition 4 requires min(a_i,b_i)^2 >= max(a_(i-1),b_(i-1)) max(a_(i+1),b_(i+1)). Shankar Theorem 6 proves the four descent/excedance sequences are ultra-synchronised for n >= 5. The binomial normalization introduces the factor B_i^2/(B_(i-1) B_(i+1)), at least one by binomial log-concavity. Taking only the two descent sequences weakens the minimum/maximum inequality in the correct directions. For n = 1,2 there is no internal index. For n = 3 the even/odd descent rows are (1,2,0) and (0,2,1), so 4 >= 1. For n = 4 they are (1,5,5,1) and (0,6,6,0), so both internal inequalities reduce to 25 >= 6. These small rows follow from the classical Eulerian and signed Eulerian recurrences, not an executed permutation enumeration. This closes the full literal claim by a routine public bridge. The journal body was denied with HTTP 403; the public 2024 proof predates this task independently of that gap. Do not recount the related r198 result 348041.

343103: Ahlbach-David-Oh-Wu Definition 1.0.1 uses the last shifted copy in Rect(T^(q)); stabilization means its entries do not change rows. Their Theorem 1.0.4 has precisely weakly decreasing row sizes and concludes stab(T) <= r. The preceding source persistence lemma says stabilization continues for larger q, so this proves stabilization at r. The final proof uses Greene sums, the optimal lattice paths in Lemma 4.0.2, and adds/removes the final column to obtain row-length increments lambda_j. Since jeu-de-taquin can only move entries upward, equality of those increments forces no vertical moves in the final copy. Both versions of the follow-up were preserved, and the final proof and flip-lemma passages were read. Figure captions/constructions were read in extracted text; no claim of visual inspection or journal/correction exhaustion. A publicly printed full-scope theorem is enough for zero novelty here.

336022: The source itself separates its negative constant-size theorem from its doubly logarithmic upper-bound Conjecture 3. Its proof constructs almost invariant sets in affine groups, giving resistance below a constant times log log |G|; this is fully consistent with expansion at a larger constant times log log |G|. It cannot refute that upper bound. The literal epsilon > 1 error is immediate from nonnegativity of norms but is an excluded domain correction. No new intended-scope endpoint is claimed.
