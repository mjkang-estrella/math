# Ordinary proof work and exclusions

This is discovery work only. None of the following is nominated for acceptance or Pi execution. No Lean, enumeration, solver, spectral numerical calculation, or child agent was run. The three explicit literal obstructions below are excluded source/domain corrections. They must not become three candidates in a later handoff.

## 318461: complete literal obstruction, excluded source construction

Take the loopless graph with edges 12 and 34 and configuration (1,0,1,0). Its maximum degree is one. In the unrestricted game, firing 2 then 4 gives zero, so ML=0. In each component, the nonzero configurations are 10, 11, 01. A valid move at the on endpoint of 10 gives 11; a valid move from 11 gives 10 or 01; from 01 it gives 11. Thus no valid move reaches 00, and every reachable global configuration has at least one light in each component. Initially there are two lights, so ML*=2. The claimed gap is 2>1.

For disjoint unions, projection of any move sequence to each component is a legal move sequence there; conversely, concatenate component move sequences. This proves both minimum-light numbers are additive. Source Example 4 gives precisely the one-light obstruction on K2 (m=1), so the above graph is just two disjoint copies of a printed construction. Section 1 has no standing connectedness assumption; Lemma 17 explicitly introduces connectedness when needed. The literal MathDB and Conjecture 16 fail, but repairing them to connected graphs is a domain correction. Zero credit; no formalization requested. In connected graphs the source's Lemmas 17–19 and rake Lemma 24 do not immediately extend: the latter progress measure uses a unique parent and disjoint branches. With cycles, path propagation can change vertices already settled. No universal degree-bounded error support lemma was proved.

## 321341: complete characteristic-two obstruction, excluded endpoint

Set p=k=2 and a=b=(0,1) in F2. The identity permutation produces sums (0,0), while the transposition produces (1,1). In each case the two a-values differ, violating the collision implication. These are all permutations of two indices. This refutes the literal all-prime statement. The source motivates Conjecture 11 using an odd-order group; p is therefore odd in the preceding motivating reduction. Calling this an odd-prime repair gives no substantive campaign result.

For odd p, matching equal-valued entries first is not justified: it can remove the flexibility needed by the remaining entries. An integer rearrangement attempt would maximize the sum of squared lifted sums. Over the integers, exchanging two matched b-values changes that objective by 2(a_i-a_j)(b_j-b_i). A collision in Fp, however, means equality only modulo p; wrapped sums have different integer lifts, so this exchange argument supplies no monotone collision-reduction potential. Replacing squares by residues loses the ordered-sign argument. Also Arsovski's Snevily theorem concerns distinct input lists in an abelian odd-order group, whereas both lists here allow repetitions; expanding repeated values into a larger group changes the sum-equality relation after projection. The missing step is a matching with no cross-type sum collision for arbitrary two multisets, not distinctness of lifted sums. No odd-prime candidate or finite witness is supplied.

## 377305: complete literal obstruction, excluded hypermetric-scope correction

The source defines H(b) for every integral b with sum one, not only facet normals of CUT. Put b=(2,2,-3). Write Sij=dij+dji and use the valid-inequality orientation F=-H. Then

F = -4 S12 + 6 S13 + 6 S23
  = 4(S13+S23-S12) + 2S13 + 2S23.

The first summand is four times the sum of OT12,3 and OT21,3. The last two are sums of non-negativity inequalities. All are nonnegative on QMET3 and hence on OMCUT3. Equality forces S13=S23=0; nonnegativity gives all four incident directed coordinates zero. The two triangle inequalities then force d12=d21=0. Thus the equality face is only the origin. OMCUT3 has full dimension six (source introduction and Table 2), so this is not a facet. This is not a non-oriented triangle normal: its three symmetric coefficients have ratio (-4,6,6), rather than (-1,1,1).

This only exploits the overbroad word 'any'. Theorem 8 already forces symmetric oriented-multicut facets to correspond to CUT facets, and the paper's claimed checks through seven points plainly cannot mean checking every integer b. The intended hypermetric-facet reading is not disproved. No source-modified object or known nonfacet is eligible for credit. Likewise the literal title 'classification' is misleading: Conjecture 3 asserts that listed inequalities are facets, not that no other facets exist; printed non-hypermetric facets do not refute it.

## 377303: finite local geometry, not a completed full-scope route

The source proves the conflicting-pair nonadjacencies (Theorem 6), and checks the converse through n=7. The useful semantic certificate for adjacency is dimension n(n-1)-2 of the common equality face. A positive combination of tight oriented multicuts with no additional facet equality would prove the needed ridge in OMCUT and QMET simultaneously. This is stronger than merely producing a quasi-semimetric satisfying two equalities: such a vector may lie on additional equalities, and membership in QMET does not imply membership in OMCUT.

Attempt 1: start with all off-diagonal distances one and set the two selected NN coordinates to zero. Even if the two directed zero edges have no directed two-edge chain, this introduces triangle equalities (one leg zero, other leg one, opposite distance one). Thus the naive point does not certify codimension two. If the zero edges form a directed path, the source's nonadjacency forces a third zero coordinate anyway.

Attempt 2: alter positive coordinates by distinct small perturbations compatible with the zero edges; for a zero i→j the required strict comparisons are d_iw<d_jw and d_wj<d_wi. These local orders suggest a directed-order construction, but for triangle/triangle pairs the tight equalities propagate through a different set of comparisons. No uniform perturbation assignment for all non-conflicting pair types was established. Averaging ordered partitions also requires an explicit separating partition for EVERY third facet and independent rank witnesses; no such universal partition construction was found. Small computed cases are source-known. Park rather than send a generic LP enumeration to Pi.

## 358756: exact moments bridge, unresolved run reconstruction

Read source Section 2, proofs of Propositions 3.1–3.2, and Section 5 Conjecture 5.2. An occurrence is an index subsequence, not a contiguous factor. Trivial equivalence is generated by reversal and complement. Both preserve the full distribution by explicit bijections on ambient words. The source already recovers run-size multiplicities via n=l+1 and gives all formulas for k≤4; these are not new invariants for credit.

A concrete further route is through overlap moments. For t≥1 define M_t(n,p)=sum_w binom(c_p(w),t). This counts a word together with an unordered t-set of distinct occurrences. If the union of those index sets has size u, compress its ordered positions to [u]. Let C_t,u(p) count t-sets of distinct increasing l-subsets of [u] covering [u], whose imposed letters agree at all overlaps. Then

M_t(n,p) = sum_{u=l}^{tl} C_t,u(p) binom(n,u) 2^(n-u).

Proof: choose the union positions, choose their compressed compatible occurrence set, and fill the n-u unconstrained positions freely. Every marked word has a unique such description. Conversely each description gives exactly one marked word. For fixed t the functions binom(n,u)2^(n-u) are linearly independent after division by 2^n, since they are scalar multiples of distinct-degree binomial polynomials. Hence strong Wilf equivalence implies equality of every overlap coefficient C_t,u. Conversely equality of every moment at fixed n gives equality of the finite occurrence distribution by downward binomial inversion, since c_p(w)≤binom(n,l).

This is a sound semantic bridge but not a solution. For t=1 the coefficients only recover length. For n=l+1 the source already recovers the run multiset. Swapping separated runs with the same size multiset need not preserve higher overlap data; nor does the multiset determine the ordered run composition up to reversal. The precise missing reconstruction lemma is that all C_t,u determine that composition up to reversal. Pair-overlap coefficients aggregate many alignments, so there is no licensed extraction of each individual autocorrelation entry. No proof that pair moments suffice, no unequal trivially inequivalent pair with all moments equal, and no finite cutoff guaranteeing all-n equivalence was found. A bounded histogram collision is not a witness. Park; no numerical search requested.

## 379766: concrete realization bridge and failed induction

Theorem 4.1 defines independent sets as lattice points of sum n-1 with at most k points in every translate of the simplex of size k; bases have size n. Read its saturated-simplex exchange proof, regular subdivision definitions, and Proposition 8.2's colored-poset proof. A regular triangulation corresponds to a common generic height array w_ij with tight spanning trees of K_n,d. A proposed basis specifies locations (degree vectors) of pure trees, not the trees themselves.

Attempt 1: use matroid exchange to place one extra simplex inductively. The source's saturated-simplex merging proves independence exchange, but does not produce any height array. In particular, one may preserve all translate occupancy inequalities while creating a directed cycle of required strict height comparisons. There is no implication from a matroid exchange to a coherent subdivision flip proved here.

Attempt 2: force all desired pure trees simultaneously using their height equalities and inequalities. A valid nonrealizability witness must rule out EVERY assignment of pure trees to the basis locations, not just one assignment. A circuit dependence of one choice is insufficient. A positive realization must also have exactly the prescribed pure-simplex locations after generic perturbation; loose height feasibility is insufficient. No specific basis and universal incompatibility argument was found, and no arbitrary-basis height construction was proved. This remains a concrete geometry gap, not a proposed generic solver task. Later spread-out-simplex/tropical-oriented-matroid bodies and journal clearance are incomplete.

## Remaining targets

The twenty per-ID entries in results.json state the other precise gaps. Uniform/famous targets were parked promptly. No work on Delta377613, flow375537, or Ramsey359209 was repeated. No CANDIDATE.md is produced because no eligible complete ordinary mechanism survives.
