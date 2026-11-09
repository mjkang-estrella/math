# Ordinary mechanisms and stopping points

This is discovery work only. No Lean, solver, numerical search, enumeration, or Pi execution was performed. None of these routes is a qualified new campaign candidate. The exclusions below distinguish a complete reduction from an unproved shortcut.

## 320028: complete source/classical reduction, excluded

Read Drake's two version-labelled target passages, the published JIS PDF, the construction on pp. 13–15 of the arXiv text, Propositions 12–13 and Figure 11 (rendered and inspected). The source operations have literal lengths +2 (append Ud) and +4 (lift: add two upsteps, one ordinary downstep and one special downstep).

Write des(pi) for the number of adjacent descents. We obtain, by induction on n,

    pathlen(pi) = 2 n + 2 des(pi).

Delete the largest letter n. If it was last, the source constructs its path by append, which adds 2 and does not change des. Otherwise its insertion after k letters is good insertion. By source Proposition 12 those k letters are exactly [k]. When k>0, the old boundary is an ascent, because every prefix value is at most k and every suffix value exceeds k. Inserting n replaces this ascent with an ascent and one descent. For k=0 it introduces one initial descent. Thus des increases by one, while the literal lift adds 4. Deleting n preserves avoidance, so this induction covers every permutation, including the empty permutation of length zero.

For completeness, the usual decomposition of a 231-avoider at its maximum is A n B, with all values of A smaller than all values of B. Its descent count is des(A)+des(B)+1 if B is nonempty, otherwise des(A). Thus the formal generating series C(z,u) satisfies

    C = 1 + z C (1 + u(C-1)).

The unique series with constant term 1 gives the classical Narayana descent distribution. Substitution z=u=q^2 gives

    q^4 C^2 + (q^2-q^4-1) C + 1 = 0,

and hence exactly the square-root formula in the literal record (the branch with constant term 1). This also specifies the source's zero-based Narayana index: N(n,k) counts k descents, so for n>0 it is binom(n,k) binom(n,k+1)/n. The empty case contributes 1.

Disposition: EXCLUDE complete source-operation/classical Narayana bridge. This is an explicit full reduction, not exclusion merely because it is short. No claim that an earlier paper explicitly states Drake's exact resolution. The classical descent distribution is documented, for example, in Han–Mao–Zeng, FPSAC2020/54-Han, section 2.9 (search-located passage; complete body not audited here). This lane makes no worldwide priority claim.

## 321204: Stern coefficient route, unclosed

Source Conjecture 6.7 uses B0=0, B1=1, B2m=t Bm, B2m+1=Bm+Bm+1 and C(a,b)=binom(a,b). It maximizes individual positive-degree coefficients over a dyadic interval. The coefficient expansion has an x/t typography mismatch, which does not authorize changing the statistic. Degree zero makes the source's inner maximum empty for B1; that is an endpoint-definition issue and gives no discovery credit.

Route 1: induction on individual polynomials. The even branch merely shifts coefficient indices; the odd branch adds coefficients of adjacent polynomials. An upper bound for each polynomial alone therefore gives twice the desired bound, not the claimed bound. The adjacency correlation cannot be discarded.

Route 2: retain the ordered pair (A,B)=(Bm,Bm+1). Appending a binary digit gives respectively

    (t A, A+B),    (A+B, t B).

These are exact semantic recurrences, not a solver encoding. They retain the correlation lost above. The coefficient in degree i counts hyperbinary expansions of m-1 with i ones, as already stated in the source introduction. A possible proof would inject these expansions, with a carefully chosen degree/valuation shift, into size-j nonadjacent subsets of an (n-1)-path; those have cardinality binom(n-j,j). The crucial injection for arbitrary binary words is missing. The degree cannot simply be identified with j: B(2^n)=t^n has a nonzero coefficient at degree n, whereas the proposed Fibonacci polynomial has degree floor(n/2).

Route 3: evaluate at t=1 and use Stern/Fibonacci maxima. This bounds the sum of coefficients, which is substantially weaker than the maximum binomial coefficient. It supplies neither the sharp upper bound nor attainment. A full proof also needs an explicit dyadic index and coefficient reaching the largest binomial value, with all parity/valuation cases covered. No such index family is proved here. Small hand recurrences (for example B11=1+3t+t^2, B21=1+4t+3t^2) are consistency checks only, not evidence of a uniform theorem.

Disposition: PARK. The pair recurrence is a meaningful exact starting point, but there is no qualified finite certificate, uniform injection, sharp extremal induction, or credible complete route. Source 1102.5109 and citing 2511.03847 were fetched; selected introductory/results passages do not settle this coefficient problem. Their full proof bodies and all later coefficient literature were not audited. No open-status certification.

## 317723: recurrence spectrum route, unclosed

Read Raff's definition Gk(n)=Pk square Pn, transfer theorem 6.1, corollary 6.2, Conjecture 3, the printed small recurrences, and the beginning of the k=2 combinatorial proof. The target is minimum recurrence order, as confirmed by Raff's thesis/author slides found in search, rather than merely the existence of an annihilating recurrence of that order.

Route 1: the published Bell-number transfer matrix gives an annihilator of order at most Bk. Cayley–Hamilton does not reduce this to 2^(k-1), and characteristic polynomial factorization alone does not prove minimum order.

Route 2: diagonalize the path Laplacian. Its nonzero eigenvalues are lambda_j=2-2 cos(pi j/k), j=1,...,k-1. The matrix-tree/product and Chebyshev route suggests factors

    U_(n-1)(1+lambda_j/2) = (alpha_j^n-alpha_j^(-n))/(alpha_j-alpha_j^(-1)),
    alpha_j + alpha_j^(-1) = 2 + lambda_j, alpha_j>1.

Expanding their product gives at most 2^(k-1) exponential terms. This is a route sketch: the spanning-tree normalization and exact sequence bridge must still be proved before using it as a result.

Route 3: a sharp lower bound requires all relevant signed products of the alpha_j to remain distinct, or a precise account of collisions and cancellations. Distinct lambda_j do not imply this multiplicative independence. Positivity only isolates the largest product. The symmetry lambda_j+lambda_(k-j)=4 does not itself imply product independence. A counterexample would require an explicit collision with a proved recurrence reduction; none is supplied. The printed k=2 and other small recurrences are not new witnesses. No transfer-matrix execution was run.

Disposition: PARK without a credible full uniform route. Missing lemmas are the exact spectral count bridge and signed-product noncollision (or a genuine finite collision). Generic recurrence fitting or a solver encoding is not a candidate.

## 321477: acyclic-space obstruction has an actual public predecessor

Read all three target versions, latest Theorem 2.28/Remark 2.29 homotopy formula, weak-map definition and Proposition 3.17 proof. Early versions mistakenly repeat M in the homotopy-equivalence hypothesis; v3 uses N, matching MathDB. The assumption is noncontractible, not nonzero reduced homology. Therefore a finite acyclic noncontractible X defeats a Betti-number argument.

The public ProbXiv page fetched in this lane contains a dated Aug 17, 2026 full proposed counterexample, not merely an abstract or an open label. It takes a punctured Poincare homology sphere X, rho=3, M=U(2,3), and N the rank-two matroid with {1,2} parallel. Canonical immersions give wedges of X*X and suspension X, both contractible; the identity weak map identifies the two distinct singleton flats. This agrees with the source homotopy formula and the rank inequalities. The page explicitly describes the acyclic/noncontractible mechanism, its topological dependencies, and the actual finite matroids. Its automated judgment is not accepted as independent verification, but its pre-existing mathematical content excludes rediscovery of this route. The Poincare/Whitehead bridges were not independently formalized or reconstructed here.

Disposition: EXCLUDE already public exact mechanism; additionally a domain-hypothesis loophole under the campaign standard. Do not hand the same witness to Pi for discovery credit. Replacing X by a homology-detectable space silently changes the literal problem and is not permitted.

## Other finite temptations

321007: with p=3,q=5 the interval hypothesis is valid and |A|=6. Taking A={1,2,3,4,5,6} modulo 15 is not centrally symmetric (1 belongs but -1 does not), hence is not any displayed +/- progression. This only exploits omission of an explicit incompleteness hypothesis from the literal standalone quantifiers. Indeed its subset sums cover all residues: positive ordinary sums cover 1,...,21 by elementary interval induction, including 15. It is not an intended incomplete-set witness. EXCLUDE domain/wording correction, and PARK the intended classification. No silent addition of A incomplete.

320998: central reflection about c pairs every point except c and would synchronize congruent goal sets, preventing a fair win, if the game were played off c. In the actual plane Player 1 can use c, breaking that involution response. Choosing c only after the first move does not fix an involution for all future moves. A fixed-point-free translation does not give disjoint involution pairs, so the same strategy proof fails. The source explicitly discusses this obstruction and prints winning finite hypergraphs; no Euclidean realization with all unintended congruent copies controlled is provided. PARK.

321315: exactness is a global minimum variable-count requirement for a fixed conflict matrix (equivalently maximum deficiency), not a property certified by small deficiency alone. Winkler's delta>=1 conclusion controls the whole clause-set, whereas matching leanness excludes nontrivial matching autarkies and needs subset conditions. A Hall-deficient subset cannot simply be deleted: the remaining conflict matrix need not be a connected graph's distance matrix. The source's 'proven true' sentence near its introduction concerns a different fixed-deficiency polynomial-time conjecture, not Conjecture 2.7.3. PARK; neither an exact countermodel nor the required subset lifting lemma is supplied.
