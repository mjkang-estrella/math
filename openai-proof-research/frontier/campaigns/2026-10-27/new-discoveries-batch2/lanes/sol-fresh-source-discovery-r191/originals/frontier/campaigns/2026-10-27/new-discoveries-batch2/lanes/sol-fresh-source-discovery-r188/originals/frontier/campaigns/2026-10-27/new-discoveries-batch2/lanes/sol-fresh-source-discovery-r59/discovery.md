# r59: Ferrers non-nesting rook source question — unresolved, credit 0

## Scope and source history

Two fresh targets were screened; no exhausted or active family was reinvested in.

1. Aluffi–Chen–Marcolli, *Log concavity of the Grothendieck class of Mbar_0,n*, Conjecture 1: for **every n>=3**, the half-degree Poincare/Grothendieck polynomial has only real zeros. EXCLUDED. Berczi–Kiem arXiv:2605.29151v1, Theorem 1.1, gives exactly this and simple negative zeros for n>=4. Actual Sections 2–4 were read, including the bivariate deformation, weighted Rolle identity, both endpoint limits, and root-crossing degree count. No independent proof investment or credit.
2. Selected: Alexandersson–Jal arXiv:2410.00127v2 (4 April 2025), Conjecture 6.1. For **every finite partition lambda=(lambda_1>=...>=lambda_n>0)**, let M_lambda(t)=sum rho t^|rho| over nonattacking rook placements with no SE pair in the English Ferrers board. The complete printed assertion is real-rootedness together with M_lambda << M_(lambda-1) and M_lambda << sum_(i=0)^(n-1) M_(lambda^(i)). Empty shapes have M=1; zero parts are removed. The actual latest arXiv v3, dated 30 June 2026, was retrieved/read early: the Future Work section and this conjecture are omitted. The latest body still defines the same object, proves ultra-log-concavity, and supplies the general skew counterexample. Omission alone does not establish withdrawal, proof, or refutation. No separate journal version is identified on the current arXiv record. Source-status HOLD for a surviving latest-version full conjecture.

Important literal scope issue: the v2 arrows have the reverse of the cited Branden convention. Already lambda=(2) has roots -1/2 versus -1 for lambda-1=(1); the first printed arrow fails. The meaningful substantive real-rootedness assertion is NOT refuted. This is a direction/wording correction, explicitly ineligible, not a new source resolution. All investigations below distinguish the printed assertion from its intended smaller-polynomial-interlaces-larger interpretation. No corrected assertion invented here is promoted to a solved source question.

## Actual closest theorem bodies and same-object screening

* Braun–Jal arXiv:2607.00922v1 (latest v1 checked by abs record), Proposition 3.2: EXACT same-object first-column recurrence below, with its complete occupancy proof. It is public and uncredited here. Theorem 4.1 proves real-rootedness/interlacing for generalized snake words. Its proof, Narayana Turan Lemma 3.1, interlacing Lemma 3.4, and recurrence Theorem 3.5 were read. This is a restricted width-two/squarecase class, not arbitrary Ferrers shapes. For instance general Ferrers polynomials need not be palindromic, whereas these snake polynomials are. No bridge from their restricted theorem to all partitions was obtained.
* Latest Alexandersson–Jal v3 Theorem 4.1 gives ultra-log-concavity, not real-rootedness; its proof uses Lorentzian basis polynomials. Theorem 4.3 and full displayed proof give a non-HPP generalized Catalan matroid at lambda=666333. The specialization t^3(t^3+36t^2+225t+400) has nonreal roots, exact cubic discriminant -602100. It is NOT M_lambda. Thus a blanket HPP argument using lattice-path bases is unavailable, but this is no source counterexample.
* Branden, *On operators on polynomials preserving real-rootedness and the Neggers–Stanley conjecture*, math/0303147, actual preprint Theorem **16** (publisher/search labels it 17): column-strict labelled Ferrers-poset E-polynomials are real-rooted, with cell-addition interlacing. Actual definitions, hook-content equation (7), and proof via diamond operator read. These are order-polynomial transforms on **cells**, not the antichain enumerator M_lambda. For lambda=(2,1), column-strict label order a=2,b=3,c=1 on a<b,a<c gives W=2t and E=2t^2+2t^3, whereas M=1+3t+t^2. No same-object subsumption from that theorem is asserted. Publisher PDF route403 retained; public arXiv preprint body obtained normally, not through access-control evasion.
* Branden 2015 survey actual Section8 Theorems8.2/8.5 require pairwise compatibility/interlacing, not adjacent comparisons of a sequence of unrestricted degrees. They do not justify the failed invariant below.
* Omega named cached Problems/Blueprint bodies: multiset rook-Eulerian Conjecture28 refutation is for fixed-content **words by strict ascents**, not placements by number of rooks. Full quantified claim and actual result statement/commentary read. FerrersLevelCounting/Transfer are Gaussian row-level fiber cardinalities, not zeros of M_lambda. No semantic clearance is inferred just from filenames. Other remote modules not read are not declared cleared.

## Exact combinatorics and the first serious route

A placement can be written as rows i_1<...<i_k with strictly **decreasing** column indices j_1>...>j_k, j_a<=lambda_(i_a). This gives a direct row-state DP: D_j records placements whose last occupied column is j; D_(c+1)=1 initially. Upon a row of length w,

D'_j=D_j+t sum_(k>j)D_k for 1<=j<=w,

and other D_j remain unchanged. The sum of all states is M. Each placement is counted exactly once by its final column, including the empty sentinel. This is an exact all-shape representation, not a root theorem.

Splitting on the first column gives

M_lambda=M_(lambda-1)+t sum_(i=0)^(n-1) M_((lambda-1)^(i)).

If the first column is occupied in row i+1, nonnesting excludes every later row; the earlier rows form precisely the truncated board after deleting that column. This derivation was independently found, then recognized as the already-public Braun–Jal Proposition3.2; no novelty claimed.

Build the board from rightmost column to leftmost. Column heights h are nondecreasing. Keep F_i=M of the first i rows of the already-built board, extending constantly beyond existing rows. A column of height h gives

G_0=1, G_i=F_i+t sum_(j<i)F_j (1<=i<=h), G_i=G_h (i>h).

This is a finite O(n*c*degree) arithmetic algorithm, requiring no enumeration of factorially many configurations. It exposes the genuine remaining closure problem.

## Failed generic closure and graph route

Adjacent root interlacing of F_i and F_(i+1), positivity of coefficients, and F_0=1 DO NOT suffice for column closure. Take F_i=(1+t)^i for i=0,1,2,3. All adjacent pairs weakly interlace. The full-height update has

G_3=2(1+t)^3-1=1+6t+6t^2+2t^3,

whose discriminant is -108, so it is not real-rooted. This is NOT a reachable Ferrers prefix state and hence is NOT a source counterexample. Any induction must exploit extra reachable-state structure. Checking only consecutive pairs cannot invoke the survey's all-pairs compatibility theorem (degrees of F_0 and F_3 already differ by3).

A second conceivable generic route views M_lambda as the independence polynomial of the cell-conflict graph: two cells conflict if they share a row or column or one is SE of the other. This identification is exact. The graph is not always claw-free: in lambda=(4,4,4,4), center (1,1) and leaves (2,4),(3,3),(4,2) induce K1,3. Therefore the blanket claw-free independence-polynomial theorem does not apply directly. This does not disprove Ferrers real-rootedness.

## Second algebraic route: iterated prefix Turan inequalities

For a current prefix vector F, let (LF)_i=sum_(j<i)F_j, and A_k=(L^k F)_h. The next full-height column acts A'_k=A_k+t A_(k+1) for the active block. Put Delta_k=A_(k+1)^2-A_k A_(k+2). Exact expansion gives

Delta'_k=Delta_k+t(A_(k+1)A_(k+2)-A_k A_(k+3))+t^2 Delta_(k+1).

This suggests retaining interlacing of successive A_k plus Turan inequalities Delta_k(t)>=0 on t<=0, in analogy with the public Narayana proof. But no uniform invariant, including height-extension transitions, has been proved. Even the new mixed coefficient is positive for empty-prefix data: h=3 gives A=(1,3,3,1), Delta0=Delta1=6, mixed coefficient8. For t<0, the cross contribution is negative, so termwise positivity is invalid. Extra discriminant/control inequalities would be needed; the identity itself supplies no such bound.

Finite exact diagnostic: all799 Delta_k tested on all251 nonempty partitions in a5x5 box are nonnegative on the negative halfline (squarefree decomposition and exact real-root counts). These inequalities are neither a uniform theorem nor independently sufficient for all the required interlacings. They are research leads only.

## Exact remaining uniform step and falsifier

The minimal unresolved mathematical step for real-rootedness is: prove that every prefix vector reachable from constant-one vectors through the NONDECREASING HEIGHT column updates above has real-rooted terminal entry. To recover the substantive intended two interlacing clauses, prove in addition the appropriate interlacing between each terminal entry and its first-column predecessor and its prefix sum. A usable stronger induction could establish all relevant iterated-prefix interlacings and Turan/discriminant bounds and show they survive both a column update and extension of the active height; neither closure has been established here.

The strongest mathematical falsifier is an explicit Ferrers partition whose literal M_lambda has a certified nonreal zero, or a reachable prefix violating a proposed needed invariant. The generic cubic is only an obstruction to a strategy. A public same-object all-Ferrers theorem would instead defeat eligibility; no absence of such theorem is certified because current-registry broad freshness remains HOLD. Source omission and the literal arrow problem separately prevent treating the full old wording as a clean current eligible target.

## Verification and limits

run.sh uses hard AS512MiB, aggregate sampled group RSS512MiB, CPU210s, wall230s, BLAS1 via the copied r58 monitor. Exact PASS:251 row-DP/column-DP equalities;69 independently brute-enumerated small shapes;251 real-root counts;502 intended-direction Wronskian nonnegativity tests;799 iterated-prefix Turan halfline tests; published skew polynomial reconstruction and exact non-real-root check; two cubic discriminants. These prove only the stated finite cases and route obstructions. No universal conclusion is inferred.

Solo, only assigned lane writes. No git/shared/other-lane writes, children, external contact, account actions, browser tabs, Lean, paper, PROOF.md, nomination, or count change. Credit0; root owns6additional/36total.
