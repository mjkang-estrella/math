# Mathematical handback — no qualifying endpoint

## 341446–341449: independence roots

Newly read Brown–Cameron, arXiv1812.09775 (downloaded PDF, source-receipts.json): definitions pp1–3; Proposition2.2; Proposition2.4 and its three explicit graph polynomials/proof pp4–7; Lemmas2.5–2.6 and the coefficient-ratio induction in Theorem2.7 pp7–10; tree constructions and Proposition3.5 pp17–19; literal Conjectures4.2–4.5 pp21–22. Not claiming every proof of the paper read. Published version not compared.

Exact semantics: i(G,z)=sum over independent vertex subsets S of z^|S|. maxmod(n) maximizes |z| over all graphs of order n and all their complex independence roots. Tree analogue restricts to trees. Uniqueness means graph isomorphism, not polynomial uniqueness. Source G1 is a central vertex adjacent to two vertices in each of k disjoint triangles; G0 adds an attached K2 and G2 adds a second. Their polynomials are (1+3z)^k+z(1+z)^k, (1+3z)^k(1+2z)+z(1+z)^(k+1), and (1+3z)^k(1+2z)^2+z(1+z)^(k+2), respectively. These are already source constructions, not discoveries.

First mechanism: exact rooted-tree dynamic programming. For root v, let A_v enumerate independent sets omitting v and B_v enumerate those containing it. With child subtrees w,
A_v=product_w(A_w+B_w), B_v=z product_w A_w.
Proof: an independent set omitting v independently chooses either status in each child; including v forces each child omitted. This is an ordinary exact semantic bridge, not yet Lean. Starting with A=1,B=z at leaves gives all coefficients in nonnegative integers.

Second mechanism: sharpen Eneström–Kakeya through consecutive coefficient ratios. If every a_j <= B a_(j+1), that classical theorem bounds every complex root by B. Source already uses this approach with a larger universal bound. The proposed even-tree target B=2^((n-4)/2)+(n+2)/2 is exactly Conjecture4.4, not a widened target. tree_attempt.py checks the integer inequalities on structured trees, and separately evaluates signed i(T,-B). A negative signed value relative to the leading term would give a real-root counterexample by IVT. No negative value was found.

Evidence: all 32,500 nonisomorphic trees of orders6–16 enumerated by NetworkX were evaluated by exact coefficient recursion and uncertified floating root calculation. Full coefficients, edge sets and floats in tree-enumeration.jsonl. 2,004 center-rooted spiders with a length1 arms, b length2 arms, c length3 arms and d length4 arms, a=0..8,b=0..24,c=0..6,d=0..2, even order6..60, passed exact ratio and sign tests. Full outputs tree-structured.jsonl; summary tree-attempt-results.json. This does not prove conjectures or globally certify uniqueness. Floating maxima do not establish equality of tied algebraic roots.

Remaining lemma for341448: a universal bound on all consecutive independence coefficients for even trees, or a different complex-root bound of the exact required size. The source's generic maximum-independent-set induction leaves an exceptional leading-coefficient case; merely substituting the smaller B is unjustified. For341446 the analogous sharper residue-class graph bound remains. For341447/341449 need a stability/equality classification after an actual sharp universal root bound; equality of coefficient bounds alone does not classify roots. No feasible complete Lean endpoint emerged. Ranked strongest unresolved route:341448, but parked at a genuine universal combinatorial lemma.

## 341597: frame energy

Newly read arXiv1901.06096v1 (original source title/limited d+1 theorem) and v3, pp1–3 (energy definition, Gale-dual/tight-frame construction and Lemmas2.1–2.2), selected Theorem4.2 proof conclusion p9, and Conjecture5.1 pp9–10. The published SIAM version has not been body-compared. v1 does not even contain the later Conjecture5.1; version distinction is essential.

For positive p, E_p(X)=sum_(i!=j)|<x_i,x_j>|^p, with every vector unit in R^d and N=kd+m, 1<=m<d. In the repeated basis, m basis vectors occur k+1 times and d-m occur k times. Therefore its actual energy is
m(k+1)k+(d-m)k(k-1)=d k(k-1)+2km.
Source Conjecture5.1 and the normalized record both print +2k. Example d3,k1,m2 already has energy4, not2. This is only a source-level arithmetic correction, excluded from discovery credit; it is not a significant solution.

Substantive mechanism retained: orthogonal block sums. If configurations X in R^a and Y in R^b are embedded in perpendicular subspaces, all cross terms vanish for p>0, so E_p(X union Y)=E_p(X)+E_p(Y). For a repeated-basis block of dimension a, multiplicity k and excess b, completing with basis directions carrying k or k+1 copies produces a full configuration of dimension d and excess m whenever 0<=m-b<=d-a. Its repeated-basis baseline splits by the same formula, so any strict block improvement propagates without changing k or p. In particular a dimension2, excess1 improvement propagates to every d>=2,1<=m<d: distribute m-1 extra copies among the remaining d-2 basis directions. This explains a dimension-independent upper threshold but provides NO reverse inequality. It is an elementary uncredited bridge, not the requested new result.

The second approach is the source's scalar minimization via kernel frames: Lemma2.2 reduces the energy to M(1/(N-d),p,N). Sharpness for k1 in some ranges and the planar induction do not yield a uniform all-d lower bound for general k. A uniform lower bound with the exact corrected baseline up to the same p0(k), together with p0(k)->2, remains missing. No small parameter witness against the printed +2k is eligible. Parked, zero credit, no surrogate formal theorem.

## 341706–341707: book number

Newly read arXiv1901.09560 Section4.1 pp18–19, Definition4.1, Construction4.2, Conjectures4.3–4.4, and selected tripartite Theorem1.6 proof pp14–15. That theorem bounds vertex triangle-degree, not edge book number, so it is not a full-scope bridge. Original1995 paper located by search, not body-read; later published version not compared. No global novelty clearance claimed.

For a simple template H with positive integer blow-up weights w_i, replace vertex i by an independent set of size w_i and every template edge by all cross edges. Exact formulas:
N=sum_i w_i; e=sum_{ij in E(H)}w_i w_j;
delta=min_i sum_(j adjacent i)w_j;
bk=max_(ij in E(H)) sum_(h adjacent i and j)w_h.
Proof: every vertex in a part has exactly the indicated neighbor parts, and common neighbors of an edge are exactly the indicated intersections. Thus these finite integer formulas describe genuine graphs of the original scope, not graphons or a weaker diagnostic predicate.

The greedy decomposition of rational x uses r=ceil(1/(1-x)), replaces x by xr/(r-1), accumulates (r-2)/r, stopping at x=1. book_attempt.py performs exact Fraction arithmetic with a finite30-step cap (no truncation occurred in tests). It compares bk/N with b(delta/N) and b(2e/N^2). For x3/5, r=(3,10) and b=4/15, while elementary common-neighbor counting gives only 2x-1=1/5. That explicit gap rules out the first naive shortcut. A direct weighted-template search was the second approach: 1,244 nonempty-edge atlas templates on3–7 vertices; uniform weights and31 seeded random weights in1..9, totaling39,808 actual blow-ups. No violation in either source hypothesis. Full per-instance exact quantities and greedy decompositions:book-weighted.jsonl; summary:book-attempt-results.json. This sampling does not prove the conjecture.

Source-scope caution: its beta(x) definition uses e>=x binomial(N,2), but its subsequent 'i.e.' formulation uses e>=x N^2/2; these are not identical for fixed N. No exploit of that mismatch is submitted. The tests use the stronger explicitly stated N^2/2 condition. The minimum-degree conjecture341706 is unambiguous. A proof still needs a universal bound on edge common-neighbor maxima, potentially a structural reduction to EFG coordinate-product constructions; neither source vertex-triangle bounds nor averaging supplies it. Parked, no Lean endpoint.

## Other primary checks

341145: known exclusion, not a candidate. Newly read Taranenko arXiv2210.12405v3 definitions pp1–3, Conjecture3, Theorem7 and full proof pp4–5, and12 explicit pairs of optimal covers. The source states these are counterexamples to uniqueness and coefficient-integrality; e.g. essential weights (13,7,6,6,4,4,4,3,2)/25 with the distinct cover obtained by interchanging highlighted coefficients. PDF text extraction loses bold, so no guessed swap is used. Theorem7 proves equivalence of extremal order2 matrices with selfdual threshold functions; the subsequent enumeration yields non-singleton optimal-cover polytopes. No re-formalization of this known result.

341437: newly read primary definitions and Proposition1.5 proof plus Conjecture1.6. The source F maximizes the MINIMUM color-class size in total colorings, rather than the largest class as normalized. A monochromatic near-total class cannot refute the source conjecture. The source proof handles s1, an already known subcase. General s would require a rainbow fork plus k incomparable sets while preserving all color classes; no proof claimed. Statement-only correction excluded, source problem parked.
