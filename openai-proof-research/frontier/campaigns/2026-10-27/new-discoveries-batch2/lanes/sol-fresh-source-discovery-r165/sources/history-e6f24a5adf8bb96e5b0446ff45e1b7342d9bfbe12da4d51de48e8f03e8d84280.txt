# r101 — two fresh lower general position claims; unresolved

Credit 0. Counts remain 8 additional / 38 total. No PROOF.md: no full ordinary result. No Lean or paper. This lane is distinct from arithmetic r100, Chatterjee review, parked MMPP, super-domination r99 and the excluded affine forcing-density family.

## Exact attributed claims and source boundaries

Eartha Kruft Welton, Sharif Khudairi and James Tuite, *Lower General Position in Cartesian Products*, arXiv:2404.19451v1 (30 April 2024), actual downloaded current PDF, manuscript pp7–9:

1. Conjecture 2.10: for any graphs G,H, gp^-(G square H) >= min(gp^-(G),gp^-(H)). Here gp^- is the **smallest inclusion-maximal** general position set, not the largest general position set. General position means no three distinct selected vertices lie on one shortest path.
2. Conjecture 3.3: every graph has a terminal set. Definition 2.2 requires a general position set S such that for every u outside S there are distinct a,b in S with d(u,b)=d(u,a)+d(a,b), or with a,b interchanged. This endpoint requirement is essential; ordinary maximality alone does not suffice. It also implies maximality.

The manuscript uses simple undirected graphs; the substantive investigation here is finite, connected, nontrivial factors, as in its cited product theorem. No disconnected-distance convention or empty-graph wording correction is claimed. Proving that restricted core would still require checking the literal all-graphs extension before any full result claim.

The primary abs history and downloaded PDF identify v1. Later/current survey: Ullas Chandran S.V., Sandi Klavžar and James Tuite, arXiv:2501.19385v5, 16 August 2026 (body date August18), actual pp47–48, Conjectures 5.13 and 5.14 repeat these claims. Earlier v2 is also preserved, but is superseded for freshness. The survey explicitly retains the diameter<=3, chordal and cograph terminal-set results; none is a new target here. Journal DOI 10.22049/CCO.2024.29171.1879 is identified externally, but the Open University journal PDF returned HTTP403; no bypass or retry. Journal wording remains unverified. MathDB's terminal description omits the endpoint requirement; it is not used as the mathematical source.

A third screened claim is Klavžar et al.'s strong geodetic prism Conjecture3.4 (RAIRO2018 actual source). It is already refuted by Gledel–Iršič–Klavžar, arXiv:1803.11423, actual successor Section7/Theorem7.1 proof, pp15–16: sg(G_{k,n})=binom(k,2)(n-1)+k and sg(G_{k,n} square K_n)<=kn+1. At k4,n2 these give 10>9. Its explicit geodesics and lower-bound argument were read. EXCLUDED, no investment or credit.

## Early all-date and current public screening

`duplicate-audit.json` hashes all 5960 selected report/ledger files across every local campaign date (including SUMMARY, discovery, FINDINGS, PROOF, review and ledger name matches). 43 broad keyword hits were unrelated terminal sets in Steiner/optimization work. No exact lower-gp or graph-terminal claim was found there. This is a bounded lexical screen, not semantic absence proof. Context and accepted/held/excluded family descriptions were read through `context.py`; the task's explicit exclusions were honored.

Fresh default HEAD reads at ~19:47 UTC: Omega556e7696bbabaff203d45456d177c5ce5b714212; OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. Compared Omega9aef67a59dec08d1ff04a18a3d23560525ab023d to this head: 2 commits, 1 file, whose actual current body is saved. The older complete18:13 baseline and r99 chains are inherited, not independently semantically cleared. Their fresh family-term scan found graph-general-position neighbors. Current pinned actual Blueprint and Lean bodies were obtained separately: CylinderSevenTen is a mobile-general-position cylinder result; RatherRealRootedComplete classifies real-rootedness of a polynomial; TianDokyeesunKlavzarOuterGeneralPositionRefutation refutes an outer-position vertex-deletion bound. Their actual statement scopes differ from both claims here. Blueprint and Lean are not conflated; no replay or audit of upstream truth was attempted. No global current-prior PASS.

Closest classical body: Di Stefano–Klavžar–Krishnakumar–Tuite–Yero, arXiv:2306.09965v2, actual Proposition2.1 proof and Theorem2.2 (quoting Rodríguez-Velázquez2022 Theorem4.1). A product has gp^-=2 iff a factor has an adjacent universal pair, or both factors have geodetic number2. In either case at least one factor has gp^-=2. Thus a counterexample to Conjecture2.10 in the nontrivial connected core must have product lower number >=3 and both factor lower numbers greater than that. This is known-body reduction only, uncredited. Rodríguez-Velázquez's original2022 proof body has not been obtained independently, so there is an explicit closest-original-body gap.

Fresh public searches used exact titles, terminal-set/general-position terms and Conjecture2.10; current survey retained both, with no full successor located in this bounded search. This is not proof that no public resolution exists. URLs, access times and byte hashes are in http.json/sourcebytes.sha256.

## Sustained full-scope route: synchronized forbidden rectangles

Let S={(g_i,h_i):1<=i<=k} be general position in G square H. For a metric factor X define

I_X(a,b)={x:d(a,x)+d(x,b)=d(a,b)},
E_X(a,b)={x:d(x,a)+d(a,b)=d(x,b)}.

For each pair i<j form the three rectangles

I_G(g_i,g_j) x I_H(h_i,h_j),
E_G(g_i,g_j) x E_H(h_i,h_j),
E_G(g_j,g_i) x E_H(h_j,h_i).

Then S is maximal iff these rectangles cover the whole product (k>=2).

Proof of reduction: distances in a Cartesian product add. Each triangle defect in either coordinate is nonnegative, so a sum of two defects vanishes iff both vanish. A new z therefore lies between i,j iff it lies in the first rectangle; i lies between z,j iff z lies in the second, and j lies between z,i iff z lies in the third. S is GP, so adding z can fail only by a triple involving z and two members of S. Every existing member is also covered, since it occurs as an endpoint of an interval rectangle. Thus coverage is precisely maximality. The argument also handles equal coordinates using I(a,a)={a}, E(a,a)=V(X). No strict-distance assumption was smuggled in.

The intended full proof would show that this synchronized rectangle cover forces one factor to possess a maximal GP set of size <=k. The naive construction takes the coordinate projections and extends them to maximal GP sets, but is invalid: in P3 square P3 the set {(0,2),(1,0),(2,1)} is GP (pair distances3,3,2), while both projections {0,1,2} are not GP. This is an actual metric obstruction, not a relaxation outside graph metrics. Consequently a factor completion argument cannot even begin with those projections. A successful compression must select or replace projected points while preserving the synchronized cover, and control cardinality. No such operation is proved here.

The strongest precise missing lemma is: for every finite connected G,H and product GP set S whose three-rectangle unions cover V(G)xV(H), there exists an inclusion-maximal GP set in G or H with cardinality <=|S|. Its hypotheses retain the metric dependencies and synchronized orientations. Dropping them makes mere independent marginal covering irrelevant. This lemma would settle the entire connected finite source core, not merely the small cases searched. It remains unproved.

## Terminal existence route and exact failures

The source constructs pairwise distance-constant cliques. At diameter3 all inter-clique distances are2 or3, so no three blocks can satisfy an additive equality: 2+2>3. Its refinement guarantees outside vertices have endpoint witnesses. Extending the algorithm to arbitrary diameter must ensure **both** this strict inter-block triangle condition and all endpoint certificates. Constancy alone is insufficient: singleton blocks {0},{2},{4} in C8 have distances2,2,4 and violate GP. This defeats that extension, not Conjecture3.3.

A separate extremal idea chooses a maximum GP set and adjusts it by a secondary potential. K1,3 blocks that entire maximum-cardinality strategy: the unique maximum GP set is its three leaves, while the center has equal distance1 to every leaf and hence no endpoint witness. Yet {center,leaf} is terminal. Thus terminal existence requires allowing cardinality decreases; maximizing GP cardinality cannot supply the theorem. An early diagnostic guess using C6 was rejected by the checker (maximum triples there can be terminal), corrected to this exact star witness before finalization; no C6 obstruction is asserted.

The remaining full-scope terminal gap is a terminating replacement rule that preserves GP and eventually supplies endpoint witnesses for every outside vertex, including those that lose their former certificate when selected vertices are removed. Neither a well-founded potential nor witness-preserving replacement invariant has been established. Source Lemma3.4 already supplies connected/twin-free/no-simplicial/no-clique-separator reductions; repeating those is not credit.

## Capped checks, falsifiers and disposition

`check.py` runs with the supplied improved guard, unchanged 512MiB AS/groupRSS, 210s CPU, 230s wall, nominal40ms sampling and BLAS1. It verifies 324 coordinate rectangle identities in P3 square P3, the exact projection obstruction, C8 inter-block failure, and all subsets of K1,3 for the extremal failure. Sixteen fixed-seed factor graphs of orders7–10 have their exact gp^- certified by exhaustive subset search; all16 cyclic-offset products were exhaustively tested for maximal GP pairs/triples. None found. This is **not** full lower-number computation on the products, nor a proof at higher cardinalities. Some random factors are complete and already covered by source results; no novelty is claimed for them. check-results.json stores every edge list and exact factor witness.

Strongest falsifier of the product claim: a connected pair with certified factor lower numbers >k and one explicit maximal GP k-set whose forbidden rectangles cover the product. The checker supplies the exact finite criterion; none is found. Strongest falsifier of terminal existence: one graph with all GP subsets checked and no terminal subset. None is found. Route failures above are not either falsifier.

Disposition: UNRESOLVED, no full theorem, no counterexample, no discovery nomination. Journal and original universal-line proof-body gaps, older registry-chain semantic limits and general literature limits remain explicit. No helper, known corollary, parameter case, terminal-definition correction, or numerical observation earns credit.
