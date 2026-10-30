# r36: full leaf-slide diameter unresolved; credit 0

## Screen before selection

Read repository/campaign AGENTS, NEXT, ledger and prior-campaign-context; reconciled r34/r35 summaries and recent root cascade, mean, denominator and Gaunt handbacks. Current accepted tally is five additional / 35 total. Old handbacks contain superseded counts. No acceptance authority is exercised.

* AIM568 is exactly Oswald's 2/pi question already investigated in r33: excluded without reinvestment.
* AIM617 asks for a single polynomial p(d,q) bounding both convex CPWL parts of every q-cell CPWL function. Its actual problem body cites published Problem9.1; no concrete finite obstruction or all-order construction emerged. Not selected, and no claim to have read its underlying journal proof.
* AIM509: for ALL n,m>=6, is the realization of the matching complex of the categorical product P_n x P_m a finite wedge of spheres? Read actual 2403.15298v2 Conjecture6.2 and Theorem1.3, plus the outline of the thirteen auxiliary graph families for width5. Betti numbers/torsion tests cannot decide homotopy equivalence; width<=5 is already proved. No uniform discrete-Morse matching mechanism found. Not selected.
* AIM611: for every fixed d>=3, do all n satisfy S(n,d)<=C_d n^(d²+d-1), for ordered distinct cospherical (d+2)-tuples? Read actual 2509.06935v1 discussion/Conjecture5.1 and adjacent theorem statements. Existence of a sphere-avoiding subset does not upper-bound all degeneracies. No uniform arithmetic count established. Not selected.
* Selected AIM503 / clopen OP-00880, because a precise quadratic answer and a published constructive upper-bound mechanism reduce the problem to a substantive lower bound; the proposed cut mechanism is falsifiable. This is different from plane noncrossing-tree edge flips (r34): leaf slides are more restrictive local moves, with no plane embedding or common-edge condition.

## Exact full target and source chronology

For each integer n>=6, states are all simple trees on the fixed labelled set [n]. A move picks a degree-one vertex v with neighbor w and a neighbor u!=v of w in the CURRENT tree; replace vw by vu. The desired equality is

    diam(G_n) = floor(n²/2)-n.

The lower-bound equivalent is: for every n>=6 there exist T,U such that EVERY legal leaf-slide sequence from T to U has at least floor(n²/2)-n steps. There is no geometric/analytic realization issue: these finite labelled graphs are the literal source objects, and vertex names in the checker are shifted from [n] to {0,...,n-1} by a bijection.

Actual published Kozlov2025 Open Question2.5 asks for a diameter formula, not this precise conjectured value. Its published HTML was obtained and the question and local-move definition read. Klatt–Papadopoulos–Raffelsiefen2607.07404v1 supplies the more recent upper bound (Theorem3.18), nearest-star characterization (Proposition3.14), extremal-potential Lemma3.16, and lower matching-distance bound (Lemma3.20/Corollary3.23). Those actual bodies/proofs were read. The exact equality is the AIM503 formulation based on their computations, not attributed as a verbatim conjecture to Kozlov.

Current arXiv landing page lists only v1, submitted 2026-07-08 13:38:19 UTC, and no journal reference was found on it. Thus v1 is the latest obtainable successor body here; this does not certify that no accepted version exists. Author-group members page confirms all three authors but is NOT a publication bibliography. Exact-title/author/followup public searches located the same preprint and an author conference abstract, no new diameter proof. Author followup coverage remains bounded; no claim to exhaustive author-site clearance.

## Public/classical checks before substantive investment

Live heads and hashes are in registry-screen.json/http.json. Omega dev advanced from cf6f598... to 50b390...; comparison reports79 commits/155 changed files, below the300-file cap. Updated inherited complete D5/Problems inventories by applying those reported changes. This is coverage of those scopes ONLY, never whole-dev completeness. AIM3541/OpenAI-preprints13578/Count183 inherited complete trees remain at unchanged heads. Targeted terms: realignment, leafslide, leaf-slide, Kozlov, Klatt, path-product, matching-complex, cospherical. Only the three AIM problem records matched these scoped path searches; no solution path matched. Filename negatives are not novelty clearance, and source-body comparisons remain decisive.

Closest classical mechanism found: Bogdanowicz2011, *Analyzing sets of phylogenetic trees using metrics*, DOI10.4064/am38-1-1, Definitions2.1/4.1 and Theorem2.2. Actual16-page publisher PDF obtained and relevant definition/proof bodies read. It defines minimum assignment of split tokens with the same quotient-Hamming cost used below. Its original trees have taxa at leaves; our states label every vertex and contain all edge splits, including singleton splits. These domain differences do not make the assignment mechanism new. Its triangle proof transfers immediately. No credit is requested for this helper or application.

Source2607.07404 matching distance instead maximizes sums of pairwise vertex-distance changes over a matching on labels; it is NOT minimum matching of edge splits. Its exact diameter is only ~3n²/8, as the source proves, so it cannot certify the proposed ~n²/2 diameter. Ordinary edge-exchange and unrestricted leaf-exchange graph theorems permit moves illegal here; they do not furnish missing leaf-slide lower bounds.

## Result of this lane

No full proof, counterexample or nominated candidate. FAILED-ROUTES.md proves an all-order obstruction to the split-transport approach and records exact finite witnesses. This is not a source resolution or independent discovery. No PROOF.md, Lean helper, large formalization, paper or packet is supplied.

Strongest falsifier of a claimed solution: any proposed lower-bound potential must change by at most one on EVERY current-tree leaf slide, including a slide of a distinguished/root vertex; fixed-root transmission does not have that property (source Remark3.7). For transport the Lipschitz property is valid, but the available magnitude is provably too small. A recurrence lifting a diametral pair from n to n+2 would need an all-sequence lower bound, not just an exhibited long sequence; none is proved.

## Lean feasibility and remaining bridge

A literal eventual endpoint would quantify `n : Nat`, `6 <= n`, two `SimpleGraph (Fin n)` trees, and every finite list of trees whose consecutive pairs satisfy the explicit leaf/neighbor/replacement relation; it would assert a lower bound `n*n/2-n` on its step count, together with an all-pairs upper bound. Finite complete-graph state spaces are encodable; BFS certificates for n=6,7 would certify only old finite instances. There is no identified all-n invariant to encode, so no honest complete Lean endpoint is currently feasible. Root independent mathematical/source/eligibility review must precede any large formalization. If authorized later, use only the requested Lean4.34.1/mathlib d13f23... pin and strict serial resource/axiom protocol; no Lean was run here.

## Reproduction and access limits

`bash run-checks.sh` uses standard Python only, exact integer bitsets, BFS and subset assignment DP. AS512MiB, CPU40s, wall55s, BLAS/OMP1. Complete state reachability is checked against Cayley n^(n-2), not assumed from a sampled census. It traverses125/1296/16807 states for n5/6/7 from one path each and all labelled path targets modulo reversal. It does not enumerate all start pairs or claim a new diameter computation. Already-public n6/7 values are only sanity checks.

Public HTTP only; no children, git, shared/other-lane edits, external messages/uploads/accounts or browser tabs. Initial mistyped clopenquestions.com DNS failure and obsolete Count /commits/main404 are recorded candidly; corrected known canonical URLs were used, not access-control bypass. No403/429/challenge retry occurred. The failed bs4 import was replaced with standard-library HTML handling. HTTP dates/status/URLs/SHA256 are in http.json; local input hashes and final artifact hashes are separately recorded.
