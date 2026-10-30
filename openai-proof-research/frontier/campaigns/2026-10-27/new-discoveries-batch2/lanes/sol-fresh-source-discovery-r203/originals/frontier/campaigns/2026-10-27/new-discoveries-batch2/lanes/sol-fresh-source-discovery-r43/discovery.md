# r43: diminished Sombor source screen — no qualifying full result

## Exact source and scope

F. Movahedi, *Diminished Sombor matrix, spectral radius, and energy of the graphs*, arXiv:2508.06531v1, p2 definitions and p19 Conjecture5.1. For every finite simple graph G, let d_i be its actual unweighted degree and let M_ij=sqrt(d_i²+d_j²)/(d_i+d_j) on edges, zero otherwise. Its energy is the sum of absolute values of all real eigenvalues with multiplicity. Conjecture5.1 says there is no graph whose energy is an integer. Actual PDF pp2,4–5,19 and current arXiv metadata read; only v1 appears. No journal reference or published counterpart located in this bounded screen; no published-version clearance.

Literal conjecture already publicly refuted by the singleton edgeless graph: zero matrix, zero energy. Actual public Problems body AND Lean definitions/result read at current Omega head50c9feeeb63c4ee7af0936663ef4272aea0780e2. The external code was not compiled. Path history reports commit2c49fc3c9a393894e443f5453368210102672f67 dated2026-10-05T15:11:03Z, well before this lane. This is both a known result and an omitted-hypothesis correction, hence ineligible. It is not presented as a substantive discovery.

The meaningful surviving question is: for EVERY finite simple graph with at least one edge, is this literal energy nonintegral? This lane DOES NOT resolve that all-graph statement and does not nominate a modified-domain statement for credit. A partial family is not enough.

## Primary-statement screen (two candidates; below four)

1. Rabizadeh–Habibi–Gutman, MATCH93(2025)853–859, Conjecture1 pp857–858: m times the absolute least Sombor eigenvalue is at least SO(G), with specified complete-component equality. Excluded immediately: Das–Xu, MATCH94(2025)855–862, Theorem1 pp858–860 proves the full inequality and equality characterization. Actual published bodies read. Strongest concrete bridge is the maximum edge weight's 2x2 principal submatrix, interlacing, then equality forces adjacency least eigenvalue -1; induced P3 excludes every noncomplete connected component. No new result.
2. Movahedi Conjecture5.1 above: literal version publicly refuted. Nonempty version examined only for a viable full route; stopped when the bridge remained partial.

The 2610.12237 search hit was reconnaissance, not a selected source question: its abstract/introduction already announces proofs, and no conjecture from it was adopted. Other search results were not candidates. Prior r1–42 summary context and ledger exclusions read before investment; r12's finite-ring MSN target is a different matrix and question. Neither active polyomino nor reflected Steiner work was pursued.

## Concrete classical bridges (uncredited)

### Regular graphs: exact conjugation argument

For every finite k-regular graph with integer k>0, source Theorem3.1 gives M=A/sqrt(2). Suppose its energy is a positive integer m. Let S be the sum of the strictly positive adjacency eigenvalues, counted with multiplicity. Trace A=0 implies E(A)=2S=m sqrt(2). All eigenvalues are real algebraic numbers, lying in the finite Galois splitting field K of A's rational characteristic polynomial. Thus sqrt(2)=2S/m belongs to K, and the nonidentity automorphism of Q(sqrt(2))/Q extends to an automorphism sigma of K. Therefore sigma(S)=-S.

But sigma permutes the multiset of all adjacency eigenvalues, so sigma(S) is a sum of a selected submultiset. The sum of ALL negative eigenvalues is -S, and every selected submultiset has sum at least -S, with strict inequality if it contains a positive value. The selected set contains k: A has eigenvalue k from the constant vector, k was among the positive summands of S, and sigma fixes k. Hence sigma(S)>-S, contradiction. This uses only elementary splitting-field automorphism extension, the real symmetric spectral theorem, trace zero, and the source's actual scaling theorem. Positivity of energy follows from the nonzero matrix. It covers disconnected k-regular graphs too. No partial-family credit.

### Complete bipartite graphs: direct Fermat bridge

Source Theorem3.4 gives E(K_p,q)=2 sqrt(pq(p²+q²))/(p+q) for all positive integers p,q. If rational, pq(p²+q²) must be an integer square. Divide out g=gcd(p,q): the remaining a,b are coprime and ab(a²+b²) is a square. The three factors a,b,a²+b² are pairwise coprime, so each is a square. Write a=u²,b=v²,a²+b²=w². Then u⁴+v⁴=w² with all three positive integers, contradicting Fermat's classical theorem. Actual Wayne Aitken, *Fermat's Proof* (September26,2010), Theorem5 and complete descent proof pp5–6 read. Thus all complete bipartite energies are irrational. This is a routine source-formula/classical-theorem corollary, not a candidate theorem. Merely extending these partial families would earn zero.

## Exact failed universal shortcut

A generic nonnegative symmetric matrix with zero diagonal, bipartite support and every nonzero weight in [1/sqrt(2),1) need not have nonintegral energy. Put t=1/sqrt(2),

B=[[t,t],[t,3/2-t]], M=[[0,B],[B,0]].

B has positive trace3/2 and determinant3t/2-1>0 (t>2/3), so both eigenvalues are positive. The orthogonal block change of basis gives diag(B,-B), hence E(M)=2 trace(B)=3 exactly. All three weights are in the required interval: t<3/4 and t>1/2. This is NOT a source counterexample: the support is K2,2, whose actual degrees are all2, so every literal source weight would have to equal t. The exceptional entry3/2-t does not. Degree consistency is indispensable.

Likewise B=[[2,1],[1,3]] has irrational eigenvalues (5±sqrt(5))/2, both positive, while the associated zero-diagonal block matrix has energy10. Irrational individual eigenvalues do not establish irrational energy.

## Checks and remaining gap

`bash run.sh python3 check.py` passes exact symbolic block diagonalization, positivity/weight-bound rational certificates, the literal degree inconsistency, a rational-matrix shortcut falsifier, and400 complete-bipartite parameter checks (1<=p,q<=20). These checks diagnose routes and corroborate formulas, not the all-graph theorem. No broad graph census was run; no all-order inference from finite tests. No checker failure occurred. Early exploratory thoughts about reducing general graphs to biregular graphs produced no necessity theorem and were abandoned before computation.

The missing step is a uniform mechanism controlling the spectral positive-part sum for arbitrary nonregular graphs with multiple degree classes, or a genuine literal nonempty-graph counterexample. Generic trace, symmetry and weight interval arguments lose the degree dependence. Strongest falsifier for further work: construct an actual graph with integral energy, with an exact characteristic/spectral certificate. Strongest eligibility objection: the literal statement is already publicly refuted and repairing its domain is uncredited; any future nomination needs a substantive surviving question and full scope, rather than these routine families.

## Current public registry coverage

At14:07:58–14:10:26UTC on2026-10-29: Omega dev50c9feeeb63c4ee7af0936663ef4272aea0780e2 (commit13:59:32Z); complete untruncated D5 tree12550 entries and Problems1551. Omega main d7af67136d4478875778ac6e75eb5fbb8b3693a5 complete69 entries. OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a complete preprints subtree13578; AIM8729eab98bafe409b66c5e39253bf56569a62327 complete tree3541; Countdbf673741a54c7dc9d88a6aec0e8148a538f4a3a complete183. Target-name paths searched in those complete scopes. Actual matching diminished-Sombor proof body read, rather than path-based inference. Other Sombor-family paths refer to different matrices and were not treated as proof of the nonempty question. No complete whole-dev tree or semantic no-prior-proof clearance is claimed. No novelty PASS. Web searches are bounded and not a citation-index survey.

All downloaded source bytes and receipts are in sources/ and http.jsonl. No denial/429/challenge was encountered. Search-tool responses are not origin-byte archives; their exact per-call retrieval timestamps were not exposed, so none are invented. No source contact, posting, account changes, browser tabs, git, children, shared files or other lanes written. No PROOF.md: no full eligible candidate. No Lean started. Root alone adjudicates counts; credit0,5additional/35total unchanged.
