# ACTUALBRIEF: expanded-corpus-r537

Author: Claude Opus 5.5, high effort, working personally with no subagents, no model fallback, no Lean and no mathematical programs. No self-credit; root alone adjudicates.

## Outcome

One author-complete proof, not independently reviewed and not claimed as qualified. Nothing else reached a full-scope endpoint.

- **362080** (treewidth of token graphs of trees): full literal proved at author level, FULLCANDIDATE.md. Upper bound (2k-1)n^(k-1) by centroid recursion; lower bound n^(k-1)/(32 k^(2k+3) 2^k) for n>=8k^2 by vertex congestion of canonical hand-off routes. Serious objection: short standard tools, and the argument gives a general inequality for all graphs with trees as the case where the bounds meet (the 336276 pattern). I recommend independent adversarial qualification and make no significance claim.
- **358572**: complete reduction to one crisp degree lemma, unproved.
- **325670**: three soft mechanisms tried; exact missing stability lemma stated.
- **360497, 353126, 318163**: settled in print; zero. Each is backed by an actual body read (see gates); the proofs are not audited.
- **331880**: public except finitely many pairs with 6<=m<=8; remainder looks like constant tracking.
- Remaining targets parked; ten IDs had no source body read, and those parks are not open-status certifications.

## Generic-proof self-tests on 362080

Spectral route (source Theorem 7 with Aldous) fails: order n^(k-2) on paths. Source Lemma 9 fails on spiders, at most about n^((k-1)/2). The star bramble does not generalize to paths. No reduction to a published theorem found. The remaining objection is the generic-law one above, in FULLCANDIDATE.md Section 6.

## Lean feasibility

362080: elementary, no analysis; needs lane-defined tree decomposition and treewidth, token graph, centroid, disjoint-union gluing, multi-factor Cartesian isomorphism, balanced separator, route and load counting. Author estimate 1500 to 2500 lines, not compiled. DORMANT-SOL-FORMAL-PLAN.md. No dispatch.
358572: would need only finite order and counting, but the core lemma is unproved. 325670: infinite graph limits and an unproved stability input; expensive.

## Provenance and access

- Literals: corpus-bindings.json; 20 of 20 bound, with the trailing newline in `raw_line_with_newline_sha256` and the no-newline hash recorded separately under its own key.
- TASK and denials read completely in contiguous chunks of at most 15000 characters: read-ranges.json.
- History: 946 allowlisted files read and hash-checked, 0 skipped by the protected filter; exact matches are neighbours 362081, 362082, 337404 and one false byte-count hit on 320844 (history-matches.json). No disposition on any reserved ID.
- GET: 9 charged hops, 9 PDF successes, 0 unavailable, 0 redirects, no new denials: access-inventory.json.
- Search: 3 calls, 3 query strings of the 9 allowed, all precharged, responses in searches/. Excerpts are navigation only.
- Registry roots were not requested because they are inherited-denied, so no current registry check was possible.
- Bodies read in part: 2402.17962, 2112.14960, 2305.17933, 1511.07306, 2402.10782, 2303.15194, 1012.2878, 2310.17469, 1305.6945. No figures inspected. Text extraction with pdftotext.

## Disclosed deviations

1. My first runner invocation executed run.py directly and failed with exit 126 because it has no execute bit. It never started, so no receipt exists. I switched to `python3 -I -B` with a new label.
2. **Search 3 retention:** after search 3 returned, my turn ended with no tool call and the response unsaved. On resumption the save was the very next tool call, verbatim from the stored response, with no re-search and no intervening tool call. This is a delay in saving, not a lost response.
3. The oversized bootstrap display was persisted by the harness outside the lane; I did not open that file. The ancestor AGENTS.md files were read in full through the runner (read_agents_a).
4. Saves of search responses and the two handoff documents ran write_lane.py directly under `timeout 140`, as the brief permits, rather than under run.py; those writes have no runner receipt.
5. The bootstrap AGENTS display was not read at the time of bootstrap; it was recovered as in item 3 before the candidate was written.

## Twenty ID-keyed gates

### 362080: Treewidth order conjecture for token graphs of trees
- outcome: AUTHOR_COMPLETE_CANDIDATE_NOT_QUALIFIED
- literal_gate: PASS_LITERAL_READ; source Conj 20 has 2<=k<=n-2, corpus 1<=k<=n-1, equivalent for fixed k
- source_gate: READ: 2402.17962v3 statement, Sections 1, 2, 5, Theorems through Section 4
- ordinary_gate: AUTHOR_COMPLETE: FULLCANDIDATE.md; not independently reviewed
- prior_gate: Bounded: 2 searches, no proof found; registries unavailable; no citing-work coverage; no journal final read
- novelty_gate: NOT_CLEARED: bounded search only
- significance_gate: UNADJUDICATED: serious generic-law objection recorded in FULLCANDIDATE.md Section 6
- formal_gate: DORMANT plan only; no Lean run
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: Whole literal proved at author level with explicit constants; recommended for independent adversarial qualification.

### 358572: Subquadratic ordered Ramsey bound for matchings of interval chromatic number two
- outcome: PARK_WITH_PRECISE_GAP
- literal_gate: PASS_LITERAL_READ
- source_gate: READ: 2305.17933v1 Sections 1-3
- ordinary_gate: PARK; complete reduction proved, core lemma unpaid
- prior_gate: Search 3 (excerpts only) reports the worst case still open; not a certification
- novelty_gate: NOT_APPLICABLE: no candidate
- significance_gate: NOT_APPLICABLE: no candidate
- formal_gate: NOT_APPLICABLE: no candidate
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: Proved reduction: the triangle-free colour H has max degree below n, since a neighbourhood is a clique in the other colour. Splitting into blocks of size s, only complete block pairs obstruct, giving a bipartite graph D on [L]x[L] of degree at most 2m/s. Exact unpaid lemma: there are c,C>0 such that for every permutation pi of [m] and every bipartite D on [Cm]x[Cm] of maximum degree at most m^c there are increasing p,q:[m]->[Cm] with (p(i),q(pi(i))) not in D. This would give r=O(n^(2-c)). Tried: independent windows fail on pi-aligned complete cells; a bi-hole handles only degree O(1); first moment handles only unstructured D; repair by shifting blocks is uncontrolled for blow-ups of expanders.

### 325670: Strict inequality for infinite Turán numbers of bipartite graphs
- outcome: PARK_WITH_PRECISE_GAP
- literal_gate: PASS_LITERAL_READ; degenerate reading with alpha above the true exponent and c_F=0 makes the corpus wording false, but source defines exponent with positive constants, so this is a wording point worth zero
- source_gate: READ: 1305.6945v1 intro, definition, Conj 1.4 (K_{2,t+1}, K_{2,2} are the proved cases)
- ordinary_gate: PARK; three mechanisms tried
- prior_gate: No proof found; no search spent
- novelty_gate: NOT_APPLICABLE: no candidate
- significance_gate: NOT_APPLICABLE: no candidate
- formal_gate: NOT_APPLICABLE: no candidate
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: Soft routes fail. Deletion gives only a LOWER bound: edges meeting any small set L of density b are at least about c*alpha*b*n^alpha, i.e. a degree floor at alpha/2 of the mean, with no ceiling. The prefix-homogeneous profile W(x,y)=A*max(x,y)^(alpha-2) is first-order consistent with all prefixes being near-extremal (D_x(x)=c*alpha*x^(alpha-1), D_x decreasing), so no contradiction arises without a stability input. Exact unpaid lemma: near-extremal F-free graphs have maximum degree (1+o(1)) times mean degree on most vertices, for general bipartite F. Known only for special F such as K_{2,t}.

### 357871: The online Ramsey number conjecture for cycles of fixed odd length
- outcome: PARK_WITH_PRECISE_GAP
- literal_gate: PASS_LITERAL_READ
- source_gate: READ: 2303.15194v1 intro bounds and Conj 32: 2.6n-3 < r <= 3n+log2 n+50k for odd k
- ordinary_gate: PARK
- prior_gate: Open as of source; no search
- novelty_gate: NOT_APPLICABLE: no candidate
- significance_gate: NOT_APPLICABLE: no candidate
- formal_gate: NOT_APPLICABLE: no candidate
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: Upper bound is in the source. Unpaid: a Painter strategy forcing 3n-o(n) rounds for every fixed odd k.

### 361895: Approximation conjecture for the ordered clique number of tournaments
- outcome: PARK_WITH_PRECISE_GAP
- literal_gate: PASS_LITERAL_READ
- source_gate: READ: 2402.10782v4 intro and Section 4, Conj 4.2: k=3 known via cited Aboulker et al
- ordinary_gate: PARK
- prior_gate: Open as of source; no search
- novelty_gate: NOT_APPLICABLE: no candidate
- significance_gate: NOT_APPLICABLE: no candidate
- formal_gate: NOT_APPLICABLE: no candidate
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: Natural pivot-recursion orderings have unbounded backward-clique accumulation over recursion depth. Generalizing the cited k=3 algorithm is unpaid, and that algorithm was not read.

### 331880: Zhang–Broersma–Chen conjecture on Ramsey numbers of trees versus fans
- outcome: PARK_FINITE_REMAINDER
- literal_gate: PASS_LITERAL_READ
- source_gate: READ: 1511.07306v2 abstract, intro Theorems 2-4, final remarks: proved for m>=9 and for n>=3m^2-2m-1; only 6<=m<=8 with n<min(8m,3m^2-2m-1) remain
- ordinary_gate: PARK
- prior_gate: Most of the range is public in the source; remainder not searched
- novelty_gate: NOT_APPLICABLE: no candidate
- significance_gate: Remainder would be constant tracking in the source embedding method; the source itself says m=8 likely follows by careful analysis, so routine-adaptation exclusion is likely
- formal_gate: NOT_APPLICABLE: no candidate
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: Unpaid: exact R(T_n,F_m)=2n-1 for 6<=m<=8 and n in [m^2-m+1, min(8m,3m^2-2m-1)). Heuristic check that stars are the worst case is not a proof.

### 353126: Zhang–Sun–Wu and Gholami–Rowshan conjecture on bipartite Ramsey numbers of even cycles
- outcome: EXCLUDE_SOURCE_OWN_PUBLIC
- literal_gate: PASS_LITERAL_READ; literal says all positive integers, but source Theorem 1.1 gives br(C4,C4)=5 and br(C6,C4)=5 against the formula values 4 and 4, and C_2 is undefined at m=1
- source_gate: READ: 2112.14960v2 abstract, Theorem 1.1, Conj 1.2, Theorem 1.3 (all n,m>=5)
- ordinary_gate: No new mathematics
- prior_gate: Public: source Theorem 1.3 plus cited small cases
- novelty_gate: ZERO
- significance_gate: ZERO: small-parameter failure is a correction
- formal_gate: NOT_APPLICABLE: no candidate
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: Intended conjecture settled in its own source. Theorem 1.3 proof not audited.

### 360497: Haythorpe's lower-bound conjecture for Hamiltonian cycles in regular graphs
- outcome: EXCLUDE_SOURCE_OWN_PUBLIC
- literal_gate: PASS_LITERAL_READ
- source_gate: READ: 2310.17469v1 abstract and intro: disproved earlier by Zamfirescu (r in 5,6,7) and Goedgebeur et al (all r>=5), and asymptotically false by this source
- ordinary_gate: No new mathematics
- prior_gate: Public refutation in the source itself; earlier refutations cited there were not read
- novelty_gate: ZERO
- significance_gate: ZERO
- formal_gate: NOT_APPLICABLE: no candidate
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: Literal records the source disproof. Zero credit.

### 318163: Lovász–Plummer exponential perfect-matching conjecture for cubic bridgeless graphs
- outcome: EXCLUDE_PUBLIC
- literal_gate: PASS_LITERAL_READ
- source_gate: READ: 1012.2878v2 Theorem 1 (2^(|V|/3656), multiple edges allowed). Literal source 0901.3894 itself not read
- ordinary_gate: No new mathematics
- prior_gate: Exact public theorem
- novelty_gate: ZERO
- significance_gate: ZERO
- formal_gate: NOT_APPLICABLE: no candidate
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: Esperet, Kardos, King, Kral, Norine prove the literal; proof not audited.

### 320844: Lovász–Plummer conjecture for regular matching-covered graphs
- outcome: PARK_FAMOUS
- literal_gate: PASS_LITERAL_READ
- source_gate: READ: 1012.2878v2 Section 6.2 Conj 24 and Theorem 25 (weaker, needs (k-1)-edge-connectivity)
- ordinary_gate: PARK
- prior_gate: Open as of source; no search
- novelty_gate: NOT_APPLICABLE: no candidate
- significance_gate: NOT_APPLICABLE: no candidate
- formal_gate: NOT_APPLICABLE: no candidate
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: One-line park per brief. Exponential growth with base tending to infinity for merely matching-covered regular graphs is beyond the cubic proof, as the source says.

### 327681: The asymptotic and exact online Ramsey conjecture for paths
- outcome: PARK_LITERAL_ONLY
- literal_gate: PASS_LITERAL_READ
- source_gate: source body not read in this lane
- ordinary_gate: PARK; no mechanism
- prior_gate: Author recalls a later asymptotic off-diagonal paper (Mond-Portier) from memory: NOT read, NOT verified, not used
- novelty_gate: NOT_APPLICABLE: no candidate
- significance_gate: NOT_APPLICABLE: no candidate
- formal_gate: NOT_APPLICABLE: no candidate
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: The exact all-l>=k>=4 formula needs both a matching Builder and Painter strategy; diagonal case is open and no small refutation is available without computation, which is barred here.

### 318483: Variance-growth conjecture for interval-graph estimators
- outcome: PARK_LITERAL_ONLY
- literal_gate: PASS_LITERAL_READ; literal itself says precise asymptotic meaning is open
- source_gate: source body not read in this lane
- ordinary_gate: PARK; no mechanism
- prior_gate: unknown; no search
- novelty_gate: NOT_APPLICABLE: no candidate
- significance_gate: NOT_APPLICABLE: no candidate
- formal_gate: NOT_APPLICABLE: no candidate
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: Nonlinear covariance-driven dynamics on coefficient vectors; the Gaussian profile that the claim rests on is itself conjectural.

### 337405: The uniform Erdős–Pósa conjecture for wheel models
- outcome: PARK_LITERAL_ONLY
- literal_gate: PASS_LITERAL_READ
- source_gate: source body not read in this lane
- ordinary_gate: PARK; no mechanism
- prior_gate: unknown; no search
- novelty_gate: NOT_APPLICABLE: no candidate
- significance_gate: NOT_APPLICABLE: no candidate
- formal_gate: NOT_APPLICABLE: no candidate
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: Requires the k log k coefficient uniform over all wheel sizes t; source technique has t-dependent coefficient.

### 325183: Positive correlation of paths in the annealed random graph model for all parameters
- outcome: PARK_LITERAL_ONLY
- literal_gate: PASS_LITERAL_READ; corpus status field says solved, while statement says uniform case open: unresolved label inconsistency
- source_gate: source body not read in this lane
- ordinary_gate: PARK; no mechanism
- prior_gate: unknown; no search
- novelty_gate: NOT_APPLICABLE: no candidate
- significance_gate: NOT_APPLICABLE: no candidate
- formal_gate: NOT_APPLICABLE: no candidate
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: Each pair has an exclusive orientation so Harris does not apply; uniform in all n and p, including near-threshold p.

### 323839: Faudree–Schelp conjecture for three-color Ramsey numbers of paths
- outcome: PARK_LITERAL_ONLY
- literal_gate: PASS_LITERAL_READ
- source_gate: source body not read in this lane
- ordinary_gate: PARK
- prior_gate: Literal says large n is known
- novelty_gate: NOT_APPLICABLE: no candidate
- significance_gate: NOT_APPLICABLE: no candidate
- formal_gate: NOT_APPLICABLE: no candidate
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: All-n exact formula has no effective large-n threshold; intermediate n would need computation.

### 381562: Hofmeister–Joret–Wood conjecture on tree densities in minor-closed graph classes
- outcome: PARK_LITERAL_ONLY
- literal_gate: PASS_LITERAL_READ; corpus status field text refers to a different conjecture
- source_gate: source body not read in this lane
- ordinary_gate: PARK; small-case probes consistent
- prior_gate: unknown; no search
- novelty_gate: NOT_APPLICABLE: no candidate
- significance_gate: NOT_APPLICABLE: no candidate
- formal_gate: NOT_APPLICABLE: no candidate
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: General H requires a full structure theorem for K_{s,t}-minor-free graphs; later work may exist and was not searched.

### 369578: Mubayi–Zhao conjecture for forbidden traces of complete uniform hypergraphs
- outcome: PARK_LITERAL_ONLY
- literal_gate: PASS_LITERAL_READ
- source_gate: source body not read in this lane
- ordinary_gate: PARK; no mechanism
- prior_gate: unknown; no search
- novelty_gate: NOT_APPLICABLE: no candidate
- significance_gate: NOT_APPLICABLE: no candidate
- formal_gate: NOT_APPLICABLE: no candidate
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: Exact extremal hypergraph statement with no attempted stability mechanism.

### 358466: Gyárfás's conjecture on chi-boundedness of forest-free graphs
- outcome: PARK_FAMOUS
- literal_gate: PASS_LITERAL_READ
- source_gate: source body not read in this lane
- ordinary_gate: PARK
- prior_gate: Famous open problem
- novelty_gate: NOT_APPLICABLE: no candidate
- significance_gate: NOT_APPLICABLE: no candidate
- formal_gate: NOT_APPLICABLE: no candidate
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: One-line park: Gyarfas-Sumner.

### 331217: Erdős's minimal-growth conjecture for regular asymptotic bases
- outcome: PARK_FAMOUS
- literal_gate: PASS_LITERAL_READ
- source_gate: source body not read in this lane
- ordinary_gate: PARK
- prior_gate: Erdos-type open problem
- novelty_gate: NOT_APPLICABLE: no candidate
- significance_gate: NOT_APPLICABLE: no candidate
- formal_gate: NOT_APPLICABLE: no candidate
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: One-line park.

### 329112: The strengthened Erdős–Hajnal conjecture for tournaments
- outcome: PARK_FAMOUS
- literal_gate: PASS_LITERAL_READ
- source_gate: source body not read in this lane
- ordinary_gate: PARK
- prior_gate: Famous open problem
- novelty_gate: NOT_APPLICABLE: no candidate
- significance_gate: NOT_APPLICABLE: no candidate
- formal_gate: NOT_APPLICABLE: no candidate
- independent_gate: NOT_PAID: no independent review in this lane
- acceptance_gate: NOT_PAID: root alone adjudicates
- credit: 0
- exact_gap_or_note: One-line park: strengthened Erdos-Hajnal.

