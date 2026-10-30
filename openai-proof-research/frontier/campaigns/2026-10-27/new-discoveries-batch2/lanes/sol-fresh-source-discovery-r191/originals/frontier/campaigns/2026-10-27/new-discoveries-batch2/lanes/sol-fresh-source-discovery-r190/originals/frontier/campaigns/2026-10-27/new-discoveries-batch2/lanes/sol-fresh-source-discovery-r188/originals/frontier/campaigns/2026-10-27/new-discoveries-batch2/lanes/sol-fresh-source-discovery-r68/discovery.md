# r68 — Rather's full zero-divisor independence conjecture remains unresolved

Credit **0**. No nomination, ordinary full proof/refutation, PROOF.md, Lean work, or acceptance claim. Root alone decides acceptance. Campaign context read: seven additional accepted, 37 total.

## Context and three-question screen

Read ancestor and batch AGENTS.md, NEXT.md, ledger.json, prior-campaign-context.json, r64/r65 summaries and discovery reports, and root-polyomino57-acceptance-r1/ACCEPTANCE-PRIOR-LIMITS.json before target investment. Input hashes and accepted-family reconciliation are in context-screen.json. No old explored family was renamed fresh. r66 analysis and r67 arithmetic/algebra were not pursued. No excluded r64/r65 retry.

Three attributed source questions were screened, below the four-question limit:

1. **Lee–Seo, arXiv:2602.02450, Conjecture 1.3.** Read latest v2 (5 August 2026), not only February v1. This asks whether every finite simple G and every entrywise nonnegative symmetric matrix H with at most one positive eigenvalue satisfy hom(G,H) >= product_v hom(K_(d_v+1),H)^(1/(d_v+1)). EXCLUDE: the same authors' arXiv:2608.17920v1, Theorems 1.1/1.2, explicitly prove this and a vertex-inhomogeneous strengthening. Read the actual section 5 induction: condition on the maximum-degree vertex, use log-convexity of the dual membership set, and propagate local membership using optimized pressure and the strengthened Lorentzian Shearer inequality. Section 5.2 ends with the d-to-Delta induction; taking all fugacities one recovers the whole source claim. No discovery credit.
2. **Hoang–Levit–Mandrescu–Pham, arXiv:2409.00827v2, Conjecture 4.2; Discrete Mathematics 349 (2026), 115109, DOI 10.1016/j.disc.2026.115109.** Every connected W_2 graph is 2-quasi-regularizable iff n>=3 alpha. Original manuscript statement read; publisher resolver returned landing HTML, not a verified typeset full article. EXCLUDE: Pereyra arXiv:2605.14076v1, actual Theorems 4.1 and 5.1 and proof bodies. The minimal deficient nonmaximum independent set forces unique private neighbors, one universal connecting neighbor, then a localization and avoidance contradiction. The maximum-set condition is exactly n-alpha>=2alpha, giving the original iff. This is concrete published-preprint resolution evidence, irrespective of registry freshness. No new result is proposed here.
3. **Bilal Ahmad Rather, arXiv:2606.04789v1, Conjecture 1, immediately before section 4.** SELECTED full target below. Current abstract page observed lists only v1, submitted 3 June 2026, 12:14:51 UTC; no journal reference was identified there. No claim that a separately published version does not exist. Read actual definitions, section 3/Theorem 3.1 proof, Conjecture 1, and section 4/Theorem 4.1 proof before substantive experiments. MathDB375092 is a cross-check of attribution, never novelty evidence.

## Literal full target and nearest bodies

For every positive integer n, let G_n have vertices the nonzero zero divisors of Z/nZ, with distinct a,b adjacent exactly when n divides ab. Put s_k=# independent k-subsets, including s_0=1. The source asks whether the entire sequence s_0,...,s_alpha is unimodal. The empty graph cases have polynomial 1; no endpoint loophole is being used. This is the ordinary independence polynomial, not an independent domination polynomial, and not a statement about only selected gcd classes.

Rather's source already proves formulas and coefficient results for small-factor families; none is a new outcome here. Theorem 3.1 derives the p^2 q polynomial by splitting on occupancy of the clique V_pq. Theorem 4.1 splits the pqr independent sets into four families, according to which (at most one) of V_pq,V_pr,V_qr is occupied. Its binomial differences agree with this lane's gcd decomposition. No assertion of novelty for the decomposition or these formulas.

Nearest potentially misleading older source: Rather arXiv:2401.02559v1. Read its definitions, Theorem 2.1 quotation, and explicit counterexample bodies. Those count **maximal independent/dominating sets**. For Z_15 the displayed polynomial x^2+x^4 has a gap, while ordinary independence counts all subsets and gives (1+x)^2+(1+x)^4-1. Thus those old counterexamples do not refute this target. No inference from name similarity or an abstract.

Actual pinned registry bodies read at Omega6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3: D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.lean and Graph/GeneralPosition/RatherRealRootedComplete.lean. The first defines ordinary domination on shared-edge four-cycle books and refutes the all-positive-order real-root classification using B_1=C_4 and 6X^2+4X^3+X^4. The second defines general-position sets through geodesics and proves a real-rootedness/complete-graph equivalence, using its first three binomial coefficients and Newton. Neither uses the ordinary independent-set sequence of all Z_n, and neither supplies a full bridge. These are actual Lean files, not Blueprint summaries. No upstream truth audit or replay was performed.

## Route A: exact all-n class recurrence, and a rigorous failure of closure

Let D_n={d:1<d<n,d|n}, V_d={a:gcd(a,n)=d}, w_d=phi(n/d). For any a in V_d and b in V_e, prime valuations give

    n|ab iff n|de.

Indeed v_p(a)=v_p(d) when v_p(d)<v_p(n); when d contains the whole p-power, a has at least that valuation, which suffices. Apply this at every prime. Thus each class is a clique if n|d^2, an independent set otherwise; different classes are completely adjacent or nonadjacent. This handles arbitrary prime powers, not just squarefree n.

For A subset D_n define F_A as the independence polynomial of its whole-class induced graph. For d in A, let N(d)={e in A\{d}:n|de}. Then

    F_A = F_(A\{d}) + Q_d F_(A\({d} union N(d))),
    Q_d = w_d x                         if n|d^2,
          (1+x)^w_d - 1                 otherwise.

Proof: partition independent subsets according to whether they occupy V_d. Nonempty occupancy has the indicated polynomial and forbids exactly N(d). All other choices are independent. Termination at F_empty=1 proves the recurrence for every n. This is a counting identity, not a new source resolution.

A tempting closure induction would assert all F_A are unimodal (or log-concave), then try to combine the two terms. It is false, even for an actual whole-class subproblem of a source graph:

    n=847=11^2*7, A={77,121}.

V_77 has phi(11)=10 vertices and is a clique since 847|77^2. V_121 has phi(7)=6 vertices and is independent since 847 does not divide 121^2. All cross edges occur since 847|77*121. Therefore the induced graph is K_10 join E_6, and

    F_A=(1+x)^6+10x
       =1+16x+15x^2+20x^3+15x^4+6x^5+x^6.

The strict valley 16>15<20 disproves the proposed hereditary closure. routes.py independently enumerates all 2^16 literal residue subsets, without the compressed recurrence, and reproduces every coefficient. **The full G_847 polynomial is log-concave**, both by the exact recurrence and by independent substitution into the source p^2 q formula. No source counterexample follows. An induction must retain correlations with the omitted classes or impose a narrower residual structure; generic class-subset closure cannot be its invariant.

Exact checks at all 999 n in 2..1000 find log-concavity, hence unimodality. check.py compares 39 cases in 2..40 against a separate literal vertex-deletion recurrence; routes.py separately checks the 20-vertex source example n45 and five p^2 q formula identities. Finite checks cannot establish any all-n inequality.

## Route B: extension moments and the missing arithmetic inequality

For an independent k-set S in an arbitrary finite graph, let U(S) be the vertices which can extend it, A(S)=|U(S)|, and e(S)=edges induced by U(S). Double counting extensions yields

    sum_S A(S) = (k+1)s_(k+1),
    sum_S [A(S)(A(S)-1)-2e(S)] = (k+1)(k+2)s_(k+2).

For the first identity, every independent (k+1)-set has k+1 predecessors. For the second, choose an ordered pair of distinct mutually nonadjacent extension vertices: each independent (k+2)-set has (k+2)(k+1) ordered removals. These arguments establish the identities for all k without experiments.

Under uniform independent k-set S and s_k>0, ordinary log-concavity at rank k+1 is consequently equivalent to

    (k+2)(E A)^2 >= (k+1) E[A(A-1)-2e].                  (* )

This follows by substituting the two identities into s_(k+1)^2>=s_k s_(k+2) and multiplying by (k+1)^2(k+2). Equivalently one needs

    Var(A) <= E A + 2 E e + (E A)^2/(k+1).

For G_n the available vertices and their edges can be expressed entirely by the valuation classes above, but I have **not proved this variance bound**, nor a weaker bound sufficient for unimodality, for all n and k. Arbitrary residual-class induction cannot establish it: in the n847 induced obstruction at k=1, E A=30/16 and E[A(A-1)-2e]=120/16, so the left side of (*) is 675/64 and the right side is 15. The failure is exact. routes.py checks both moment identities directly for k=0..4 in that induced graph.

A still stronger shortcut, ultra-log-concavity normalized by degree, already fails in an actual full source graph: G_16 has polynomial 1+7x+14x^2+16x^3+9x^4+2x^5. At rank2, normalized coefficients give (14/10)^2 < (7/5)(16/10). The ordinary coefficients are log-concave. This is an obstruction to that stronger strategy, not to source unimodality; no credit is attached.

## Strongest objection, falsifier, precise gap

No aggregate inequality for arbitrary n has been proved. A complete class recurrence, a failed hereditary invariant, a moment reformulation and finite confirmations are helpers, not full outcomes. The entire selected question remains open in this lane. The main remaining task is a valuation-sensitive comparison controlling the sum of occupied-class contributions (or the moment inequality (*)) without assuming the disproved hereditary/ultra-log-concave assertions.

A mathematical falsifier is an actual n and three indices a<b<c with s_b<min(s_a,s_c), from complete exact counting or an ordinary proof. The exhibited induced-subgraph valley is explicitly insufficient. A preexisting public proof of the all-n claim would independently defeat eligibility even if this lane later proved it. No worldwide priority clearance is claimed.

## Access, chronology and runnable evidence

Exact retrieval URLs, UTC times, status, response headers and SHA256 are in http.jsonl and provenance.json. Sources are saved unchanged. No registry API request was made: inherited shared API403 is respected, r61 provenance reports no usable reset information, and this lane found no new reset evidence. Latest **observed** Omega6c27b0a... at15:49 is not currentHEAD; current freshness remains HOLD. Cached actual D5 Lean tree ff3d4c... was parsed for targeted paths, not treated as a current complete content audit. Root's polyomino acceptance limits were read and retained.

Publisher W2 access was a resolver landing, not an obtained verified journal proof; Rather has an observed v1-only arXiv record, not a proven absence of later journal work. Search absence and MathDB's empty solutions are not novelty certificates. Targeted live searches located the Lee–Seo successor and the distinct 2024 Rather note; they did not supply a full all-n answer. Bibliographic/journal and registry coverage remain bounded.

Run `bash run.sh` here. All Python processes use the copied capped runner: AS512MiB, group RSS512MiB, CPU210s, wall230s,40ms sampling, BLAS1. Two shards cover 2..250 and251..1000. No cap was raised; no mathematical failure or cap failure occurred. Finite checks are not proof. No git/shared/other-lane edit, children, browser, account, contact, post or upload action.
