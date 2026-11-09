# Independent review of MathDB 365710

Review date: 2026-11-01 UTC. This is an adversarial source, ordinary-proof, novelty and significance review, not acceptance. Recommendation: **HOLD** on campaign qualification; **PASS** on the ordinary proof and substantive statement fidelity. Conditional significance: **QUALIFIED_PASS**. Credit remains zero; campaign count remains 5/20 beyond 39. Root alone adjudicates acceptance.

## Scope and source fidelity

The frozen raw MathDB record asks whether the extremal complete bipartite graphs maximize sigma_t over all connected triangle-free graphs on a fixed number n of vertices. This is precisely arXiv:2411.04881v1 Conjecture 24, not an assertion only about bipartite graphs. Equation (4) defines sigma_t as the sum of squared degree differences over **unordered, distinct vertex pairs**, including nonedges. There is no factor 1/2 with this convention. It is n squared times the population degree variance. It is neither the edge-based sigma index nor the sum of absolute differences called total irregularity.

Proposition 1 supplies sigma_t = n M1 - 4m squared. Proposition 10 supplies the triangle-free bound sigma_t <= m(n squared - 4m) and its complete-bipartite equality case. Proposition 11, for n >= 7, says the optimum among complete bipartite graphs occurs at one of floor or ceiling of n(2-sqrt(2))/4 for the smaller part. It does not say the nearer integer always wins, nor that both rounded choices maximize. Comparing the two values or taking the finite maximum is faithful.

I also fetched and read the published successor, Ars Mathematica Contemporanea 26 (2026), #P4.01, DOI 10.26493/1855-3974.3268.60f. It was accepted 6 October 2025 and published online 11 August 2026. Its equation defining sigma_t, Proposition 1.1, Propositions 3.2 and 3.3, and Conjecture 6.1 retain the same relevant content. Page 11 still explicitly poses the conjecture. This is useful positive evidence of a recent surviving question, not a guarantee of no later resolution.

For n >= 2 the literal maximum value is

    B(n) = max { a(n-a)(n-2a)^2 : a an integer, 1 <= a < n }.

Proving sigma_t(G) <= B(n), together with actual attainment by K_(a,n-a), resolves the literal assertion. The wording does not additionally demand classification of every possible maximizer. The author proves that stronger classification too: every connected triangle-free maximizer is complete bipartite. Classification does not mean all complete bipartite graphs maximize.

The conjecture does not print a numerical lower bound on n, but its nondegenerate complete-bipartite interpretation presumes n >= 2, consistent with the source's small-order discussion. State n=1 separately: its only graph has sigma_t=0; it can be called K_(0,1) only if empty parts are allowed. Do not silently assert existence of two nonempty parts for n=1. Empty graphs require a separate connectivity convention and are outside the intended nonempty setting.

## Ordinary proof: independent adversarial audit

All substantive steps of SIGMA-ORDINARY-PROOF.md pass. The following checks are mathematical, not conclusions inferred from enumeration.

1. Expanding the unordered pair sum gives n times the sum of squared degrees minus the square of the degree sum. The handshake lemma gives the claimed identity. Also sum over edges of d(u)+d(v) is M1: each vertex contributes its degree once for each incident edge.

2. In a triangle-free graph, endpoint neighborhoods of an edge are disjoint, including the endpoints themselves in the opposite neighborhoods. Thus n-d(u)-d(v) counts vertices adjacent to neither endpoint. Summing counts every induced one-edge triple exactly once, by its unique edge. Consequently D=nm-M1 is a nonnegative integer counting **unordered** three-element vertex sets. No multiplicity three or six enters.

3. A connected triangle-free graph of order at least two with no induced P4 is complete bipartite. Fix v, take A=N(v), B=V minus A. Connectivity and absence of induced P4 imply all distances from v are at most two: the first four vertices on a shortest path of length at least three induce P4. For b in B minus {v}, choose a in A adjacent to b. If a' in A is not adjacent to b, then b,a,v,a' is an induced P4; all four vertices are distinct, and the three missing chords follow from triangle-freeness and b not adjacent to v. Hence every b meets all of A. A is nonempty and independent; an edge in B would make a triangle using any a in A. This gives both independent parts and every cross edge. Connectedness is essential.

4. On an induced path a-b-c-d, the one-edge triples are exactly {a,b,d} and {a,c,d}. For any other vertex x, its path-neighbor set S is independent. If no triple involving x and two path vertices has exactly one edge, S must cover each path edge. An independent vertex cover of a connected bipartite path has to be one entire bipartition class: each edge has exactly one endpoint in S, forcing alternating membership. The possibilities are {a,c} and {b,d}. Either makes {x,a,d} a one-edge triple, contradiction. Thus each exterior vertex supplies at least one triple. Select one by finite choice or the least pair in a fixed ordering. These triples have exactly one exterior vertex, so different x cannot collide. They cannot collide with either triple wholly in the path. Hence D >= 2+(n-4)=n-2. Edges among exterior vertices do not affect this injection.

5. For n >= 7, h(t)=t(n-t) increases for integer 1 <= t <= floor(n/2). Its first value n-1 is <= n squared/8 (the polynomial n squared-8n+8 is positive at 7 and increasing thereafter), and its last value floor(n squared/4) is >= n squared/8. A target hit or consecutive bracketing pair therefore exists. A consecutive increment is n-2t-1 <= n-3; selecting its nearer endpoint gives distance <= (n-3)/2. The identity h(n squared-4h)=n fourth/16-4(h-n squared/8)^2 proves B(n) >= n fourth/16-(n-3)^2. A target hit, parity of n, the final interval, and equality of endpoint distances cause no exceptions.

6. Completing the square in m gives sigma_t <= n fourth/16-n(n-2) for a non-complete-bipartite connected graph. Since n(n-2)-(n-3)^2=4n-9>0, this is strictly below B(n) for n >= 7. For n=4,5,6 the same bound gives 8, 385/16, 57, strictly below the star's values 12,36,80 respectively. For n=2,3 the connected triangle-free graphs are respectively K2 and P3. For n=1 there is only the singleton. No non-complete-bipartite case was missed.

7. K_(a,n-a), with both parts nonempty, is actually connected and triangle-free. Its within-part degree differences vanish, and its a(n-a) cross pairs have squared difference (n-2a)^2. This proves the endpoint is attained and makes the strict exclusion of other graphs meaningful.

No ordinary-mathematics correction is required. For formalization, the compressed independent-vertex-cover argument should be expanded into the alternating-membership reasoning above.

## Independent exact diagnostics

The reviewer wrote scripts/verify.py from scratch, without importing or running the author script. It recursively constructs every labeled triangle-free graph by adjoining a vertex with an independent neighbor set. Each graph occurs exactly once by deletion of its highest label. Connectivity is checked by bitset reachability; complete bipartiteness is checked by explicit adjacency across the partition N(0), its complement. Sigma_t is computed directly over unordered pairs, independently of the degree-sum identity.

The run completed with exit status 0, in approximately 21.8 seconds wall time and 11 MiB peak RSS, one Python compute thread, under CPU 120 seconds, address-space 6 GiB and external wall 140 seconds limits. The full output is logs/verify.log. It covers all labeled graphs through n=8; connected counts for n=1,...,8 are 1,1,3,19,207,3571,93243,3603139. All obey the conjecture, the strict non-complete-bipartite inequality, and the deficit bound. Minimum deficits among non-complete-bipartite connected graphs are 2,3,4,5,6 at n=4,...,8. Thus the gap is sharp in these orders.

The induced-one-edge count is independently computed from triples for every connected graph through n=7. All eight triangle-free one-vertex extensions of a fixed P4 have explicit witness pairs logged. Integer bracketing is checked exactly through n=100000 using binary search and the denominator-cleared inequality; no floating-point arithmetic is used. Exhaustive order 9 would be substantially beyond this script's per-call budget; I did not start an unfinished order-9 run. These diagnostics support the audit and do not replace its unbounded proof.

## Prior art and routine-corollary risk

**Zhou, Zagreb indices, MATCH 52 (2004), 113-118: all six scanned pages actually read visually.** In particular Theorem 5, pp.115-116, proves M1<=nm for triangle-free graphs with m>0, with equality precisely for complete bipartite graphs. No n-2 strict-gap strengthening appears in its body. Its equation (1), together with d_i+e_i+f_i=m in a triangle-free graph, already implies

    M1 = nm - sum_i f_i,

where f_i counts edges in the set of nonneighbors of vertex i. This is exactly the author's induced-one-edge deficit identity in another notation. **That identity should be credited to this old proof, not advertised as a new theorem.** The new content needing clearance is the connected non-complete-bipartite lower bound sum f_i >= n-2 and the extremal use of that gap with rounding.

The mere classical bound and its equality classification do not settle integer rounding. Even adding parity and a strict integral gap of 2 need not dominate the rounding loss: at n=100, B(n)=6247500 while the continuous maximum is 6250000. The numerical relaxation m=1250, D=2 yields sigma_t=6249800, above B(n), without contradicting M1<=nm or its strictness. This is a relaxation example, not a claimed graph. Thus the author is supplying a real missing argument; the known inequality alone is insufficient.

**arXiv:2507.14568v1 and v3: definitions and relevant tree/bipartite theorem bodies read.** The v1 title is the title in the assignment; v3 is titled “Extremal Irregularity Bounds for Albertson Index in Trees and Bipartite Graphs with Degree Sequence,” dated 13 December 2025. Both define sigma as the sum of squared differences over **edges**. Relevant v3 Section 4 contains Lemma 4.1 and Theorems 4.2-4.3, involving minimum/maximum degrees, part sizes and the bound n1 fourth+n2 fourth; it does not prove the requested all-pair extremum or reduce arbitrary triangle-free graphs to bipartite graphs. The complete-bipartite formula coincides for edge and all-pair sigma there, but this coincidence is not a bridge for general graphs. v1 Section 3.2 also concerns edge sigma and trees. No Conjecture 24 resolution was found in these inspected bodies; unrelated theorem correctness was not certified.

**Goldberg, arXiv:1308.3867v1, A spectral bound for graph irregularity: full five-page extracted body read.** Theorems 1.1 and 1.2 bound Albertson's edge absolute-difference index by expressions involving nM1-4m squared and the Laplacian spectral radius. This does not give the needed upper bound on all-pair sigma_t or the strict deficit. The local source basename 'nikiforov' is a fetch-script label error; the actual author is Felix Goldberg, not Nikiforov.

**Published Filipovski et al. 2026 body: relevant Sections 1,3,5,6 and references read.** It explicitly retains the target and adds Caro-Yuster, Graphs with large variance, Ars Combinatoria 57 (2000), 151-162. Its Section 3 correctly credits their Theorem 1.2 for the general-graph variance maximum, unlike treating that old result as new. The extremizers there are unrestricted graphs, not this triangle-free class. That observation does not rule out a more relevant result elsewhere in the Caro-Yuster body.

**Material unread bodies:** Bell (1992), A note on the irregularity of graphs, was located by metadata; the publisher PDF route returned HTTP 403 on 2026-11-01. No retry or circumvention was attempted. Bell's precise theorem scope and any strict-gap result remain uncleared. Caro-Yuster's author-site PDF connection timed out after 35 seconds; no body was received and no retry was attempted (receipts/caro-body.json). The complete 2023 Dimitrov-Stevanovic paper, Réti 2019, Snijders 1981, and all later citing literature have not been fully read. General total-irregularity results use absolute differences and cannot be identified with sigma_t by title alone.

OpenAlex resolves the arXiv and journal target to W4415114651 and reports zero citing works, also returning an empty citing-list query. This is plainly an index-coverage limitation, not proof that no papers cite it. The arXiv API query for the exact identifier returns no entries; this API is not a full-text citation index. Bounded OpenAlex searches for strict Zagreb gaps and triangle-free degree variance produced no verified subsumer. Search metadata is not treated as mathematical clearance. The earlier root arXiv search log was read as context only.

## Live registries

Both head requests used the mandated /commits/HEAD route, successfully on 2026-11-01. OpenAI HEAD is 4eaee87548250b2682affda7d05d947c05554bae, committed 2026-10-30T00:35:35Z, the same revision checked in the author lane. The historical pinned upstream revision is fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; that old pin alone is not live clearance.

Omega HEAD is **3ca0ba6c579f2685c52d95a4a6b8a07d037382c9**, committed 2026-11-01T16:59:48Z, newer than the author's ce5be22... snapshot. The current commit changes CLAUDE.md for Lean cache governance. Its recursive root tree is truncated and is explicitly not used for a complete screen. I fetched the nonrecursive root, then the current D5 and Problems subtrees by their immutable tree hashes. Both subtrees are untruncated (13313 and 1631 entries). A bounded title/path screen found only unrelated graph irregularity and triangle-free items; see logs/*-screen.json. This is not a semantic scan of every theorem body. No claim of registry-wide nonduplication is made.

## Literal Lean target and semantic traps

A precise endpoint avoiding radicals is as follows. Work over SimpleGraph (Fin n), with decidable adjacency and actual finite degrees. Define the integer-valued quantity

    sigmaT G = sum u in Fin n, sum v in Fin n with u < v,
                 ((G.degree u : Int) - (G.degree v : Int))^2.
    F n a = (a : Int) * ((n : Int) - a) * ((n : Int) - 2*a)^2.

Here every occurrence of a in F is cast to Int before subtraction. For every natural n >= 2 prove

    exists a : Nat, 1 <= a and a < n and
      (for every b : Nat, 1 <= b -> b < n -> F n b <= F n a) and
      (for every G : SimpleGraph (Fin n),
        G.Connected -> G.CliqueFree 3 -> sigmaT G <= F n a).

Also define an actual graph K(n,a) by adjacency iff exactly one of u.val<a and v.val<a holds; prove for 1<=a<n its Connected and CliqueFree 3 properties and sigmaT K(n,a)=F n a. This supplies literal extremal attainment. For the stronger author claim, prove under the same hypotheses

    (for every H on Fin n, Connected H -> CliqueFree 3 -> sigmaT H <= sigmaT G)
      -> exists A : Finset (Fin n), A.Nonempty and
         (Finset.univ minus A).Nonempty and
         (for every u v, G.Adj u v iff (u in A iff v not in A)).

The last equivalence expresses opposite membership, so it excludes loops automatically. For n=1 prove sigmaT=0 separately. These are specifications, not compiled Lean declarations or an existing certificate. The weaker existence-of-a-complete-bipartite-maximizer theorem is enough for the record.

Traps: Nat subtraction would truncate negative degree differences and n-2a; casting must precede subtraction. An ordered double sum counts twice; an edge sum changes the invariant. A bipartite hypothesis loses odd-cycle triangle-free graphs. CliqueFree 3 is required, not clique number exactly 2. Edge finsets count unordered edges once, neighbor finsets count incident edges, and triple finsets must count three-element sets once. An induced P4 requires all nonconsecutive nonedges and four distinct vertices, not merely a walk or non-induced path. Complete bipartite means all cross edges, not merely a coloring with two colors. A maximizer's partition must exist up to relabeling; it need not be the first a labels. A natural-valued D definition requires proof of nonnegativity before subtraction identities. Finite maxima need nonempty domains. Graph abstraction, finite relabeling, witnesses, all combinatorial counting identities and rounding lemmas must be proved, not parameters assumed by a terminal arithmetic theorem.

The proof uses only finite combinatorics and rational polynomial inequalities. Feasibility is good in principle; the likely workload is the induced-path and counting bridges rather than analysis. No Lean theorem, dependency pin, axiom audit or extracted replay was supplied or performed in this review. Only propext, Classical.choice and Quot.sound would be allowed for eventual acceptance.

## Verdict and actions

The ordinary result would be a full-scope resolution of a named conjecture still printed as open in the August 2026 publication. It is not a parameter instance, wording fix, tree-only theorem or mere formalization. The additional gap and rounding argument prevent dismissal as an immediate use of Proposition 10. This warrants conditional significance QUALIFIED_PASS.

Nevertheless, the principal invariant identity is already in Zhou's proof, the new deficit bound is elementary, and the degree-variance literature has a material unresolved body-level gap. I cannot certify that the bridge is new rather than a routine application of an existing strict-gap or variance theorem. Therefore novelty and overall campaign qualification are HOLD, not PASS or FAIL. No known disqualifying prior resolution was located in the actual bodies read.

Next actions: clear Bell and Caro-Yuster by lawful access or explicitly adjudicate the missing-body risk; investigate connected triangle-free strict Zagreb-deficit / induced-one-edge-triple bounds and later citing papers; credit Zhou's deficit identity. Only after root's novelty decision should a literal Lean implementation be commissioned, independently reviewed, pinned, axiom-audited and rebuilt from an extracted packet. None of these gates may be replaced by the finite tests here.

All writes were confined to this review lane. No git, shared ledger edits, messages to outsiders, browser tabs, publication or upload occurred. The frozen-lane before/after hashes and preservation result are under receipts/. The first brief/proof/source snippets were read before the baseline was recorded; that sequencing limitation is explicitly recorded, rather than claiming a before-first-read hash that was not made. Subsequent analysis used the hashed frozen inputs. No background process is left running at handback.
