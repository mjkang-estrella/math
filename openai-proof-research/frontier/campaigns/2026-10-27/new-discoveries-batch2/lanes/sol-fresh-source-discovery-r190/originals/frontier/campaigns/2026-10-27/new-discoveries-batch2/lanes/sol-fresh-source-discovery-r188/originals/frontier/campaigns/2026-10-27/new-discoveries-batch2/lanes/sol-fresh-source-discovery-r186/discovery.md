# r186: exact labeled graph counting — unresolved

## Selected statement and source

Daniel Lokshtanov, Section 4.4, printed p.117 of Agrawal–Chudnovsky–Paulusma–Schaudt–Codsi, *Solving Problems on Graphs: From Structure to Algorithms*, Dagstuhl Reports 15(1),105–121, DOI 10.4230/DagRep.15.1.105. The publisher metadata gives publication 2025-10-02; the seminar was 2025-01-19–24. Actual publisher PDF and HTML agree. This is the published source, not a database paraphrase.

For input positive integers n,k, count graphs on the labeled vertex set [n] having at least one vertex cover of cardinality at most k. Is there an algorithm taking time 2^{o(n²)}? Interpret the question uniformly in k (k≥n is trivial), with exact integer output. A positive answer must provide a single uniform algorithm and a worst-case exponent f(n)=o(n²), including all 1≤k<n. No fixed-k or almost-all-graphs result answers it. The source does not explicitly specify randomization; no randomized shortcut is claimed here.

Define C(n,k) to be this count, N=binom(n,2), and s=n-k. A vertex cover is the complement of an independent set. Complementation is a labeled bijection, so

    C(n,k) = 2^N - F(n,s),

where F(n,s) counts labeled K_s-free graphs. In particular C(n,n−3)=2^N−T(n), with T(n) the exact triangle-free graph count. This necessary parameter instance receives no separate nomination or credit. It exposes the main obstacle already within the full question.

## Early history and public screening

Before selecting the statement, `early-screen.json` screened report DOI, seminar number/title aliases and neighboring leads. `statement-screen.json` then screened Lokshtanov, graph counting, monotone-subsequence aliases, and author names across the refreshed union of r183/r182/r181/r180/r178/r170 indexes. There were 2,527 records, 11 changed/new and no missing records. Hits on Lokshtanov in unrelated graph papers do not investigate this exact counting question. Every qualified record was copied, with no drift at capture (`original-copy-provenance.json`). Original r111–113 records survive, not just later summaries. No new echo exclusions were made; inherited counterpart/provenance data remain available. This is a bounded lexical history screen, not a semantic guarantee over all mathematics.

Bounded broad public searches covered graph structural/extremal and counting leads, not just three previously failed targets. The published Dagstuhl report supplies a genuinely fresh exact question. Neighboring report problems (treewidth, clique-width, atoms) were screened but not selected: no concrete all-scope route was developed. The threshold survey 2610.22838 was reconnaissance: a prior lane already uses its resolved spectral material; its integrality/master-identity questions introduce definition/formulation issues and are not adopted. The dissociation-set search returned an asserted 2026 public resolution, so this was not spent as a fresh slot; no independent endorsement of that unread proof is made. The Levit–Itskovich subsequence lead was not selected: publisher access returned 429 on the first web open, and no retry/bypass was made. Exactly one fresh statement is selected here.

The inherited actual registry inventories were re-screened with candidate aliases. Broad TriangleFree hits included two cached original proof bodies, copied with Git blob identities matching the inherited inventory: Sahbi star-forming equality refutation and Ahanjideh–Ekim–Yıldız dense configurations. Their actual statements concern extremal parameters/configurations in individual graphs, not counting labeled graphs. The latter's opening definitions and structural content were read, not its entire dependency corpus. Other path hits include ordinary VertexCover library helpers and hash-substring noise (25041 inside hash filenames); these are not novelty evidence. Current HEAD, capped historical intervals and missing merge trees remain PARKED. No public exact resolution of the selected question was found in the bounded public title/author/alias searches, but current registry proof-body coverage is incomplete. No novelty PASS is issued.

## Material companion/classical bodies read early

1. Hébert-Johnson–Lokshtanov–Vigoda, *Counting and Sampling Labeled Chordal Graphs in Polynomial Time*, publisher ESA2023 PDF, DOI 10.4230/LIPIcs.ESA.2023.58; latest arXiv2308.09703v2 (2024-10-03). Actual Theorem1/1.1, evaporation definitions, state definitions and recurrences, full-version Section3.4 proof/Lemma3.13 and Section5.1–5.2 structural proof bodies were read. Their polynomial algorithm is for chordal graphs, with clique/color bounds. The canonical evaporation proof relies on simplicial vertices and clique separators. A cycle C5 is triangle-free and has no simplicial vertex, so direct use on F(n,3) cannot even begin. Neither complementation nor exchanging clique and cover parameters removes the chordality hypothesis. No classical bridge to all graphs is supplied.
2. Jenssen–Perkins–Potukuchi–Simkin, arXiv2410.22951v1 (2024-10-30; live abstract lists v1 only), *Sampling and counting triangle-free graphs near the critical density*. Actual definitions of Z(λ), Theorems1.1–1.3, Sections1.1 and5.6 proof of Theorem1.3 were read. At p=1/2, Z(1)=T(n). Theorem1.3 provides relative approximation with ε≥C'exp(−sqrt n), runtime polynomial in n,1/ε. Rounding an arbitrary exact T(n) requires absolute error <1/2, hence relative tolerance on the order of 1/T(n), potentially 2^{−Θ(n²)}: balanced bipartite subgraphs alone give T(n)≥2^{floor(n²/4)}. The allowed accuracy floor is far too coarse for that rounding argument, and its polynomial dependence on 1/ε would not certify subquadratic-exponential exact time even if extended. This does not prove exact counting impossible; it blocks this proposed classical bridge. The partition-function identities below are classical inclusion–exclusion, not nominated discoveries.

## Sustained universal route: signed clique-union compression

For 2≤s≤n let E_S be the event that the s-subset S is independent in a uniformly chosen graph. For a nonempty family A of s-subsets, let U(A) be the union of all pairs contained in its members. Inclusion–exclusion gives the exact finite identity, for every n,s,

    C(n,n−s) = Σ_{A≠∅} (−1)^{|A|+1} 2^{N−|U(A)|}
             = Σ_F c_s(F) 2^{N−|E(F)|},
    c_s(F) = Σ_{A≠∅: U(A)=E(F)} (−1)^{|A|+1}.

Proof: a graph contributes Σ_{∅≠A⊆I_s(G)}(−1)^{|A|+1}, which is 1 when its collection I_s(G) of independent s-subsets is nonempty, and 0 otherwise. For each fixed A exactly N−|U(A)| edges remain free. All sums are finite, so interchange is valid. This closes every quantifier of the identity, not the source running-time question.

A plausible uniform route is to evaluate this signed sum by an algebraic decomposition that collapses structured quadratic families at once. Simply storing all distinct clique unions, even only nonzero c_s, provably fails to deliver that bound. The following obstruction and exact collapse show both what is needed and what one structured component permits.

Fix s=3, one apex x, disjoint sets A,B of sizes a,b, n=a+b+1, and an arbitrary nonempty bipartite graph H⊆A×B. Let F_H consist of the H edges and the two apex spokes for every endpoint active in H. All triangles of F_H are exactly {x,u,v} with uv∈H: A,B are independent and no other triangles exist. Every uv is contained in exactly that one triangle. Thus a family of triangles covers E(F_H) iff it contains every one of these |H| triangles, giving

    c_3(F_H) = (−1)^{|H|+1} ≠ 0.

The cross edges recover H, so the F_H are distinct. With a,b as balanced as possible there are 2^{ab}−1 = 2^{Θ(n²)} nonzero union states. This excludes the proposed explicit-state enumeration method, not all algorithms or the source question. Quotienting these states by graph isomorphism alone saves at most an n! factor and still leaves 2^{Θ(n²)} states.

Nevertheless this entire family can be summed exactly in O(ab) arithmetic terms. Let v(H) count active vertices and define

    Z(a,b) = Σ_{H⊆A×B} (−1/2)^{|H|}(1/2)^{v(H)}
           = 2^{−(a+b)} Σ_{i=0}^a Σ_{j=0}^b
               binom(a,i)binom(b,j) 2^{−(a−i)(b−j)}.

Complete proof: for each vertex u, its contribution to (1/2)^{v(H)} equals (1+1_{u isolated in H})/2. Expand the product over all a+b vertices, obtaining 2^{−a−b} times a sum over subsets S of vertices required to be isolated. If S contains i vertices of A and j of B, the remaining H is an arbitrary subset of the (a−i)(b−j) allowed edges. Summing (−1/2)^{|H|} gives (1−1/2)^{(a−i)(b−j)}. There are binom(a,i)binom(b,j) choices of S, proving the formula for all nonnegative integers a,b, including zero. It follows that the contribution from nonempty F_H is exactly

    2^N (1−Z(a,b)).

Indeed |E(F_H)|=|H|+v(H), and subtracting the empty H term 1 reverses the sign. Clearing denominator 2^{ab+a+b} evaluates the expression with polynomial-bit integers; since ab+a+b≤N, the total expression is an integer. This is a useful algebraic test of cancellation compression, not a new eligible theorem: it is a routine binomial/isolated-vertex transform.

## Exact missing step and strongest objections

The route must partition or algebraically combine *all* clique-union contributions without double counting, then evaluate the full sum in 2^{o(n²)} bit operations uniformly in s. No such decomposition or evaluation bound is proved. Nonapex overlaps occur already on K4: its four triangles cover its six edges iff at least three are selected, so c_3(K4)=4−1=3. No single apex belongs to all four triangles; the one-apex calculation cannot account for this coefficient using its original unique-triangle edge argument. Even apex families with different choices of x,A,B overlap. Adding their closed forms is therefore invalid.

The obstruction is global algebraic control of arbitrary clique overlap, not failure to check larger n. The triangle-free slice alone remains unclosed. The k=o(n) regime can be handled by enumerating candidate covers and edge choices in n^{O(k)}2^{O(kn)} time with deduplication; that parameter regime gives no full uniform bound and is not selected separately. Likewise C(n,n−2)=2^N−1 is a trivial endpoint, not a discovery.

Alternative canonical-neighborhood transfer is exact but does not solve the complexity gap: when extending a triangle-free graph G, its new neighborhood can be any independent set of G. Storing the full labeled independent-set profile retains all pairs and hence recovers G, so its unrestricted state space is quadratic exponential; even triangle-free bipartite G already give 2^{floor(t²/4)} different profiles. Compressing only by |V|,|E| or independence number discards continuation information. No theorem justifies a smaller sufficient profile.

## Validation and disposition

`checks.py` independently enumerates all labeled graphs through n=6, checks all cover thresholds, checks the complement triangle-free identity, compares the full event inclusion–exclusion with direct counts through n=5, checks c_3(K4)=3, and compares direct apex-family rational sums with the collapsed formula for 15 pairs (a,b), ab≤12. There are 9,403 nonempty apex-family controls and ten full inclusion–exclusion controls. These are diagnostics of the displayed identities, not evidence of a universal running-time claim. First run passed; no numerical floats are used.

Disposition: one fresh unresolved attributed statement sustained, zero full candidates. No PROOF.md because there is no full source proof. No Lean, manuscript, child agents, browser, git/shared/count edits, uploads, messages or public posts. Root owns review/investment/acceptance. Counts remain 9 additional /39 total, next40. Bounded source/novelty limits and parked registry gaps prevent any priority certification.
