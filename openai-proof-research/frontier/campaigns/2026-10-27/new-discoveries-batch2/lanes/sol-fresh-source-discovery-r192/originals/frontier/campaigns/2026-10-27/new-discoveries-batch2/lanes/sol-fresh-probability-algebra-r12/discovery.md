# No complete eligible result: finite-ring MSN-energy classification remains open

Credit 0. Counts remain 3/30 additional, 33/60 total. This lane has no acceptance authority. No Lean, paper or PROOF.md was produced.

## Source selection and exact scope

Selected Tak–Dutta–Nath, *Minimum second neighborhood degree energy of commuting graphs of finite rings*, arXiv:2605.22160v1, submitted 21 May 2026, Problem 5.2. Actual source HTML and latest abstract/history retrieved 29 October 2026, 05:40 UTC; only v1 is listed. Primary URL: https://arxiv.org/html/2605.22160v1 . Read the definitions, equations (1)–(2), Section 5 theorem/proof bodies and final problems, not merely the abstract.

Problem 5.2 asks for examples of finite noncommutative rings with MSN-hyperenergetic commuting graph, AND a characterization of all such finite rings. Both clauses matter. The example construction below is not a solution of the complete problem, not a refutation of a universal assertion made by its authors, and not a nominated discovery. The strongest objection is both incomplete scope and routine classical spectral reduction. There is no specific MathDB ID claimed for Problem 5.2.

The commuting graph has vertices R minus Z(R), with two DISTINCT vertices adjacent precisely when they commute. For a vertex x, the source uses N²(x)=(union over y in N(x) of N(y)) minus {x}. This includes neighbors in triangles; it is NOT the set of vertices at distance exactly two. Put delta₂(x)=sum of the ordinary degrees of vertices in N²(x). The MSN matrix has off-diagonal entry min(delta₂(x),delta₂(y)) on an edge, and zero elsewhere. Its energy is the sum of absolute eigenvalues. MSN-hyperenergetic means this energy exceeds 2(n−1)³, the source's complete-graph benchmark on n vertices.

Immediate stale-target exclusions: Conjecture 5.1, concerning finite CC-rings, is explicitly proved by Theorem 5.2 in the SAME source. Its graph is a disjoint union of cliques; Theorem 5.3 supplies the corresponding general graph result. Theorem 5.4 and Corollary 5.5 explicitly prove the nearby CN-energy conjectures. Cached MathDB374875 and 374874 still said open, but these labels cannot override the actual proofs. Neither is pursued or credited. This screen therefore continued beyond the stale-target exclusion to the untouched Problem 5.2.

## Ordinary partial derivation: explicit associative rings, not a classification

The following argument is complete for its displayed family. It uses elementary bilinear algebra and classical symplectic graph spectra; the latter are independently re-derived here to make every bridge inspectable. This does not establish novelty.

Let m>=2, V=F₂^m ⊕ F₂^m, and write u=(x,y). Define B(u,v)=x dot y' for v=(x',y'). On A_m=V ⊕ F₂ use componentwise addition and

    (u,c)(v,d) = (0,B(u,v)).

This is a finite associative ring of order 2^(2m+1), usually without a unit. Bilinearity gives both distributive laws. Every product lies in W=0⊕F₂, and W annihilates A_m on both sides; hence every triple product is zero and associativity follows. The commutator is (0,F(u,v)), where

    F(u,v)=B(u,v)+B(v,u)=x dot y' + x' dot y.

This alternating form is nondegenerate: testing v=(e_i,0) kills every coordinate of y, and testing v=(0,e_i) kills every coordinate of x. Consequently Z(A_m)=W, of size 2. The ring is noncommutative since (e_1,0) and (0,e_1) have commutator 1 in W.

A unital example is its standard F₂-unitization U_m=F₂ ⊕ A_m. With coordinates (a,u,c), multiplication is

    (a,u,c)(b,v,d)=(ab, av+bu, ad+bc+B(u,v)).

For completeness, expanding either parenthesization of three factors gives scalar abc (with scalar letters renamed as needed), vector ab*w+ac*v+bc*u, and the same central terms by bilinearity B(av+bu,w)=a B(v,w)+b B(u,w) and B(u,bw+cv)=b B(u,w)+c B(u,v). This is also the standard identity (a,x)(b,y)=(ab,ay+bx+xy) in a unitized associative algebra. Its identity is (1,0,0). Scalar terms commute, so the commutator is still (0,0,F(u,v)). Therefore its center consists precisely of the four elements (a,0,c), and |U_m|=2^(2m+2).

For either ring, noncentral vertices are indexed by u!=0 and t central labels, where t=2 for A_m and t=4 for U_m. Adjacency between different u,v is F(u,v)=0, and each set of t vertices over one u is a clique. The commuting graph is the clique extension of the classical graph H_m=Sp(2m,2) by t, with adjacency

    G = (H+I) tensor J_t − I.

This identity follows entry by entry; it is not inferred solely from a catalogue label.

Put a=2^m. The graph H has v=a²−1 vertices and degree k=a²/2−2. Indeed the orthogonal hyperplane to a nonzero vector has a²/2 elements, and 0 and that vector are omitted. For two distinct vectors, the two nonzero independent linear constraints have an intersection of size a²/4. If the vectors commute, remove 0 and both vectors, giving lambda=a²/4−3 common neighbors. If they do not commute, only 0 belongs to this intersection among these three vectors, giving mu=a²/4−1 common neighbors. In particular every pair has a common neighbor for m>=2, since lambda>=1 and mu>=3; H is connected.

Counting length-two walks proves the exact matrix identity

    H² = −2H + mu I + mu J.

The real symmetric matrix H has eigenvalue k on constants. On their orthogonal complement J vanishes, so its eigenvalues must be r=a/2−1 or s=−a/2−1. Their multiplicities f,g are determined by dimension and trace:

    f+g=a²−2,     k+fr+gs=0,
    f=(a²+a−2)/2, g=(a²−a−2)/2.

The eigenvalue k is simple by connectedness; alternatively its eigenspace simplicity follows from the standard sum over edges of (x_i−x_j)². Thus the displayed list is exhaustive. It agrees with Brouwer's public classical parameter and eigenvalue tables, retrieved and retained as closest actual prior bodies.

For the clique extension, split the vector space into vectors constant on each fiber and vectors with sum zero in every fiber. On the first space G acts as tH+(t−1)I; on the second it acts as −I. Hence the entire ordinary adjacency spectrum is

    d=t(k+1)−1         multiplicity 1,
    t(a/2)−1          multiplicity f,
    −t(a/2)−1         multiplicity g,
    −1                multiplicity (a²−1)(t−1).

There are n=t(a²−1) vertices. Every distinct pair in the extension has a common neighbor: for distinct base vertices use the preceding counts; for a shared base vertex use a neighbor of that base vertex (k>=6). Consequently N²(x) contains every vertex except x, and delta₂(x)=(n−1)d. The MSN matrix is exactly (n−1)d G. Multiplying the absolute values of the displayed eigenvalues by this positive integer gives the FULL MSN-energy, with no numerical eigenvalue approximation.

For m=3, t=4, U_3 has order 256, center size 4, and a commuting graph with n=252, d=123. Its adjacency spectrum is

    123^1, 15^35, (−17)^27, (−1)^189.

Its ordinary energy is 1296. Thus delta₂=251*123=30873 and

    E_MSN = 30873*1296 = 40,011,408
          > 2*251³ = 31,626,502.

This proves existence even under a convention requiring a multiplicative identity. The smaller nonunital A_3 has order 128, n=126, degree 61, adjacency energy 612, and MSN-energy 4,666,500 > 3,906,250.

One can also read off an infinite nonunital family without asymptotic guesswork. For t=2 the ordinary energy is a³+2a²−3a−4, and hyperenergeticity is equivalent to

    P(a)=a⁵−6a⁴−6a³+14a²+9a−6 > 0.

For a>=8, a⁴(a−6)−6a³ >= 2a³(a−3)>0 and 14a²+9a−6>0, proving the assertion for all m>=3. This remains a family calculation, not the all-ring characterization.

## Failed full-classification route and exact unresolved step

The source proves CC implies non-hyperenergetic. The tempting converse would classify hyperenergeticity by failure of the CC property. It is false, not merely unproved. For m=2, t=4, the ring U_2 is non-CC: in the centralizer of the element with u=e_1 lie elements with u=e_2 and u=f_2, and those two elements do not commute. Nevertheless its graph has n=60, degree 27, ordinary energy 180, and

    E_MSN=286,740 < 410,758=2*59³.

The same obstruction occurs for nonunital A_2. Thus neither “all non-CC rings are hyperenergetic” nor “every MSN-integral ring is CC” survives: these examples are non-CC, MSN-integral, and not hyperenergetic. No classification follows from the CC dichotomy.

The next attempted route was to extend the regular-graph formula to arbitrary centralizer structures. What is actually known is delta₂(x)=sum_{y!=x, C(x) intersect C(y) has a noncentral common neighbor distinct from x,y} (|C(y)|−|Z(R)|−1). In the displayed family this is constant because all distinct pairs have common neighbors and all centralizers have equal size. Neither property is proved or true as a general ring hypothesis: the source's own CC-rings can have disconnected commuting graphs, with no cross-component common neighbors. For a general ring the MSN matrix is not a constant times the adjacency matrix; min(delta₂(x),delta₂(y)) varies on edges. No necessity theorem reduces a hyperenergetic arbitrary ring to the bilinear family, or to a finite list of centralizer geometries. This is the precise missing bridge to the source's characterization clause. Restating the spectral inequality in terms of that matrix is tautological and is not offered as a characterization.

The displayed example does not refute Conjecture 5.1: it is explicitly NON-CC. It does not refute a “no examples exist” conjecture, because the source only asks a question. Its all-m extension does not supply the missing necessity theorem. Per instruction, partial/family results earn zero even if the existence clause was previously unanswered.

## Prior bodies, coverage and limitations

The classical symplectic graph parameters and eigenvalues appear at https://aeb.win.tue.nl/graphs/Sp.html and https://aeb.win.tue.nl/graphs/srghub.html . Both primary author pages were fetched, and the exact ordinary proof above independently supplies the required bridge. The graph spectrum itself is not new. Realizing it through a two-step algebra and scaling a regular graph's adjacency matrix is a strong routine-corollary objection, not evidence of substantive novelty.

Read Manilal–Harikrishnan, *On Minimum Second neighborhood Degree Energy of Graphs*, actual published PDF, DOI10.37193/CMI.2024.02.07, especially definitions and Proposition3.1/Example3.1 and related regular-graph formulas. Its Proposition3.1 asserts a dense constant off-diagonal matrix for an arbitrary regular graph. That expression cannot be used under the literal edge-supported definition: for example a nonedge must have matrix entry zero. This lane avoids that formula entirely and uses the newer source's explicit union-minus-self definition. No credit is sought for diagnosing that inconsistency or resolving its convention. The newer source cites Harikrishan–Manilal, *Minimum second neighborhood energy of commuting graphs of finite groups*, reference26, only as “preprint”; targeted title/author searches found no actual body. That is an explicit closest-companion coverage gap, not clearance.

Current public searches on 29October2026 covered the exact source number/title, MSN-hyperenergetic rings, symplectic commuting spectra, and the reference26 title. They found the source and classical graph material but no read complete resolution of Problem5.2. This is a bounded negative search, not worldwide priority evidence or a citation-index audit.

Per the user instruction and existing GitHub API rate limit, reused r7's recent complete D5/Problems and OpenAI preprint trees, count-ex-machina registry, head receipts and current CONTENTS. Their retrieval interval is 29October2026 04:39–04:43 UTC. Omega head67b4fae085cf19003a33f8027410c383b49e5046 (commit04:37:11UTC), count head dbf673741a54c7dc9d88a6aec0e8148a538f4a3a (9September), OpenAI head7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a (26October). These were not refreshed here. Targeted topic/path checks and catalogue checks found no matching target; registry-screen.json preserves exact cache URLs/hashes, terms, matches and nontruncation checks. This is not whole-proof code inspection. No API traversal or direct MathDB request was made. Cached MathDB entries are dated28October03:59UTC. The pinned initial catalogue is fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb,8October, read as a locator rather than novelty evidence.

Relevant history read: ancestor/batch AGENTS, ledger and prior-campaign-context, latest NEXT checkpoints, r11 geometric-analysis SUMMARY/discovery, r7 analysis provenance/registry evidence, r9 discrete SUMMARY, pi-analysis-r1 progress and relevant cached catalogue entries. Targeted repository searches found no mathematical prior lane on2605.22160/Problem5.2, only the broad cached catalogue entries for its already-proved neighboring conjectures. No claim to have body-read every historical lane is made. All expressly forbidden families were screened out; Tao's public resolution was not retried.

## Runnable verification and disposition

Run `python check.py` from this directory. It enforces a 512MiB address-space ceiling, 20CPU seconds and BLAS/OMP thread count1. It uses integer arithmetic and bitsets only, checks all262144 triples of the64-element unital U_2 for associativity and both distributive laws, verifies exact strongly regular pair-intersection identities at m=2,3,4, reconstructs all second neighborhoods for m=2,3 and both fiber sizes, checks exact spectral multiplicities/first two moments, and verifies the256-element ring's center directly. All checks pass; these finite checks do not replace the all-m derivation or prove the all-ring classification.

A source-text extraction initially failed because bs4 was absent; this failure is retained, and extraction was replaced by stdlib tag stripping with no package installation. No mathematical or resource-limit failure was suppressed; no cap was raised. Source HTML remains authoritative for notation.

No full source-level proof/refutation, novelty clearance, acceptance, Lean endpoint, or count is claimed. All writes stayed in the assigned lane. No children, git, shared edits, browser tabs, external messages, posting, uploading, contact or account changes.
