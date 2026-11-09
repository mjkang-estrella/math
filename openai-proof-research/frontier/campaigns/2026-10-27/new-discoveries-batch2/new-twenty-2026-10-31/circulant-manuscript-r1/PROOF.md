# Ordinary proof and source correspondence

1. The question and its scope

Abstract. We give a finite, kernel-checked refutation of Conjecture 4.5 of Tuite, Thomas and Chandran. Every circulant graph on 15 vertices with diameter 2 has monophonic position number at least 3. Among its 128 possible undirected jump masks, 109 contain a triangle, 17 further masks fail the distance bound, and the remaining two describe the same C5 blow-up, whose independent fibers contain triples of twins. The exact monophonic position number of that familiar residual graph is 6. The accompanying Lean dossier proves the literal negation of the source conjecture; the finite computation is part of the proof.

All graphs here are finite, simple and undirected. A monophonic path is an induced path: a sequence of distinct vertices in which two vertices are adjacent exactly when their indices are consecutive. A monophonic position set (mp-set) contains no three distinct vertices on a common induced path. Its maximum cardinality is the monophonic position number mp(G). Equivalently, no member of the set lies internally on an induced path between two other members. Indeed, from three selected vertices on a common path, take the subpath from the first to the last. Conversely, a violation of the internal-vertex condition supplies three members on one induced path. This condition concerns all induced paths, of arbitrary length.

For J contained in {1,...,floor(n/2)}, write C_n(J) for the graph on Z/n with edges of differences plus or minus a member of J. This represents every circulant up to cyclic labelling. A general Cayley generating set gives the same simple undirected graph after symmetrization and removal of zero. The conjecture is existential in J for each order n; it does not assert the property for every J.

Source context [1]. Lemma 4.3 states: if a graph of order r >= 4 has mp-number 2 and diameter 2, then such graphs also exist at orders 3r, 3r+1 and 3r+2. Theorem 4.4 states that a graph of order n with mp-number 2 and diameter 2 exists if and only if n is in {3,4,5,8} or n >= 11. Its proof uses computer search for n <= 32 and then Lemma 4.3 inductively. These statements concern unrestricted graphs. The search is credited to Erskine by personal communication; the underlying data are not printed.

Conjecture 4.5 [1] strengthens the large-order assertion: for every n >= 11, there exists a circulant graph of order n with diameter 2 and mp-number 2. The survey [3], cached v5 dated 16 August 2026, repeats it in Section 4.1 and asks for its proof in the open-problem list. We refute precisely this assertion at the interior order 15. Theorem 4.4 and its unrestricted construction are unaffected.

2. Two obstructions and the finite classification

Lemma 1 (triangles). The vertices of a triangle form an mp-set. Proof. If three pairwise adjacent vertices lay on an induced path, their three distinct indices would have to be pairwise consecutive. Three distinct integers cannot have this property. Thus mp(G) >= 3 whenever G contains a triangle.

Lemma 2 (open twins). Three distinct vertices a, b, c with N(a) = N(b) = N(c) form an mp-set. Proof. Equality of open neighborhoods implies that these vertices are pairwise nonadjacent: adjacency of a and b would put b in its own neighborhood. If an induced path contained all three, it would have positive length, and a would have a neighbor q on that path. Equality of neighborhoods makes q adjacent to b and c as well. It is different from all three. The induced subgraph of a path has degree at most 2, whereas q would have three distinct neighbors. This is impossible.

Classification lemma. A triangle-free circulant on 15 vertices for which every vertex is at distance at most 2 from zero has positive jumps {1,4,6} or {2,3,7}. Here is the complete finite certificate, together with its elementary decision rule. Encode J by m = sum of 2^(d-1) over d in J, so 0 <= m < 128. Put S = J union (-J) in Z/15. A triangle through zero exists exactly when a,b are in S and b-a is in S. By translation, absence of such a triangle is triangle-freeness of the whole graph. Two-step reachability from zero is exactly {0} union S union (S+S).

The following table lists every mask passing the triangle test. The second row supplies a vertex outside {0} union S union (S+S), or a dash when there is none. The other 109 masks fail the triangle test. Each entry can be checked with residues 0 through 14; no graph-isomorphism algorithm or numerical tolerance enters.

Masks: 0 1 2 4 5 6 8 9 12 32 33 34 40 41 64 66 68 70 96
Missing: 1 3 1 1 5 7 1 6 2 1 4 1 1 - 2 3 2 - 4

For completeness, the exhaustive rule is: for m = 0,...,127 form S; if some a,b in S have b-a in S, record triangle; otherwise test each x = 0,...,14 for x in {0} union S union (S+S). The table gives all 19 masks surviving the first test; exactly 17 fail the second. Lean's theorem classify proves the universal implication over Fin 128 by decidable reduction in the kernel. The independent Python certificate uses the displayed modular rule. The human-readable table and executable rule specify the entire finite calculation, rather than an unexplained search for examples.

The survivors have masks 41 = 1+8+32 and 70 = 2+4+64. Multiplication by 2 modulo 15 sends the signed jumps of {1,4,6} to those of {2,3,7}; it is a graph isomorphism.

3. Refutation and the residual structure

Theorem. For every circulant G of order 15 with diameter 2, mp(G) >= 3. In particular, Conjecture 4.5 of [1] is false.

Proof. If G has a triangle, apply Lemma 1. Otherwise label its vertices by Z/15 and let J be its positive jumps. Diameter 2 implies that every vertex is reachable from zero in at most two steps, so the classification lemma gives J = {1,4,6} or J = {2,3,7}. In the first case the full signed jump set is the six residues congruent to plus or minus 1 modulo 5; in the second it is the six residues congruent to plus or minus 2 modulo 5. Consequently 0, 5 and 10 have identical open neighborhoods. Lemma 2 gives a three-element mp-set. Hence no jump set at n = 15 can satisfy both diameter 2 and mp-number 2. Since 15 >= 11, the universal existential statement in the conjecture is false.

The five cosets of {0,5,10} are independent fibers of size 3. Between two fibers all edges or no edges occur, and the quotient is C5 (with quotient step 1 or step 2). Thus each residual graph is the lexicographic product C5[3K1]. It has diameter 2: adjacent quotient fibers are joined completely, two nonadjacent quotient fibers have an intermediate fiber, and two vertices in one fiber have a common neighbor.

Remark (known exact value). In fact mp(C5[3K1]) = 6. For a direct check, any three distinct vertices of C5 lie on an induced path: delete a suitable one of the two unselected cycle vertices, leaving an induced four-vertex path. Prescribed members of three distinct fibers can therefore be lifted onto an induced path, so an mp-set meets at most two fibers and has size at most 6. For the lower bound take all vertices of two nonadjacent fibers. If an induced path contains two vertices from one fiber, their identical neighborhoods force them to be the two ends of a path of length 2: any extension creates a chord. Such a path cannot also meet the chosen nonadjacent fiber. Therefore no three members of this six-element set lie on an induced path.

This exact value receives no separate novelty claim. The lexicographic-product formula in [4, Theorem 4.4] already gives it. For a connected base G of order at least 2 that formula maximizes n_M omega(H) + r_M mp(H) over mp-sets M of G, where r_M counts isolated vertices of G[M] and n_M counts vertices in its nontrivial components. For H = 3K1, omega(H) = 1 and mp(H) = 3. A nonadjacent pair in C5 contributes 6; every base mp-set has at most two vertices. The formula thus gives the same value.

Coverage and corrected question. The review dossier verifies explicit circulant witnesses at every order 11 through 40 except 15. Each witness has two-step reachability, a missing edge, and induced paths containing every triple of vertices; hence diameter is exactly 2 and mp-number is exactly 2 (any pair is an mp-set). At 15 the exclusion is exhaustive over all masks. Positive witnesses at the other orders do not classify all masks. Does such a circulant exist for every n >= 11 with n != 15? This natural corrected question remains OPEN here. No assertion is made above order 40.

4. Formal statement correspondence and replay

The namespace below is Circulant350979; module names are Circulant, Bridge and Endpoint. The four supplied modules, including Audit, are byte-identical to expanded-corpus-r108. AuditFull is a new full declaration audit adapted from the independent review. The correspondence is as follows.

Mathlib's circulantGraph J is fromRel of the difference relation. It symmetrizes that relation and removes loops; arbitrary asymmetric J and J containing zero introduce no extra graphs. Bridge.represent therefore covers every circulant at order 15. Fin 15 and ZMod 15 use the compatible finite residue representation in this development.

Mathlib defines the natural diameter of a disconnected graph as 0. The hypothesis diam = 2 excludes this case: radius_of_diam first proves the extended diameter is finite, then bounds distances. Thus neither disconnected graphs nor a diameter convention creates a spurious refutation. The source quantifier uses natural orders; under n >= 11 this agrees with integer orders.

The dossier pins Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. The replay driver accepts LEAN_BIN and LEAN_PACKAGES, rejects existing local oleans, verifies source hashes, and builds sequentially with -j1 and warningAsError. It then runs leanchecker with exactly one module per process. Each child has at most two CPUs, a 120-second CPU limit, a 140-second wall watchdog and a sampled aggregate RSS limit of 6 GiB; MALLOC_ARENA_MAX is 2.

AuditFull enumerates all 52 declarations originating in the three proof modules, including generated declarations, and prints their full types, bodies using value? (allowOpaque := true), safety flags and transitive axioms. It rejects local axioms, missing ordinary bodies, unsafe or partial declarations, and any axiom beyond propext, Classical.choice and Quot.sound. Two deliberately false Lean claims must be rejected: substituting mask 40 for 41, and denying triple-path coverage at the positive order-16 control.

Trust limits. Decidable finite reduction is kernel-checked; no native_decide, ofReduceBool, sorry, admit or added axiom is used. The Lean implementation, allowed logical axioms, operating system, binary and cached upstream mathlib oleans remain trusted. Mathlib is pinned but not rebuilt. Leanchecker rechecks exported environments using the same kernel implementation; it is not a second foundational implementation. RSS sampling does not certify every transient peak. The exact residual mp-number and coverage through 40 are supplementary ordinary/executable results, not additional theorems claimed by the source_refutation endpoint.

5. Related work, access limits and references

The monophonic-position precursor [2] develops the invariant and standard clique and structural bounds. Its Lemma 3.1 describes the induced structure of an mp-set as a disjoint union of cliques. These observations and the source's own blow-up arguments explain the residual obstruction; the additional finite step here excludes every other order-15 circulant. The product theorem [4] subsumes the exact residual value. No priority is claimed for that value, the twin mechanism, or the underlying graph.

The graph-likelihood paper [5, Section 6] explicitly uses the same 15-vertex circulant C5[3K1] in a different extremal problem. That graph is therefore familiar. A likelihood counterexample does not establish the universal exclusion for the monophonic-position conjecture; conversely, this manuscript makes no graph-likelihood claim.

Access and novelty limits. This draft reads the retained arXiv bodies selectively, concentrating on the definitions and relevant theorem sections. The journal version of [1] is reported as Ars Mathematica Contemporanea (2025), but its actual body was not read: the retained access receipt records HTTP 403. No access barrier was retried. The journal is not silently treated as equivalent to the read preprint. The independent review found no earlier exact refutation in its bounded searches and retained registry screens; it did not clear all citing literature or semantically inspect every public proof. Its qualified finding and the root's conditional eligibility ruling are included in the dossier. This manuscript asserts no worldwide priority and assigns zero campaign acceptance credit.

The following bibliography identifies the bodies actually used in this manuscript, rather than uninspected search snippets or the unread journal body. Retrieval receipts, original bodies and their hashes are retained under sources/. Version metadata are copied from those retained bodies and receipts; no new live literature survey was performed for this packaging task.

[1] James Tuite, Elias John Thomas and Ullas Chandran S. V. On some extremal position problems for graphs. arXiv:2106.06827v3, 8 February 2022. Read: definitions, Lemma 4.3, Theorem 4.4 and Conjecture 4.5. https://arxiv.org/abs/2106.06827v3 . Journal body (Ars Mathematica Contemporanea, 2025) unread; 403 receipt retained.

[2] Elias John Thomas, Ullas Chandran S. V., James Tuite and Gabriele Di Stefano. On monophonic position sets in graphs. arXiv:2012.10330, retained HTML body. Read: definitions and Lemma 3.1 with its proof. https://arxiv.org/abs/2012.10330 .

[3] Ullas Chandran S. V., Sandi Klavzar and James Tuite. The General Position Problem: A Survey. arXiv:2501.19385v5, 16 August 2026. Read: Section 4.1 and the relevant Section 6 open problem. https://arxiv.org/abs/2501.19385v5 .

[4] Ullas Chandran S. V., Sandi Klavzar, Neethu P. K. and James Tuite. Monophonic position sets of Cartesian and lexicographic products of graphs. arXiv:2412.09837v3 (version header: 17 November 2025; body dateline: 24 August 2026). Read: Section 4, especially Theorem 4.4 and its proof. https://arxiv.org/abs/2412.09837v3 .

[5] Simone Severini and Eric W. Weisstein. The minimum of the graph likelihood. arXiv:2608.19467v2, 29 October 2026. Read selectively: Section 6 and the C5 blow-up description. https://arxiv.org/abs/2608.19467v2 .
