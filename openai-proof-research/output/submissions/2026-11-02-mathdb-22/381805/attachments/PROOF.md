DRAFT. Ordinary proof and formal correspondence; zero accepted credit.

# Exact super edge-magic total strength of a seven-cycle with four leaves at one vertex

## Abstract
Let H be the graph obtained from C7 by adjoining four pendant vertices to one cycle vertex. We give a super edge-magic total labeling with constant 26 and prove, by a degree rearrangement bound, that every such labeling has constant at least 26. Thus sm(H) = 26. On the nonnegative pendant-count domain of Deepthi's conjecture, this contradicts the predicted value 27. The accompanying literal Lean module proves the refutation by establishing sm(H) ≤ 26 < 27; the exact lower bound is an ordinary mathematical proof, not a claimed Lean theorem. This draft makes no priority claim. Several closely related older original bodies remain unread.

## 1. Definitions and the source assertion
All graphs here are finite, simple and undirected. For a graph G with p vertices and q edges, a super edge-magic total labeling is a bijection f from the disjoint union of vertices and edges onto {1,...,p+q}, such that f(V(G)) = {1,...,p} and there is an integer c with f(u)+f(uv)+f(v)=c for every edge uv. The number c is its magic constant. For a graph admitting at least one such labeling, its super edge-magic total strength sm(G) is the minimum of these constants over all such labelings.

For odd n ≥ 3 and integers k1,...,kn ≥ 0, write G(n;k1,...,kn) for a cycle a1,...,an in that order with exactly ki new degree-one vertices attached to ai, and no further vertices or edges. Then p=q=n+Σki. Deepthi's arXiv:2212.05329v1, Conjecture 1.6 [1], retained as Conjecture 1 of the 2024 journal article [2, p.75], asserts the following: for every such super edge-magic total graph, sm(G(n;k1,...,kn)) = 2q+(n+3)/2.

## Domain and status
Neither version imposes ki ≥ 1 in the conjecture. The nonnegative interpretation is supported by the graph construction and by Section 3, which allows a deficit k-c=0 when c=k. The source does not explicitly discuss every pattern of multiple zero counts; nonnegativity is the supported interpretation, not a quotation. Our example has six zero counts. It does not refute an alternative assertion restricted to all-positive counts.

This is an AI-assisted research draft prepared with OpenAI Codex; no human authorship or affiliation is asserted. It is unpublished, assigns zero accepted campaign credit, and leaves 9/20 beyond the earlier 39 unchanged. Root alone accepts. The mathematical statement, formal endpoint and bibliographic limits are distinguished throughout.

# 2. A complete labeling certificate

## The graph
Use vertices v0,...,v10. The cycle edges are v0v1, v1v2, v2v3, v3v4, v4v5, v5v6, v6v0. The remaining edges are v6v7, v6v8, v6v9, v6v10. Hence H = G(7;0,0,0,0,0,0,4), with p=q=11. Its degree multiset is {6,2,2,2,2,2,2,1,1,1,1}. In particular there are no isolated vertices or extra components.

## Vertex labels
In vertex order v0,...,v10, set f = (3,2,4,5,8,6,1,7,9,10,11). These are exactly the integers 1 through 11. Define each edge label by f(uv)=26-f(u)-f(v). The following table checks every edge equation.

Edge | Endpoint sum | Edge label | Total
v0v1 | 5 | 21 | 26
v1v2 | 6 | 20 | 26
v2v3 | 9 | 17 | 26
v3v4 | 13 | 13 | 26
v4v5 | 14 | 12 | 26
v5v6 | 7 | 19 | 26
v6v0 | 4 | 22 | 26
v6v7 | 8 | 18 | 26
v6v8 | 10 | 16 | 26
v6v9 | 11 | 15 | 26
v6v10 | 12 | 14 | 26

## Proposition 1
The displayed labeling is super edge-magic total with magic constant 26. Indeed, the endpoint sums in the table are exactly {4,...,14}, each once. Subtraction from 26 gives exactly {12,...,22}, each once, so these edge labels are distinct and disjoint from the vertex labels. Together they give a bijection onto {1,...,22}, and every total equals 26 by construction. Therefore sm(H) ≤ 26.

## Comparison with the conjecture
For n=7 and q=11 the asserted value is 2·11+(7+3)/2=27. Proposition 1 already refutes that equality: an admissible constant 26 forces the minimum to be at most 26. One need not optimize the witness to refute the conjecture. The next section proves that this particular upper bound is also the exact minimum.

# 3. Exactness and the older bounds

## Lemma 2 (degree rearrangement)
Let d1 ≥ ... ≥ dp be a graph's degrees. Among all permutations of the vertex labels 1,...,p, the degree-weighted sum is at least Σi di·i. To prove this, if positions i<j have labels x>y, exchange them. The old weighted sum minus the new one is (di-dj)(x-y) ≥ 0. Repeatedly removing inversions produces the increasing labeling without increasing the sum. Equal degrees do not affect the argument.

## Theorem 3
The super edge-magic total strength of H is exactly 26. Proof. Let f be any super edge-magic total labeling of H, of constant c. Its vertex labels are 1,...,11. By Lemma 2 and the displayed degree sequence, Σv deg(v)f(v) ≥ 6·1+2(2+3+4+5+6+7)+(8+9+10+11)=98. Its edge labels are necessarily 12,...,22, so their sum is 11(12+22)/2=187. Summing the eleven edge equations counts each vertex label once per incident edge. Consequently 11c = Σv deg(v)f(v)+Σe f(e) ≥ 98+187=285. Since c is an integer, c ≥ ceil(285/11)=26. Proposition 1 supplies the reverse inequality, proving sm(H)=26.

## Relation to Swaminathan and Jeyanthi
The lower-bound method is not claimed to be new. Deepthi [2, p.75, Theorem 2] reproduces Swaminathan and Jeyanthi [3, Theorem 4]: for n=2s+1, the lower bound is 2q+2+(m2+2m3+...+(n-1)mn+n(n-1)/2)/q, with the leaf counts sorted m1 ≥ ... ≥ mn. For H the sorted counts are (4,0,0,0,0,0,0), so this is 24+21/11=285/11. Their reproduced upper bound is 2(k1+k3+...+k7)+3(k2+k4+k6)+2n+s+2. Here the four leaves occur at odd index 7 and s=3, giving 8+14+3+2=27. Thus the known reproduced bounds already give 26 ≤ sm(H) ≤ 27. Our certificate attains their rounded lower bound.

## What is and is not subsumed
The uniform-count corollary reproduced immediately afterwards does not apply. Deepthi's concentrated-excess result is journal Theorem 3 (arXiv Theorem 2.1). It requires c < 2n(k+1)/(n-3). At n=7,k=0,c=4 this would require 4<3.5, which fails. The uniform, deficit and two-excess cases do not cover this graph. This example therefore does not contradict a proved theorem in the target article.

## Scope
The conclusion resolves the stated universal formula on its nonnegative-count domain. It supplies neither a replacement formula for the whole family nor a counterexample in the all-positive subfamily. Its mathematical depth is modest; the potentially new content is the upper bound 26 and its conflict with the published conjecture, subject to the bibliographic limitations on page 5.

# 4. Formal correspondence and replay boundary

## The literal module
The dossier includes proof/Magic.lean byte for byte from the frozen author lane, in namespace Magic381805. Its terminal theorem is source_refutation : ¬SourceConjecture. It uses actual unordered edges of a SimpleGraph, not a freely specified list of edge equations. Fin labels are stored starting at zero; adding one gives the paper's labels. The table below describes the semantic bridges.

Lean declaration | Mathematical role
IsSuperEdgeMagic | Equivalence on vertices disjoint-union edges to Fin(p+q); vertex range and all edge totals
IsFamily; family | Injective cycle, no chords, exact pendant fibers; this H belongs
vertex_count; edge_count | Both cardinalities equal 11
raw_bounds; labeling_bijective | Labels in range; actual total bijection
labelEquiv; certificate | Witness labeling satisfies constant 26
strength; strength_le | Nat.sInf over all realized constants; sm(H) ≤ 26
SourceConjecture | Universal equality for odd n ≥ 3, nonnegative k, admitting a labeling
wrong_predicted_value; source_refutation | 26 < 27 contradicts the proposed equality

## Formal endpoint versus ordinary proof
IsFamily requires exactly cyclic adjacency between cycle vertices, requires every outside vertex to be a leaf at one cycle vertex, and counts every leaf fiber. This excludes chords and extra components. SourceConjecture quantifies over graphs on Fin N, which suffices for this explicit finite counterexample. The existence hypothesis and explicit certificate make the empty-set convention of Nat.sInf irrelevant. strength_le uses Nat.sInf_le on the actual labeling witness. The transitive endpoint includes all these bridges. The module does not prove the lower bound of Theorem 3: exact strength 26 is established here in ordinary mathematics only.

## Reproducibility and trust
Replay pins Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. It refuses existing oleans, builds with -j1 -DwarningAsError=true, runs leanchecker and audits all 37 Magic-origin declarations, including generated declarations and instances. The only allowed transitive axioms are propext, Classical.choice and Quot.sound. Reviewer supplements are separately named. Imported cached dependency oleans are trusted; neither a full upstream rebuild nor an independent kernel implementation is claimed.

## Diagnostics are separate
The independent review enumerated 831,600 cycle assignments modulo reversal and interchangeable leaves, finding 178 consecutive-sum assignments and minimum starting sum 4. This is corroboration, not the Lean lower-bound proof. Its all-positive concentrated-excess MILPs found no counterexample: three were reported infeasible and three timed out. Floating-point solver outcomes are not certified impossibility results. No all-positive theorem follows.

# 5. Related work, limitations and references

## Related work
Figueroa-Centeno, Ichishima and Muntaner-Batle [4] give the consecutive endpoint-sum characterization, reproduced in Deepthi as Lemma 1 (arXiv Lemma 1.1): a bijective vertex labeling extends precisely when the q endpoint sums are consecutive. For starting sum t the total is p+q+t. The table on page 2 verifies the extension directly. Their original 2001 body was not obtained; the attribution and statement here rely on the reproduction. Their 2002 Magical coronations of graphs was read in review; no construction giving this graph at constant 26 was identified.

Avadayappan, Jeyanthi and Vasuki's 2000 and 2001 articles [5,6] are important antecedents for strength invariants. Their originals remain unread; survey reports of formulas for other families do not clear all of their constructions. Akka and Warad [7] is a distinct 2010 paper, not a reissue of [6]. Its convention puts edges in 1,...,q. Shifting vertices by +q and edges by -p transforms our convention to theirs, increasing constants by 2q-p; a matching formula would therefore be relevant. No matching case was found in the read body.

Kim [8, Theorem 2.3 and Corollaries 2.7-2.8] constructs leaf extensions. The reviewed constructions preserve c-2q; beginning with C7 at constant 19 and adding four leaves yields 27, not the smaller certificate here. Gallian [9], edition 28 dated 30 October 2025, was read at relevant sections and bibliography entries, not exhaustively. No explicit matching concentrated-leaf minimum was located. Neither a survey screen nor the source's continued conjecture proves priority.

## Unread original bodies and adjudication
The closest unread older bodies are Swaminathan-Jeyanthi 2006 [3] and its 2003 conference version; Avadayappan-Jeyanthi-Vasuki 2000 [5] and 2001 [6]; and Figueroa-Centeno-Ichishima-Muntaner-Batle 2001 [4]. Access attempts were restricted, denied, timed out or returned non-PDF content. Enomoto et al.'s foundational source also remained unread after an HTML challenge. Additional limits include a cactus-ring publisher body and an indexed Yang-Baxter citation not cleared in the original review. Receipts retain exact access evidence. Reviews kept novelty/significance on HOLD; root later issued a bounded QUALIFIED_PASS with residual risk disclosed. That ruling is preserved, not converted into original-body clearance. This manuscript makes no priority claim and awards no credit.

## References (original-body limits as above)
[1] N. S. Deepthi, Super edge-magic total strength of some unicyclic graphs, arXiv:2212.05329v1 (2022), Conj. 1.6. [2] Same title, Ars Combinatoria 159 (2024), 73-85, doi:10.61091/ars159-08, Conj. 1.

[3] V. Swaminathan and P. Jeyanthi, Super edge-magic strength of fire crackers, banana trees and unicyclic graphs, Discrete Mathematics 306 (2006), 1624-1636; doi:10.1016/j.disc.2005.06.038. [4] R. M. Figueroa-Centeno, R. Ichishima and F. A. Muntaner-Batle, The place of super edge-magic labelings among other classes of labelings, Discrete Mathematics 231 (2001), 153-168.

[5] S. Avadayappan, P. Jeyanthi and R. Vasuki, Magic strength of a graph (2000). [6] Same authors, Super magic strength of a graph (2001). [7] D. G. Akka and N. S. Warad, Super magic strength of a graph (2010), 557-568; doi:10.1007/s13226-010-0031-z. [8] Y.-H. Kim, On constructions of new super edge-magic graphs from some old ones by attaching some pendants (2017), Commun. Korean Math. Soc. 32, 225-231; doi:10.4134/CKMS.c160044. [9] J. A. Gallian, A Dynamic Survey of Graph Labeling, Electronic J. Combin., DS6, ed. 28 (2025).
