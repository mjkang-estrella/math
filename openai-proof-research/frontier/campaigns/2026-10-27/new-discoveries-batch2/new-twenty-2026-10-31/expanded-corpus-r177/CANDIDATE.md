# Candidate audit — no qualifying discovery claimed

**Final update:** 357873 is already refuted in Roy–Saha, arXiv:2506.01810v1, Theorem 2.7 (2025). The primary theorem and its proof were read. The order-free assertion is also false, contrary to the provisional interpretation in the diagnostic discussion below. The lane’s additional eight-vertex square obstruction is not discovery credit for an already settled target. No strong lead survives.


## 359474: ordinary full-scope proof; high, likely disqualifying credit risk

Target: Brimkov–Brimkov, arXiv:2308.06670v1, Conjecture 1. The source class excludes the disjoint union of the two cliques. Its degrees are **m vertices of degree m−1 and n vertices of degree n−1**. The MathDB notation must not be read as m−1 vertices of degree m. The following proof concerns the source class, not the disconnected-clique paraphrase.

Verdict: a complete ordinary argument below, **not a Lean-certified campaign result**. It is a short classical closure argument plus the source's Proposition 5. Under the brief's exclusion of short new observations on available machinery and source-ingredient bridges, it should not be counted. No independent review or root acceptance has occurred. No strong, credit-worthy lead is asserted and no dummy Lean endpoint is supplied.

### Proof

For a graph of order N, adding an edge between nonadjacent vertices of degree sum at least N−1 preserves traceability. This is the path version of Bondy–Chvátal closure. To see it directly, adjoin a universal vertex, reducing traceability to Hamiltonicity. The endpoints then have degree sum at least N+1 in a graph of order N+1. If a Hamilton cycle after the edge addition uses the new edge, remove it to obtain a spanning path with those endpoints. The two sets of possible endpoint-neighbor indices on that path have total size at least N+1 inside N possible indices, so overlap, and the usual reversal produces a cycle without the new edge. Deleting the universal vertex gives the claimed path lemma. Repeating permissible additions preserves traceability.

The equal-size case m=n is source Proposition 5 (Hamiltonicity). Assume n>m, and partition the original vertices into L of size m and H of size n according to their degrees m−1 and n−1. Cases with m=1 cannot belong to the connected source class. Put N=m+n.

First complete H to a clique: each missing pair in H has degree sum at least 2n−2≥N−1. Let S⊆H be the vertices which originally have a neighbor in L, let s=|S|, and let T=H\S. The source class is connected (source Proposition 2), so s>0. After H is completed, each h∈S has degree at least n, and each v∈L still has degree at least m−1. Consequently add every missing S–L edge.

If T is empty, H is now complete to L. Suppose T is nonempty. For v∈L let r_v be its original number of neighbors in H. Then r_v≤s, and its current degree is m−1+s−r_v. Every vertex of T originally had no neighbor in L; since its original degree was n−1, it originally had all other vertices of H as neighbors. Hence each h∈S originally had at least n−s neighbors in T. If r_h is its original number of neighbors in L, the original degree bound gives r_h≤s−1. Thus

    Σ(v∈L) r_v = Σ(h∈S) r_h ≤ s(s−1).

There is a v∈L with r_v<s: if s≥m, use r_v≤m−1<s for every v; if s<m, use s(s−1)<ms and the displayed count. This v has current degree at least m. Every t∈T has degree at least n−1, so add all missing v–T edges. Now every t∈T has degree at least n, allowing all its missing edges to L to be added, using the lower bound m−1 on low-vertex degrees.

We have made H complete to L. All low vertices have degree at least n, so any remaining missing pair in L has degree sum at least 2n≥N−1. Complete L. The final graph is complete and traceable, so the original graph is traceable by repeated application of the closure lemma. This proves the source conjecture. □

### Evidence and remaining gates

The finite independent Hamilton-path dynamic program checked all labeled realizations for (m,n)=(2,3),(2,4),(3,4),(3,5),(3,6),(4,4), excluding the disconnected cliques. It additionally checked a prefix of 70,520 labeled realizations for (4,5); that prefix is not exhaustive. See outputs/traceability.json. These checks support implementation fidelity, not the general proof.

Required for a future formal result: formal trace-closure lemma, all degree/counting arguments, source equal-size case or an independent formal substitute, literal universal source statement, and strict Lean replay/axiom audit. Those are deliberately not represented as completed. Given the likely routine-bridge exclusion, expensive Lean work is not justified here.

## 357873: order-specific diagnostic; do not credit

For the labeled graph with matching x_i y_i (i=1,2,3) and extra edges x1 x2, x2 x3, x1 y3, the computed second homological shift of the square of the cover ideal has three degree-eight generators, in descending order x3>y3>x2>y2>x1>y1:

    A = x3² y3 x2² y2 x1²
    B = x3 y3² x2² x1² y1
    C = x3 y3 x2² y2 x1² y1.

The second colon is (A):B=(x3 y2), not generated by variables. This computation uses a linear-quotient presentation of the square; the colon-variable subsets give the shift multidegrees by its minimal mapping-cone resolution. It has not been kernel-formalized. All detailed generators/colon supports are in outputs/cover-detail-3-21-2-2.json.

This graph is bipartite. The source claimed a positive result for bipartite graphs, but Roy–Saha disproves that general claim; the eight-labeling calculation here concerns only this particular square. Four of its eight admissible labelings pass all computed shifts of the square; four fail. Moreover, a separate order-specific exponent-one failure conflicts with the source's own Theorem 4.1. The published version retains the same stated order, and the author's thesis explicitly separates a weaker order-free conjecture and uses another order for whisker graphs. These are substantial reasons to treat this as an ordering/theorem-correction diagnostic, not a new substantive resolution. The lane’s six-vertex calculation alone does not refute the order-free conjecture; Roy–Saha’s already published construction does. See outputs/cover-relabel.json and sources/ficarra-thesis.txt, Theorem 9.3.8.

## Other sustained route: 358940

Exhaustive pinnacle-set coefficient counts through n=12 extend the source's n≤10 range with no negative gamma coefficient. The completed n=13 extension is recorded in outputs/pinnacle13.json. No proof or counterexample follows from these bounded checks.
