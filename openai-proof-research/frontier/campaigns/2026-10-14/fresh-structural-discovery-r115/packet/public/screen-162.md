# 162: balance does not permit regularity

This screen tried an extra regularity condition on the balanced intersecting examples, before freezing anything. The stipulated balanced source `thm:main` has r=q+1 parts with r nonisolated vertices per part and cover number r for sufficiently large primes q. In `prop:deterministic-reduction` and its affine-line construction, merged parallel lines, split two-point blocks, and ordinary line blocks have different sizes. The split blocks already show why equal part sizes do not mean equal vertex degrees. No flaw in the source is asserted.

The attempted regularization is excluded by a stronger existing elementary operation. Let H be a nonempty finite intersecting r-uniform r-partite hypergraph, r≥2, whose nonisolated vertices all have degree d≥1. If it has M edges, each nonisolated part has the same size s=M/d. Fix an edge e. Counting incidences of other edges with vertices of e gives

    M−1 ≤ Σ_(f≠e) |e∩f| = r(d−1).

Hence sd≤rd−r+1, and s≤r−(r−1)/d<r. Every part is a cover, so τ(H)≤s≤r−1. Thus no regular example under these hypotheses can have τ(H)=r.

This is the t=1 regular specialization of the incidence-degree mechanism in Bishnoi–Das–Morris–Szabó, [Ryser's Conjecture for t-intersecting hypergraphs, arXiv2001.04132v2](https://arxiv.org/pdf/2001.04132v2), Lemma3.3 and Corollary3.5. The operative inequalities and their proofs were read, including the regular/equality design discussion; an abstract was not treated as proof. This exclusion is classical feasibility, not a new campaign finding or nominee.

The separate original counterexample companion was acquired and identified but not fully read. The previous linear-Ryser trade investigation was consulted as an antecedent; regularity is a different additional condition, but that difference does not make its classical exclusion a research result. No alternative weaker regularity statement was substituted.
