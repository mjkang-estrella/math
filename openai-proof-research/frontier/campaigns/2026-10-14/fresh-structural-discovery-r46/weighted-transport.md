# Family183: bounded fractional transport is not yet a new mechanism

This is a pre-freeze screen, not a theorem about weighted-level complexity. The ordinary all-ranks and k-sensitive conclusions are already source-paid. Arbitrary real positive weights in [1,C], with C fixed, were considered because rational cloning has denominator-dependent size. No exponent or complexity claim for them is proved here.

## A finite transport lemma that does extend

Assume the same generic-position conditions as source183. Let a straight-line dual sweep have fixed vertex capacities w_p∈[1,C]. At each state let m_p∈[0,w_p] be the greedy allocation of a fixed total mass τ: fill vertices in sweep order, with at most one partially filled vertex. Suppose consecutive endpoint batches have mass distance A_i=½Σ_p|m_p(i+1)−m_p(i)|∈[a,a+C], for a>0. Define losses l_p=(m_p(i)−m_p(i+1))_+ and gains g_q=(m_q(i+1)−m_q(i))_+. They have common total A_i. Give the geometric edge pq weight

    z_pq = a l_p g_q / A_i.

Its total weight in batch i is a A_i; each edge weight is at most C², because a≤A_i and l_p,g_q≤C. Each loss vertex precedes each gain vertex in initial sweep order and follows it in final order. Indeed initially a loss has positive allocation and a gain is not full; finally a gain has positive allocation and a loss is not full. Two distinct vertices cannot both be the sole partial vertex. Thus their order reverses strictly. Each edge points right in the dual point plane, and its slope belongs to the batch interval, exactly as in the ordinary source construction. A pair cannot recur in distinct step-disjoint batches because two affine projection functions cross at most once.

At vertex p the outgoing edge mass is a l_p, the incoming mass a g_p. Put token mass a m_p at each vertex in each endpoint state, transport the stated edge masses, and keep the common mass a min(m_p(i),m_p(i+1)) in place. This is a finite acyclic time-expanded flow. Successively follow any positive initial flow to a final sink, subtract the minimum positive edge flow on that path, and repeat. Each iteration kills an edge, so finitely many weighted paths suffice even for irrational capacities. The total path weight is aτ. The nonconstant geometric pieces of each path have increasing x-coordinates and increasing slopes, hence form a convex chain. Applying the same construction to a(w_p−m_p) and reading rightward gives concave chains of total weight a(W−τ), W=Σw_p. Both chain families carry every geometric edge with total chain weight z_e. No integer matching or unbounded-denominator blowup is needed.

For a window with participating vertex set S, paths that ever move can be initialized only at vertices in S; the total weight of nontrivial chains is at most aΣ_{p∈S}w_p≤aC|S| for either family. The ordinary convex-versus-concave crossing argument therefore gives weighted proper-crossing mass at most 2a²C²|S|². Crossings are counted with product edge weights. This is finite flow decomposition plus bilinearity of the source's crossing count, not an additional substantial contribution.

The designated-endpoint crossing inequality also extends routinely to edge weights z_e≤B. Retain each edge independently with probability z_e/B. Apply the source inequality e³≤K m v cr+K v³ to every retained subgraph; Jensen and independence yield

    (Σ z_e)³ ≤ K B m v Σ_{e crosses f} z_e z_f + K B³ v³.

An unordered crossing convention changes only K. This is the standard random-thinning transfer.

## What is not proved

A bend can move arbitrarily little mass: for two crossing unit-capacity vertices and residual threshold ε∈(0,1), the allocation ε moves from one to the other. Thus bounding the number of bends by total transported mass is invalid. The plausible repair is the source's shifted-threshold activity argument: shift τ by Θ_C(b) to force Ω_C(b) endpoint mass from b distinct active vertices, allowing the two partial boundary vertices. This repair has not been fully written or checked here. Neither have the weighted limiting rank coordinates, differentiation, zoom, spatial, and boundary steps. The rank-limit section was read; the later sections were not. The complete weighted theorem remains unproved, not refuted.

## Primary boundary

Matoušek1991 constructs long monotone paths and reports a weighted-median assignment in its final paragraph, referring to Cole–Megiddo–Sharir and Yamamoto. Neither an explicit weight assignment nor bounded weight ratio is supplied in that paper. Agarwal–Desikan reports the resulting unrestricted-weight Ω(n^(5/3)) lower bound and an integer-weight upper bound depending on maximum and total weight. No bounded-[1,C] lower bound is inferred here. Dey and Eppstein's tight general-matroid bounds exclude a generic all-matroid power-saving transfer; they do not settle the proposed weighted quantile problem.

Disposition: no frozen target, no nomination. The concrete finite interface has a standard fractional-flow solution; no new nonroutine operation has been identified. Parent explicitly advised against spending a full proof on weighted bookkeeping alone. This is an author-side discovery decision, not an independent contribution verdict.
