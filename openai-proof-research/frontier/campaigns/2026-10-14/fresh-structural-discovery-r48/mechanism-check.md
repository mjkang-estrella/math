# Ternary-grid embedding interface: exact progress and limits

Author-side work in r48, with the parent's all-order moment calculation explicitly credited below. No independent review or full Ramsey proof is claimed. The pinned upstream theorem is stipulated, not audited.

## 1. The question and the paid containment bound

Write T_d=P_3^{\square d}, with vertices {0,1,2}^d and adjacency when precisely one coordinate changes by one. The provisional question is whether an absolute C satisfies R(T_d,T_d)≤C3^d for every integer d≥0, for arbitrary two-edge-colorings of complete graphs and ordinary, not induced, copies. No target was frozen: the operative-source comparison did not yield a credible complete construction. No restricted substitute is nominated.

The source171 theorem R(Q_n,Q_n)≤C_0 2^n gives R(T_d,T_d)≤C_0 4^d. Indeed P_3 is a subgraph of Q_2 and Cartesian products preserve subgraph embeddings. This particular containment is dimension-optimal: the all-middle vertex of T_d has degree 2d, whereas Q_m has maximum degree m, so T_d⊂Q_m requires m≥2d. Consequently the source's constant-density cube-subgraph corollary cannot directly give the proposed linear bound; its density cost is (4/3)^d. This is a limitation of that containment operation, not a Ramsey lower bound.

## 2. Exact layer and moment profiles

For v let k(v) be its number of coordinates equal to 1. The layer k has a_k=binom(d,k)2^{d−k} vertices. Each middle coordinate supplies two neighbors in layer k−1, and each endpoint coordinate supplies one neighbor in layer k+1. Thus deg(v)=d+k(v). Ordering layers by decreasing k gives exactly b(v)=d−k(v) earlier neighbors. There are no edges within a layer. Since every vertex has degree at least d, this ordering also proves degeneracy exactly d for d≥1.

The graph has 3^d vertices and 2d3^{d−1} edges for d≥1. Any two distinct vertices have at most two common neighbors: a common neighbor makes their graph distance two; if they differ in one coordinate, they must be the two endpoints and have one middle common neighbor; if they differ in two coordinates, the two orders of the unit moves give exactly two common neighbors. These exhaust the possibilities.

For every real p≥0 the binomial theorem gives

    Σ_v 2^{p deg(v)} = 2^{pd} Σ_k binom(d,k)2^{d−k}2^{pk}
                     = (2^{p+1}+2^{2p})^d,
    Σ_v 2^{p b(v)}   = Σ_k binom(d,k)2^{(p+1)(d−k)}
                     = (1+2^{p+1})^d.

The parent supplied the useful all-order comparison (the elementary layer counts and first moment had already been derived here). Relative to |T_d|^{p+1}, the full-degree moment bases at p=1,2,3,4 are respectively 8/9, 24/27, 80/81, and 288/243. The fourth already grows exponentially. Thus first-moment slack 8^d/9^d cannot justify the high even moments required by the source peeling estimates.

For every real p≥1, 1+2^{p+1}<3^{p+1}. For a direct proof set q=p+1≥2; the function 3^q−2^q increases for q≥2 because its derivative 3^q log3−2^q log2 is positive, and at q=2 its value is 5>1. Every fixed-order backward-degree moment therefore has exponential slack. At host size N=C_d3^d, the maximum backward flat inverse-neighborhood ratio is 2^d/N=(2/3)^d/C_d; the maximum full-degree ratio is 4^d/N. These are numerical budgets, not conditional embedding estimates.

## 3. A bounded-fiber rainbow extraction shortcut fails exactly

One tempting black-box strategy is to amplify a host of order 3^d into one of order 4^d, apply the source cube theorem, and extract a copy of T_d that uses distinct original host labels. Bounded multiplicities of labels in a cube do not suffice, even if adjacent vertices always have distinct labels.

For each d≥3 put m=ceil(log_2(3^d))−1=floor(log_2(3^d)). Label x∈{0,1}^{2d} by

    c(x)=(x_1,...,x_m, x_{m+1}+...+x_{2d} mod 2).

This is a proper vertex coloring: an edge changes either one displayed bit or the parity bit. There are exactly 2^{m+1} labels, strictly between 3^d and 2·3^d, each occurring exactly 2^{2d−m−1} times. Its multiplicity is at most (4/3)^d, since 2^{m+1}≥3^d.

At every vertex the first m coordinate flips have m distinct neighbor labels; all remaining coordinate flips share one further label. Thus only m+1 distinct neighbor labels occur. For d≥3, 3^d<2^{2d−1}: this holds at d=3 (27<32) and persists by multiplying the left side by 3 and the right by 4. Hence m+1≤2d−1<2d. An embedded T_d in Q_{2d} must use every one of the 2d neighbors of its center. At least two of their labels agree. No copy is rainbow.

Equivalently, the label quotient is Q_{m+1}; a bounded-multiplicity homomorphic cube image can lose the center's required degree. This refutes only the stated extraction premise. It does not construct a two-edge-coloring without T_d, does not rule out other amplification schemes, and does not refute R(T_d)=O(3^d).

## 4. What the pinned proof actually needs

Source171 introduction, regime guide and reduction/notation were read in full. Its contradiction setup excludes monochromatic Q_n with side size N and N/2^n tending to infinity (and the stated auxiliary upper normalization). Density-increment, patch and clustered alternatives are eliminated by cube embeddings before deep discrepancy is established. Absence of T_d at N≈3^d does not supply this premise: a cube of dimension around log_2(3^d) has maximum degree less than 2d. Absence of T_d does imply absence of Q_{2d}, but then N/2^{2d}≈(3/4)^d, outside the needed large-ratio regime. The proof's discrepancy input therefore cannot simply be reused with an effective dimension.

The homogeneous-peeling lemma in source Section12 lines119–146 is also specific about its probability contract: one common law π, exclusion of a large clique with K_π>3θ, and a uniform bound on τ(x)D_π(x)^{−r} exp(CQ). Its deletion step pays inverse common-neighborhood degrees for the number r of constraints. Conditioning does not turn heterogeneous neighborhoods into samples from a common law; the text explicitly warns of this. The first moment in Section2 above is not a replacement for this uniform or conditional estimate.

A genuinely unpaid route would need (i) a replacement for the cube-specific alternatives establishing an adequate host structure for T_d, and (ii) a sequential sampler embedding layers in decreasing k while controlling the inverse common-neighborhood moments and marginal loads under every inherited exposure. The all-order backward profiles would then be relevant. Neither component has been proved here. Bounded codegrees alone do not establish either one.

## 5. Closest actual primary operations

Lee, *Ramsey numbers of degenerate graphs* (Annals185,2017), Definition2.1, Lemma2.2 and Theorem2.3: the proof prepares one set using dependent random choice, injects one complete bipartition there, bounds total neighborhood defect, and orders the other side by defect so that its common-neighborhood sizes permit greedy injection. The inspected degree-dependent host requirement uses α^{−Δ}; applying Δ=2d in density1/2 does not give a linear-in-3^d host. The separately inspected degeneracy theorem has parameter-dependent constants and thresholds, not a uniform constant for this growing d. Nothing in those read passages supplies the sequential conditional contract above. Source: https://annals.math.princeton.edu/wp-content/uploads/annals-v185-n3-p02-p.pdf .

Tikhomirov, *A remark on the Ramsey number of the hypercube*, arXiv2208.14568v3: the full inspected Lemma5.5 proof partitions one cube bipartition into facets, samples distinct host blocks, and samples injectively inside each block. Each opposite vertex has n−w neighbors in one block and w in distinct other blocks; a bad-tuple bound and union bound leave at least 2^{n−1} candidates for every opposite vertex. Proposition6.3's inspected proof obtains dispersed neighborhoods, a density increase, or almost-complete blocks by iterative removal. This supplies real structural alternatives but not a ternary sequential sampler; replacing its full-neighborhood constraint count by backward degree changes the exposure mechanism. Source: https://arxiv.org/pdf/2208.14568v3 .

Mota–Sárközy–Schacht–Taraz, *Ramsey numbers for bipartite graphs with small bandwidth*: the inspected Theorem1.2 fixes maximum degree Δ before its bandwidth and size thresholds; the inspected embedding lemma chooses regularity tolerance depending on Δ. Its near-linear result for fixed-dimensional grids is not a uniform theorem for T_d with Δ=2d tending to infinity. The comparison is about those explicit parameter dependencies, not an assertion that every possible use of regularity fails. Source: https://www.math.uni-hamburg.de/home/schacht/2015/Ramsey_grid.pdf .

## 6. Disposition and verification scope

No theorem beyond the elementary statements above is claimed; no target has been frozen or nominated. The original provisional full two-color, all-d question remains unresolved. The finite diagnostic checks small layer counts, integer moments, codegrees, and the explicit coloring. These are checks of examples, not substitutes for the general proofs. A feasible formalization would cover finite-product degree counts, binomial sums, the degree obstruction, and the displayed bit-label coloring. No full Ramsey construction or Lean certificate exists in this packet.
