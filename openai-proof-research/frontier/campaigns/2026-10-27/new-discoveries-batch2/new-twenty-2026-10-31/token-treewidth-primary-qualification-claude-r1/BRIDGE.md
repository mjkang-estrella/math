# BRIDGE.md: complete reduction of MathDB 362080 to a primary theorem actually read

Written after PROOF.md and after reading Hickingbotham and Wood. Reviewer-authored. Not independently reviewed. This is a routine-reduction
argument. It is not an authenticated earlier solution of the conjecture and it is not a novelty finding.

## Primary statements used (read in full, including the proof of Lemma 24)

Hickingbotham and Wood, Structural Properties of Graph Products, arXiv 2110.00721, ar5iv rendering, sha256 e00d616e...4abf. This is reference [14] of the source,
which uses it only for grids (source Theorem 10 = their Corollary 26).

- Lemma 24. For all eps, beta in [2/3,1) with beta > eps and integers k,n,m >= 1 with m >= kn and n >= 1/(1-beta), and for all connected graphs G and H with m and n
  vertices such that every beta-separation of G has order at least k, every eps-separation of G box H has order at least (1-eps/beta) k n.
- Theorem 25. Under the same hypotheses, tw(G box H) >= (1-eps/beta) k n - 1.
- Lemma 19. tw(G_1 box G_2) <= (tw(G_1)+1) v(G_2) - 1.

An eps-separation is a partition (A,S,B) of V with 1 <= |A|,|B| <= eps|V| and no A-B edge; its order is |S|.

The factors in Lemma 24 are arbitrary connected graphs. Paths enter only in Corollary 26. I checked the Lemma 24 proof by hand, including
2 beta - 1 >= 1 - eps/beta (equivalent to 6 beta^2 - 6 beta + 2 >= 0, which always holds) and the case split on copies.

## Reduction

Fix k >= 2 and a tree T on n >= 12k^2 vertices. (k=1 is tw(T)=1. n < 12k^2 is handled at the end.)

Step 1, pieces (reviewer Lemma A, PROOF.md). T has k pairwise edge-disjoint subtrees Q_i with at least m = floor((n-1)/(2k)) edges. Hence the private sets W_i = V(Q_i) minus the shared vertices have
at least mu = m-k+2 >= n/(4k) >= 3k vertices. (n >= 4k(k-1) gives the first inequality, n >= 12k^2 the second.)

Step 2, relaxed source Lemma 9 (reviewer Lemma B, PROOF.md). T_1' box ... box T_k' is a minor of F_k(T), each T_i' a tree on W_i. Source Lemma 9 is the case of pairwise vertex-disjoint pieces, which cannot reach a hub.
The only change is allowing pieces to meet in shared vertices and contracting those vertices into private neighbours. Take subtrees G_i of T_i' on exactly mu vertices.

Step 3, iterate Lemma 24. Put beta_j = 1 - j/(3k) for j=1..k, so beta_k = 2/3, beta_1 < 1 and 1/(1-beta_j) = 3k/j <= 3k <= mu. Let P_j = G_1 box ... box G_j, connected with mu^j vertices. Put K_1 = 1 and
K_{j+1} = ceiling(d_j K_j mu), with d_j = 1 - beta_{j+1}/beta_j = (1/(3k))/beta_j in [1/(3k), 1/(2k)].

Claim: every beta_j-separation of P_j has order >= K_j, and K_j <= mu^(j-1).
- j=1: an order-0 separation would disconnect the connected graph G_1. K_1 = 1.
- Step: apply Lemma 24 with G=P_j, H=G_{j+1}, m=mu^j, n=mu, k=K_j, beta=beta_j, eps=beta_{j+1}. m >= kn is K_j <= mu^(j-1). n >= 1/(1-beta) holds. Orders are integers, so the conclusion gives K_{j+1}.
  Also K_{j+1} <= mu^j/(2k) + 1 <= mu^j since mu >= 2.

Thus K_k >= (mu/(3k))^(k-1). Applying Theorem 25 at the last step (eps=beta_k=2/3) gives tw(P_k) >= (mu/(3k))^(k-1) - 1.

Step 4, assemble. By minor and subgraph monotonicity, tw(F_k(T)) >= x - 1 with x = (n/(12k^2))^(k-1). Since n >= k+1 gives tw >= 1, tw >= max(1,x-1) >= x/2. For n < 12k^2, x < 1 and tw >= 1 >= x/2.
Therefore, for every k >= 2, every n >= k+1 and every tree T on n vertices,

    tw(F_k(T)) >= (1/2) (n/(12k^2))^(k-1).

Step 5, upper bound. PROOF.md: centroid, remove token sets containing it, Lemma 19 on the resulting products. tw(F_k(T)) <= 2 n^(k-1) - 1. Source Theorem 1 upper bound is the star case: its central bag V_0 is exactly the set of tokens containing the centre.

Every hypothesis is paid: connectedness of every factor, integrality of the K_j, m >= kn, n >= 1/(1-beta), the eps < beta chain, all trees uniformly, all n >= k+1, and k fixed.

## What the bridge shows, and what it does not

Shows: the hand-off route and its congestion count are unnecessary. So is a new flow argument. The lower bound needs only pieces, one relaxation of Lemma 9, and repeated use of a lemma already
stated for arbitrary connected graphs in the paper the source cites for this purpose.

Does not show: that anyone printed this reduction or the conjecture's resolution. Steps 1 and 2 are reviewer-authored and short, and Step 2 is the one real new observation.
The ar5iv rendering is not checked against the J. Graph Theory final, whose lemma numbers may differ.
