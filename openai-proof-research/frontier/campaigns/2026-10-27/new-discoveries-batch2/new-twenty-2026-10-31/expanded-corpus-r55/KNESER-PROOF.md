# 361086: ordinary refutation of arXiv v4 Conjecture 2.5

Status: complete ordinary proof, no Lean endpoint, zero credit. Published 2025 body unread after HTTP 403. No qualification or novelty PASS is claimed. This is an exact refutation of the displayed v4 statement, not a proof of a bounded surrogate. Independent review is outstanding.

Source: Chau–Ellis–Friedgut–Lifshitz, arXiv:2312.06370v4, 13 November 2024, Definition in Section 1 and Conjecture 2.5, printed page 10. Page visually inspected; PDF receipt and hash in sources/receipts.jsonl. The statement has no restriction k>2 or asymptotic n hypothesis. The n>10000ks^5 hypothesis belongs to the separate main theorem, not this conjecture.

Take n=7, k=2, m=11. We have binom(7,2)/2=21/2 <=11<=21, and the smallest t with binom(t,2)>=11 is t=6 (binom(5,2)=10, binom(6,2)=15).

Let B consist of {6,7}, together with {i,6} and {i,7} for 1<=i<=5. It has eleven distinct pairs. The vertex {6,7} is disjoint from none of B. For each i, the pair {i,6} is disjoint precisely from the four pairs {j,7}, j!=i; symmetrically for {i,7}. Thus Delta(B)=4.

Now let F be ANY eleven-element subfamily of binom([6],2). Regard F as the edge set of a simple graph J on six vertices. Its complement H in K6 has four edges. For every J-edge {v,w}, exactly deg_J(v)+deg_J(w)-1 J-edges meet {v,w}, so the number of disjoint partners is 12-deg_J(v)-deg_J(w). It suffices to find a J-edge with degree sum at most 7.

If deg_H(v)>=3, then 1<=deg_J(v)<=2 (H has only four edges), and choosing any J-neighbour w yields deg_J(v)+deg_J(w)<=7, hence at least 5 disjoint edges.

Suppose instead Delta(H)<=2. Four edges have eight incidences among six vertices. There must be at least two distinct vertices u,v of H-degree 2. If some such pair is NOT an H-edge, then {u,v} is a J-edge and deg_J(u)+deg_J(v)=3+3=6, giving six disjoint edges.

Otherwise every pair of degree-2 vertices is an H-edge. There can be at most three degree-2 vertices (a clique in maximum degree 2). If there are three, they form a triangle, using three H-edges and saturating all three vertices; the fourth H-edge is among the other three vertices. Pick a degree-2 vertex u and an endpoint w of that fourth edge. Then {u,w} is in J and the J-degree sum is 3+4=7.

If there are exactly two degree-2 vertices u,v, the remaining four H-degrees sum to 4 and are at most 1 each; hence all four equal 1. Since u has only two H-neighbours, at least one of these four degree-1 vertices w is not its H-neighbour. Again {u,w} is in J and the J-degree sum is 3+4=7.

Thus in every case a pair A in F has at least five disjoint partners in F. This proves Delta(F)>=5>Delta(B)=4, so no F on [6] with eleven pairs can minimize over all families on [7]. This contradicts Conjecture 2.5 exactly.

The exhaustive independent Python diagnostic checks all 1365 compressed families; 420 have maximum degree 5 and 945 have maximum degree 6. It corroborates the argument but is not a formal certificate.

Remaining gates: actual 2025 journal-body comparison; targeted primary predecessor/successor and significance review; full Lean semantics for finite uniform families, disjointness degrees, actual maximum, least t and exact negation; extracted strict warningAsError rebuild, all local declaration/axiom audit, and independent reviews. No Lean build or formal packet is claimed. Source gap is retained and the route is parked under the assignment instruction rather than pursued through denied-access retries.
