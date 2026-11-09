# 341108 — full ordinary proof, held; zero credit

Status: ordinary full-scope candidate relative to the source's parameter domain. Not accepted, not independently reviewed, not formally authorized. Final publisher body unavailable (403); specific source/prior/significance holds below. No assertion of literature novelty.

Literal source: Xi–So–Wang, arXiv:1811.08322v1, 19 November 2018, Section 4, pp.8–11, Conjecture 4.7. The source domain is simple strongly connected finite digraphs of order n with vertex connectivity k, 1 ≤ k ≤ n−2, and 0<α<1. The MathDB record leaves the definition of G_{n,k} implicit. The k=n−1 complete graph case is separated by the source and K(n,k,1) is undefined there; do not silently quantify that endpoint.

Claim: Every such G has μ_α(G) ≥ μ_α(K(n,k,1)), with equality precisely when G is isomorphic to K(n,k,1).

Definitions: Directed distance is shortest directed path length. Transmission is the row sum of the distance matrix D. M_α=α diag(transmission)+(1−α)D. Its spectral radius is μ_α. Set β=1−α>0 and N=n−k≥2. K(n,k,m), 1≤m≤N−1, consists of complete bidirected blocks S,A,B of sizes k,m,N−m, with all arcs in both directions between S and A∪B and all arcs A→B, and no arcs B→A.

Reduction with equality, independently justified. Pick a minimum k-vertex cut S. The condensation of G−S is a finite acyclic digraph with at least two components. Choose a source component A and put B=V(G)\(S∪A). Both A and B are nonempty and no arc goes from B to A. Add every missing arc except B→A to form H=K(n,k,m). Removing S disconnects H strongly, so its connectivity is at most k; adding arcs cannot lower connectivity, so it is exactly k. Adding an arc strictly lowers M_α entrywise at least at the corresponding off-diagonal entry, since β>0, and never increases any entry. Every off-diagonal distance is positive, hence the matrices are irreducible. Strict Perron comparison therefore gives μ_α(G)≥μ_α(H), with equality only when G=H in this labeling. For completeness, strict comparison follows by multiplying M_H x≤M_G x for a positive right Perron vector x of M_H by a positive left Perron vector of M_G; at least one strict entry gives strict inequality of radii. This pays the strictness bridge, not just the reduction's assertion.

The quotient. In H, vertices in S∪A have identical off-diagonal distances 1 to every other vertex. Rows for vertices in B have distance 2 to A and distance 1 to S and the other vertices of B. Their transmissions are n−1 and n+m−1, respectively. The partition (S∪A,B) has quotient
Q_m = [[α(n−1)+β(k+m−1), β(N−m)],
       [β(k+2m), α(n+m−1)+β(N−m−1)]].
Both off-diagonal entries are positive. Its positive Perron eigenvector lifts to a positive eigenvector of M_α(H) by making it constant on each class; thus its Perron root equals μ_α(H), not merely some other eigenvalue. No symmetry between S and A as graphs is asserted; equality of the relevant distance row sums is what is needed.

Let t_m=μ_α(H)−(n−1). Subtracting n−1 from the quotient diagonal, its trace is αm−βn and determinant is −βm(N−m). Thus t_m is the positive root of
p_m(t)=t²+(βn−αm)t−βm(N−m).
The determinant is strictly negative, so there is exactly one positive and one negative real root. In particular t_1>0.

Full-range comparison. For 2≤m≤N−1, using p_1(t_1)=0 and expanding just the difference gives
p_m(t_1)−p_1(t_1)=−(m−1)[α t_1+β(N−m−1)]<0.
Here m−1>0, α>0, t_1>0, and N−m−1≥0. Since p_m has exactly one positive root and is negative between zero and that root, p_m(t_1)<0 implies t_1<t_m. This covers the entire missing range α>4/5 and n<2k+2, as well as the source's already established ranges. If N=2 there is only m=1; no comparison is needed. Together with the strict saturation reduction it proves the stated inequality and equality characterization for every allowed n,k,α. It also explains why α=0 must be excluded: the difference can vanish at the opposite endpoint.

Source dependency audit: finite condensation/topological ordering, existence and positive left/right eigenvectors for a finite strictly positive-off-diagonal matrix, and elementary quadratic factorization. The source's Remark4.2 and Theorem4.3 were read in full including proofs; the argument above independently supplies their relevant bridges. No reliance on unexamined public theorem truth beyond these explicitly named classical facts; no mathematical computation or enumeration was run.

Prior and significance gates: v1 itself proves α≤4/5 (Theorem4.5) and all α when n≥2k+2 (Theorem4.6). Its explicit Conjecture4.7 asks for the remaining full domain. The final 2019 publisher article, DOI10.1016/j.laa.2019.04.038, is a precise matching final-source HOLD: its body was attempted and returned403; no alternate-delivery attempt is permitted. It may contain a later full proof or correction; this is not claimed as established. Three precharged search calls/nine queries across the lane and four current registry root snapshots do not clear literature or registry proof bodies. No new proof body found in snippets is asserted.

Strongest contrary case: the entire graph reduction and general quotient polynomial already occur in the original source. The new remaining step is an exact quadratic comparison, not new graph structure. A reviewer could judge the completed earlier-to-target bridge above a routine extension of the source's own method. Its being short is not by itself grounds for exclusion, and I do not self-adjudicate significance. Root and independent reviewers must decide that concrete objection before any formal investment. No earlier exact public full proof is claimed. No credit or formal dispatch.
