# Refutation of the full zero-diagonal sparsity conjecture

RETIRED CAMPAIGN DUPLICATE: r245 already refuted this exact source statement with a stronger4n−10 family, and sol-das-ap-irreducible-source-formal-r1 formalized an n5 witness. This is a preserved ordinary repeat proof only, with zero fresh credit. It is not an acceptance or literature-priority claim. No assertion is made about Conjecture 5.2 (allowing algebraic positivity).

Source: Sunil Das, *Sign patterns that allow algebraic positivity*, https://arxiv.org/pdf/2112.00442v3, arXiv version dated 22 March 2022; document dated 23 March 2022. Definition in §3, PDF p10; Conjecture 5.1 in §5, PDF p22. Its quantifiers are: every minimally AP-irreducible sign pattern of order n with zero diagonal has at most 2n−2 nonzeros. The frozen PDF hash is in access.json and bindings.json. The source defines AP-irreducibility by (i) strong connectivity of D(A), (ii) a positive entry in every row and column, and (iii) strong connectivity of D(B_A), where B_A=A_+−(A_−)^T. Here A_− retains negative entries, so B_A has nonnegative entries: its support consists of positive arcs together with reversed negative arcs. Overlap adds positive contributions; it never cancels them.

## A five-vertex certificate

Take the following sign pattern, with vertices a,b,x,c,d in that order:

```
      a  b  x  c  d
a     0  +  0  0  -
b     +  0  +  0  0
x     0  -  0  +  0
c     0  0  -  0  +
d     0  0  0  +  0
```

It has 9 nonzeros, exceeding 2·5−2=8. Its positive arcs are a↔b, b→x→c, c↔d; its negative arcs are x→b, c→x, a→d. In D(A), the chain b,x,c is bidirected and the two end pairs are bidirected. Thus D(A) is strongly connected. In B_A the reversed negative chain arcs duplicate positive chain arcs, and the remaining reversed negative arc is d→a. Consequently a→b→x→c→d→a is a directed Hamiltonian cycle, proving strong connectivity of B_A. Each row and column has a positive entry.

Every positive entry is essential: deleting a→b empties positive column b; deleting b→a empties positive column a; deleting b→x empties positive column x; deleting x→c empties positive row x; deleting c→d empties positive column d; deleting d→c empties positive row d. After deleting negative x→b, D(A) has no arc entering {a,b}. After deleting negative c→x, D(A) has no arc entering {a,b,x}. After deleting negative a→d, B_A has no arc entering {a,b}. Each is a nonempty proper directed cut. Thus deletion of any nonzero destroys AP-irreducibility. Deletion of further entries cannot restore any of its three monotone requirements. The pattern is minimally AP-irreducible and refutes the source conjecture. ∎

## Structural mechanism: an infinite family

For any integer t≥1, use n=t+4 vertices a,b,x_1,…,x_t,c,d. Put positive arcs a↔b and c↔d, and put a positive directed chain v_0→v_1→…→v_(t+1), where v_0=b, v_i=x_i for 1≤i≤t, and v_(t+1)=c. Put negative arcs v_(i+1)→v_i for 0≤i≤t, and a→d. All unspecified entries, including the diagonal, are zero. Positive and negative positions are disjoint.

There are 4+(t+1)+(t+1)+1=2t+7=2n−1 nonzeros. D(A) is strongly connected because it contains the bidirected chain connecting the two positive two-cycles. B_A contains the Hamiltonian cycle a,b,x_1,…,x_t,c,d,a. Positive row/column coverage is immediate.

Each positive two-cycle arc is essential by an empty positive row or column exactly as above. Each positive chain edge ending at x_i is the only positive entry in column x_i. The last positive chain edge x_t→c is the only positive entry in row x_t. For a negative chain edge v_(i+1)→v_i, removing it leaves no D(A) arc entering S_i={a,v_0,…,v_i}. The extra negative a→d leaves S_i, and all other chain edges stay on one side of its boundary or point outward. Removing negative a→d leaves B_A without any incoming arc to {a,b}. This proves minimality for every t≥1.

Hence the proposed bound fails at every order n≥5. This family and the five-vertex witness are one refutation, not separate outcomes.

## Scope and routine-adaptation objection

Das's Lemma 3.10 proves the 2n−2 bound under the extra condition that no positive entry connects distinct strongly connected components of A_+. Its proof contracts those components into a minimally strongly connected quotient and sums the standard 2m−2 arc bounds. Here the positive components are {a,b}, the t singleton vertices, and {c,d}; positive chain arcs cross components. The omitted hypothesis therefore fails explicitly. In D(A), reverse chain arcs are essential; in B_A they duplicate positive chain arcs, whereas the reversed long negative arc is essential only in B_A. Minimality of their joint requirements does not imply minimality of a single contracted digraph. That is the specific obstruction to extending Lemma 3.10.

The constructive general-family proof is logically independent of the initial randomized search. structural_check.py uses Boolean Floyd–Warshall and explicit cut certificates; checks.py used forward/reverse DFS and single-entry deletion. Both use exact discrete arithmetic. Their finite runs validate implementations, while the arguments above prove the universal family and the full source refutation.
