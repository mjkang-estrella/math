# Split transport: valid lower bound, insufficient all-order magnitude

This is an uncredited failed route, not a proof of the source conjecture.

Let C(T) be the multiset of the n-1 unordered bipartitions A|A^c obtained by deleting each edge of a labelled tree T. Define

    h(A|A^c,B|B^c)=min(|A symmetric_difference B|, n-|A symmetric_difference B|),
    W(T,U)= min over bijections C(T)->C(U) of sum h.

The cost h is the quotient metric on the binary Hamming cube under complementation. To see its triangle inequality, choose representatives of the first two partitions minimizing their Hamming distance and choose a representative of the third minimizing distance to that chosen second representative; ordinary Hamming triangle inequality bounds the quotient distance of the first and third. Composition of two assignment bijections then proves the triangle inequality for W. This is the actual classical Matching Split construction; its novelty is not claimed. Even only a pseudometric would suffice below.

If leaf v slides from w to u across CURRENT edge wu, the singleton split {v}|rest persists. Every edge other than wu and the moved pendant edge has the same bipartition as before: all paths from v to the remaining graph enter on the same side unless that removed edge is wu. The bipartition associated with wu toggles precisely v. All other split tokens can therefore be matched at zero cost, with cost1 for wu, so W(T,T')<=1. Composition along any sequence proves W(T,U)<=d_G(T,U). This argument permits v to have any label, including a distinguished root.

Nevertheless, W cannot provide the desired full lower bound. For a path on n labels, its split side sizes are:

* n=2m: twice each k=1,...,m-1, once k=m;
* n=2m+1: twice each k=1,...,m.

Pair splits of equal smaller-side size in any two paths. For size k, h<=2k because two k-element sets have symmetric difference at most2k; also h<=floor(n/2) for any two partitions. Hence if n=2m,

    W <= 2 sum_(k=1)^(m-1) min(2k,m)+m = floor(3m²/2).

For m=2a the sum evaluates to6a²; for m=2a+1 it evaluates to6a²+6a+1. These give the displayed floor formula. If n=2m+1,

    W <= 2 sum_(k=1)^m min(2k,m) = floor(3m²/2)+m.

Both expressions are <=3n²/8. For all n>=9 this is STRICTLY below floor(n²/2)-n: the difference is at least n²/8-n-1/2, positive at9 and increasing thereafter.

Why path pairs are sufficient to obstruct this strategy: source Lemma3.16 proves Ψ(T)<=floor(n²/4)-n+1 with equality ONLY for paths. Theorem3.18 bounds d(T,U)<=Ψ(T)+Ψ(U)+n-2. If either tree is not a path this is at most floor(n²/2)-n-1. Thus any pair attaining the conjectured diameter must consist of paths. The above W bound excludes certification by W for every possible such pair at every n>=9. This does not exclude more structured/nonlinear invariants or resolve the conjecture.

An exact small falsifier to `W=d_G`: n6 source path 0-1-2-3-4-5 and target path 2-1-0-5-4-3 have true leaf-slide distance12, but split transport8. Complete BFS and exact assignment DP verify this. Across ALL360 labelled path targets modulo reversal at n6, maximum W is10, already below12. At n7 all2520 path targets have W<=14, while a true distance17 occurs. These are finite mechanism tests, not new parameter-instance results.

The local cut update was checked on all6480 directed slides encountered across the complete n5/n6 state spaces. The n7 search omits this repetitive per-edge check. The checker also verifies the two closed-form sums for1<=m<=1000. None of these finite checks substitutes for the all-order argument above.
