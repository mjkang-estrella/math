# Edge-critical restrictions on a unique-good sink-free graph

Myeongjin Kang; no affiliation. Original prose CC BY4.0.
Supporting parent deduction, not a full proof or result nomination.

Premise: the pinned family173 theorem guarantees at least one Seymour
vertex in every nonempty finite oriented graph. Call v good when
|N2+(v)|>=|N+(v)|, with N2+ excluding v and N+. Suppose the desired
sink-free two-good assertion is false. Choose a sink-free counterexample
D first minimizing vertices, then arcs. The premise makes its good vertex
unique; denote it z.

If z has at least two outgoing arcs, delete one. The graph stays sink-free.
For every vertex other than z, its first out-neighborhood is unchanged and
its second out-neighborhood can only shrink. Thus no other good vertex
appears. The premise guarantees some good vertex, so the new graph again
has exactly one, contrary to arc minimality. Therefore N+(z)={w}.

In a sink-free oriented graph every outdegree-one vertex is good: its
successor has at least one out-neighbor, which is neither itself nor the
original vertex (no loops or digons). Hence all x!=z have outdegree>=2.
In particular w has outdegree>=2. For z, N2+(z)=N+(w).

Delete any arc x->y with x!=z. This remains sink-free. The vertex z is
still good: if x!=w its second neighborhood is unchanged; if x=w, that
neighborhood loses exactly y and retains at least one vertex. No vertex
other than x can newly become good, since its first neighborhood is
unchanged and its second can only shrink. Minimality therefore forces x
to become good in the deleted graph.

Write A=N+(x), B=N2+(x), and delta=|A|-|B|>0. Define

 P_y={b in B: y->b and no u in A\{y} has u->b},
 I_y=1 if some u in A\{y} has u->y, and 0 otherwise.

After deleting x->y the first neighborhood is A\{y}. The second is exactly
(B\P_y) union ({y} if I_y=1), a disjoint union. Indeed the only lost
length-two paths from x are those beginning with x->y; the only previously
excluded first neighbor that can become a second neighbor is y itself.
There is no return x by a two-cycle. Consequently

 delta_after = delta - 1 + |P_y| - I_y <= 0.

For every x!=z this gives 1<=delta<=2. If delta=2, then for EVERY y in A,
I_y=1 and P_y is empty. Thus D[A] has positive indegree at every vertex,
and each point of B is reached via at least two different vertices of A.
If delta=1, every y satisfies |P_y|<=I_y; in particular a source y of D[A]
has no private second neighbors, and any other y has at most one.

These are necessary structural conditions for a minimal counterexample,
not a contradiction. They do not establish the full two-vertex assertion.
The exact source-premise scope and any integration into its pruning proof
remain the active author's responsibility. No numerical test is used to
claim a universal graph conclusion.

## Further consequence conditional on the protected subset-deficit lemma

A minimal sink-free counterexample D is strongly connected. A proper
terminal strong component would itself be sink-free (a singleton terminal
component would be a sink of D); its two good vertices supplied by order
minimality would remain good in D. This contradicts uniqueness.

Suppose the author's protected lemma has established the source-style
strict subset deficit for every nonempty S contained in V(D)\{z}. Then w
has an in-neighbor other than z. Indeed, otherwise strong connectivity
and z's unique outgoing neighbor give F(S)=V(D)\{w} for S=V(D)\{z}:
every vertex other than w has an in-neighbor in S. Moreover z belongs to
F(S), so w belongs to F²(S). It follows that

 |F²(S)\F(S)| >= 1 = |F(S)\S|,

contradicting the protected strict deficit. Thus D−z has positive
indegree at every vertex: w retains an in-neighbor and no other vertex
loses an incoming arc when z is removed. This deduction is conditional
on that protected lemma, which is being proved by the author, and must
not be confused with a completed full argument.
