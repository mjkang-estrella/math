# S2 checkpoint: reductions and exact remaining equality problem

Full S2 is UNRESOLVED. These deductions concern a hypothetical minimum-order,
then minimum-arc counterexample to S2, using the stipulated ordinary SNC.
They are not an independently reviewed result or a substitute target.

Let z be its unique Seymour vertex, and let F denote ordinary outgoing image.

1. D is strongly connected. A sink strongly connected component has no outgoing
arcs, is itself sink-free, and inherits every first/second neighborhood. If
proper, minimal order supplies two good vertices in it, also good in D.

2. Every vertex other than z has outdegree at least two. A vertex x with its
sole outgoing neighbor y has N2(x)=N1(y), since no opposite arc or loop exists;
sink-freeness makes x good. Moreover d+(z)=1: if at least two, delete any arc
out of z. The graph remains sink-free. At every other vertex the first
neighborhood stays fixed and the second can only shrink. Thus at most z is
good, contradicting minimal arc count. Write z->w for this unique arc.

3. For every nonempty S contained in V(D)\{z},

 |F²(S)\F(S)| < |F(S)\S|.                                      (SD)

Here S may equal V(D)\{z}. Repeat the source's lemma:subset-deficit proof
with I=F(S)∩S, E=F(S)\S and g(T)=|F(T)\(I∪T)| for T⊆E. Strong connectivity
makes E nonempty. Delete all arcs S -> E\T. If a sink is created, it is a
vertex v∈S and is newly good. If no sink is created, the smaller arc count
and minimality for S2 supply at least two good vertices. Vertices outside S
have unchanged first neighborhoods and cannot improve; the only originally
good vertex outside S was z. Hence at least one newly good v lies in S.
In either case Q=N1_D(v)∩(E\T) is nonempty. The exact same endpoint comparison
as in the source gives

 g(T∪Q)−g(T) ≤ |Q|+|N2_D(v)|−|N1_D(v)| ≤ |Q|−1.

All vertices of S were originally bad, which is crucial. Iterating to E
proves g(E)<|E| and hence (SD). No assertion for S containing z is made.

4. Put D'=D−z, with image F'. It is sink-free by (2). For nonempty S⊆V(D'),
set A=F'(S), B=F'²(S), a=1[z∈F_D(S)],
q=1[a=1 and w∉A∪B], and b=1[a=0 and z∈F_D(A)]. Directly:

 |F_D²(S)\F_D(S)| = |B\A|+q+b,
 |F_D(S)\S|       = |A\S|+a.

Therefore (SD) implies

 |B\A|−|A\S| ≤ −1+a−q−b ≤ 0.                                (WD)

Equality in (WD) forces a=1, q=b=0; in particular some S-vertex points to z
and w∈F'(S)∪F'²(S). For S={w}, a=0, so (WD) is strictly negative.

5. D' is strongly connected. Choose a sink strongly connected component C.
It is nontrivial since D' is sink-free, so F'(C)=C=F'²(C). By strong
connectivity of D, C has an arc to z unless C=V(D') (where it still does).
Equality in (WD) forces w∈C. Since z's only outgoing arc goes to w, C∪{z}
is then closed under all outgoing arcs of D. Strong connectivity of D makes
C∪{z}=V(D), proving the claim.

The remaining route is precise: D' is strongly connected; every subset has
nonpositive deficit (WD); every zero-deficit subset reaches z in one step
in D and reaches w within two steps in D'; and {w} has strict negative
deficit. The source's contradiction requires strictly negative deficit
for every nonempty proper subset before its transitive blowup. Weak deficits
cannot simply be substituted. Equality propagation in its compatible-pair
pruning objective, or a different exact use of these boundary constraints,
remains unpaid. Finite small-order tests are diagnostics only.

Primary comparison: Dara–Francis–Jacob–Narayanan 1808.02247v3, pp15–16
Theorem6/Lemma18/Lemma19 and pp19–21 Lemma25, theorem6 ending, Corollary5,
Conjectures2–3 and Proposition8 read. Their safe completions, modules and
median-order periodicity rely on the missing matching. Their Lemma18 is a
related deletion boundary fact; the general (SD)/(WD) reduction above is
not claimed independent of the source's arc-deletion mechanism.
