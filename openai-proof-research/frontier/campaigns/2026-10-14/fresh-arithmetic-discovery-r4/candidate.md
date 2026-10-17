# Two Seymour vertices in every sink-free oriented graph

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT.

**Author-level complete proposed proof of frozen S2. Independent proof and
contribution gates have NOT occurred. Campaign count unchanged.**

The statement is Dara–Francis–Jacob–Narayanan's Conjecture 2, not a new
conjecture. The proof below is relative to the stipulated ordinary Seymour
theorem and finite-relation pruning lemma in the pinned OpenAI manuscript
*A proof of Seymour's second-neighborhood conjecture*, at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Their truth is an assigned premise.
Every further deduction is given below. No restricted graph class replaces S2.

## Statement and notation

Every nonempty finite oriented graph D with no sink has two distinct vertices
v,w satisfying |N2+(x)| >= |N1+(x)| for x=v,w. An oriented graph has no loops,
parallel arcs, or opposite pairs. N2 means directed distance EXACTLY two.

For a digraph K, put F_K(S)=union_{x∈S} N1_K(x), without subtracting S.
Define

 δ_K(S)=|F_K²(S)\F_K(S)|−|F_K(S)\S|.

For a singleton, δ_K({v})=|N2_K(v)|−|N1_K(v)|. A vertex satisfying the
statement's inequality is called good. All sets below are finite.

## 1. A hypothetical minimum counterexample

Suppose S2 fails. Choose a counterexample D first with minimum vertex count,
then with minimum arc count. The stipulated ordinary Seymour theorem
(thm:main in the source) ensures at least one good vertex; thus D has exactly
one, called z.

D is strongly connected. Otherwise take a sink strongly connected component C.
Because D is sink-free, C is not a singleton and its induced graph is sink-free.
All first and second out-neighborhoods of its vertices stay inside C. Minimal
order would give two good vertices in C, hence in D, a contradiction.

Every vertex x≠z has outdegree at least two. If N1(x)={y}, then N2(x)=N1(y):
loops and opposite arcs exclude x and y from that last set. Since y is not a
sink, x would be good.

The vertex z has outdegree exactly one. If it had at least two outgoing arcs,
deleting one leaves a sink-free graph with fewer arcs. At any other vertex,
the first neighborhood stays fixed and deleting an arc cannot enlarge its
second neighborhood. Thus all other vertices remain bad, contradicting
minimality. Write z->w for z's sole outgoing arc.

## 2. Strict deficits for sets avoiding z

We prove

 δ_D(S)<0  for every nonempty S⊆V(D)\{z}.                      (1)

This adapts the source's lemma:subset-deficit, with the exception handled
explicitly. Fix S and put I=F_D(S)∩S, E=F_D(S)\S. Strong connectivity gives
E≠empty. For T⊆E define g(T)=|F_D(T)\(I∪T)|.

For T≠E, delete all arcs from S to E\T, obtaining D_T. At least one arc is
removed. If D_T has a sink, that sink is a newly good vertex v∈S. If D_T is
sink-free, minimality gives at least two good vertices in D_T. Vertices outside
S have unchanged first neighborhoods and cannot improve their second ones.
Only z among those vertices could originally be good. Thus again there is a
newly good vertex v∈S. In either case

 Q=N1_D(v)∩(E\T)

is nonempty and consists exactly of the first neighbors v loses. Originally
v is bad, because z∉S. Write d_i=|N_i,D(v)|, so d_2≤d_1−1.

The surviving first neighbors of v lie in I∪T. Any surviving two-step path
through I⊆S ends in I∪T, while one through T ends in F_D(T). Thus all surviving
two-step endpoints lie in I∪T∪F_D(T). Newly counted exact second neighbors
must have been lost first neighbors, hence belong to Q∩F_D(T). Conversely,
put

 C=F_D(Q)\(I∪T∪Q∪F_D(T)).

Every point of C was an exact second neighbor before deletion and is no longer
reachable in two steps. It cannot be v, since that would oppose v's arc to a
member of Q. Therefore

 d_1−|Q| ≤ |N2,D_T(v)| ≤ d_2−|C|+|Q∩F_D(T)|.

Direct set subtraction gives

 g(T∪Q)−g(T)=|C|−|Q∩F_D(T)| ≤ |Q|+d_2−d_1 ≤ |Q|−1.

Repeat, always deleting afresh from D, until T=E. Every added Q is nonempty
and disjoint from the current T. Summation yields g(E)<|E|. Since F_D(I)⊆F_D(S),
we have F_D²(S)\F_D(S)=F_D(E)\(I∪E). Its size is g(E), proving (1).

The proof does NOT assert (1) for a set containing z.

## 3. Delete the exceptional vertex, keeping its boundary information

Let H=D−z, with image operator F. It is sink-free because every remaining
vertex had outdegree at least two in D. For a nonempty S⊆V(H), put
A=F(S), B=F²(S), and define indicators

 a=1[z∈F_D(S)],
 q=1[a=1 and w∉A∪B],
 b=1[a=0 and z∈F_D(A)].

Since z's only successor is w, exact set comparison gives

 |F_D²(S)\F_D(S)|=|B\A|+q+b,
 |F_D(S)\S|=|A\S|+a.

Consequently (1) implies

 δ_H(S) ≤ −1+a−q−b ≤ 0.                                     (2)

In particular, if w∉F(S)∪F²(S), then δ_H(S)≤−1: for a=1 the indicator q
is one; for a=0 the displayed bound is already at most −1. Thus

 w∉F(S)∪F²(S)  implies  δ_H(S)≤−1.                          (3)

Also H is strongly connected. Take a sink strongly connected component C of H.
It is nontrivial, as H is sink-free, so F(C)=C=F²(C). Since D is strongly
connected, some vertex of C points to z. Equality δ_H(C)=0 in (2) forces
q=0, hence w∈C. Then C∪{z} is closed under outgoing arcs in D. Strong
connectivity of D implies C∪{z}=V(D). Therefore C=V(H), as claimed.
In particular all vertices of H have positive indegree. Let n=|V(H)|.

## 4. Transitive blowup and a bound on every fiber

Set m=n²+2. Replace each vertex p of H by a transitive tournament with labels
1,...,m, arcs from smaller labels to larger ones. For each base arc p->q,
put every arc from the p-block to the q-block. Call the resulting orientation
G, put X=V(G), and let J be its outgoing image operator. All indegrees of G
are positive. Define

 C_G(U)=|U|+|J²(U)|−2|J(U)|.

For every nonempty proper U⊂X whose support S in H is proper, the source's
blowup estimate, derived here, gives

 C_G(U) ≤ m δ_H(S)+n.                                       (4)

Indeed, let T_p⊆{1,...,m} be U's labels in block p and let f be the internal
image operator of the transitive tournament. For nonempty T with smallest
label a, f(T)={a+1,...,m}; it follows directly that

 |T|−2|f(T)|+|f²(T)|≤1.

Set H0=F(S)∪F²(S). The first image fills exactly every F(S)-block and has
internal image f(T_p) in remaining blocks. A two-step path with two external
arcs lands in F²(S), one with one external arc lands in F(S), and an entirely
internal path contributes f²(T_p). Therefore

 C_G(U) ≤ m(|H0|−2|F(S)|)+sum_{p∈S}|T_p|
           −2 sum_{p∈S\F(S)}|f(T_p)|
           +sum_{p∈S\H0}|f²(T_p)|.

Extend the final sum to S\F(S), which only increases it. Bound |T_p| by m on
S∩F(S), and use the internal bound on all other blocks. This gives

 C_G(U) ≤ m(|F²(S)\F(S)|−|F(S)\S|)+|S\F(S)|,

which implies (4). If instead S=V(H), positive indegrees give F(S)=V(H),
so J(U)=J²(U)=X and C_G(U)=|U|−|X|<0. By (2), every nonempty proper U thus
satisfies C_G(U)≤n, even though individual values need not be negative.

## 5. Compatible families have strictly negative total fiber defects

For P,Q⊆X×X define coordinate images J1 and J2, advancing the first or second
coordinate along an arc of G respectively. Say P,Q are compatible when
J1(P)∩J2(Q)=empty. Let Δ={(x,x):x∈X}. It is compatible with itself because
G has no opposite arcs. Restrict attention to compatible P,Q containing Δ.

Every column P_j={p:(p,j)∈P} and every row Q_i={s:(i,s)∈Q} is nonempty and
proper. Nonemptiness follows from the diagonal. If P_j=X, positive indegrees
make J1(P) contain X×{j}. An in-neighbor t->j gives (t,j)∈J2(Δ), a conflict.
The row argument is the same with the coordinates exchanged.

Fix an anchor j=(w,a), where 2≤a≤m. No member x of P_j has a two-step walk
x->t->j: the left member (x,j) would conflict with the right diagonal member
(t,t). It follows that its support S⊆V(H) satisfies

 w∉F(S)∪F²(S).                                              (5)

To check the direct-step part, if a base p∈S has p->w, every vertex in its
block has the two-step walk through (w,a−1) to (w,a). For a two-step base
walk p->q->w, choose any vertex in the q-block. Both contradict the preceding
exclusion. The support is nonempty and proper (H has an in-neighbor of w).
By (3) and (4), this special column has C_G(P_j)≤−m+n.

Identically, for a row Q_i anchored at i=(w,a), 2≤a≤m, any s->t->i would
make (i,s) conflict with the left diagonal member (t,t). Its support obeys
(5), and C_G(Q_i)≤−m+n.

Each side has nm fibers, of which at least m−1 are special. Every other
fiber has C_G≤n. Hence

 sum_j C_G(P_j) ≤ n²m−m(m−1)=−m<0,
 sum_i C_G(Q_i) ≤ n²m−m(m−1)=−m<0.

Coordinate images operate fiberwise, so these are exactly

 |P|+|J1²(P)|<2|J1(P)|,
 |Q|+|J2²(Q)|<2|J2(Q)|.                                     (6)

This is the additional operation: one whole exceptional block supplies a
quadratic gain m(m−1), dominating the at most n²m residual loss. It does not
pretend every subset of G has a strict deficit.

## 6. Apply the stipulated pruning lemma

For completeness the source extremal closure is specified, with only its
pruning lemma imported. Choose a compatible pair P,Q containing Δ maximizing

 M+d, where M=|P|+|Q| and d=|X|²−|J1(P)|−|J2(Q)|.

Compatibility makes d the number of uncovered points. Such a maximum exists.
Put R=(X×X)\J2²(Q) and C=(X×X)\J1²(P). From (6),

 |R|+|C| > M+2d.                                            (7)

Both contain Δ. For example if (v,v)∈J2²(Q), some s->v has (v,s)∈J2(Q),
while (s,s)∈P implies (v,s)∈J1(P), a contradiction. The other coordinate
is identical. All their diagonal members are conflict-free: a conflict of
left (v,v) with right (i,s) gives s->v->i, which from (s,s)∈P puts (i,s)
in J1²(P), excluding it from C. The other side is symmetric.

For the pruning lemma's conflict (p,j)∈R, (i,s)∈C with p->i and s->j,
its initial charge point (p,s) is outside J1(P)∪J2(Q). Indeed membership
in J1(P) supplies u->p from (u,s)∈P and hence (i,s)∈J1²(P); membership
in J2(Q) similarly supplies a two-step path that puts (p,j)∈J2²(Q).
Thus the initial charge set has size at most d.

The stipulated lemma:pruning, valid for every finite binary relation, gives
compatible P'⊆R,Q'⊆C, retaining all conflict-free diagonal members, with
at most d+d' deletions; here d'=|X|²−|J1(P')|−|J2(Q')| bounds the lemma's
points left uncovered after pruning. By (7),

 |P'|+|Q'|+d' > M+2d−(d+d')+d'=M+d,

contradicting maximality. This contradiction rules out the minimum
counterexample and proves the full frozen S2 statement, at author level.

## Attribution, novelty boundary, and validation limits

The strict subset-deficit argument, transitive blowup estimate, finite-relation
pruning, and compatible-pair objective are source antecedents. The ordinary
Seymour theorem is stipulated as well. Dara–Francis–Jacob–Narayanan already
state precisely this conjecture; their Theorem6 proves deletion survival
when the deleted graph is a tournament missing a matching. Its proof uses
safe completions, modular partitions, and periodic/stable median orders.
Their Lemma18 supplies related one-vertex deletion observations, and their
Corollary5 gives two good vertices for the missing-matching class. No claim
is made that those operations were discovered here.

The proposed added work is the minimal unique-good reduction, exact boundary
retention after deleting its sole-successor vertex, and aggregate fiber gain
from the m−1 interior anchors in ONE blowup block. This produces the full
unrestricted sink-free result using a different closure from the restricted
median-order machinery. Whether that addition is independently substantial
or already present elsewhere requires a separate contribution review.

Small finite graph checks support identities and prevent an invalid shortcut:
strong connectivity plus weak deficits does NOT force all singleton deficits
to vanish. The exact six-vertex counterexample in the diagnostic proves only
that shortcut false. No finite search is used to infer S2. The decisive
universal argument is Sections1–6 above. Source hypotheses are stipulated,
not audited. No manuscript, Lean packaging, publication, or acceptance made.
