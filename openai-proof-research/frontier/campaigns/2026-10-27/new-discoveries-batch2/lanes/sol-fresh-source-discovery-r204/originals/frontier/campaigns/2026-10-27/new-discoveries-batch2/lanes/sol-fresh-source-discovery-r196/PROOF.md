# Ordinary candidate: sparse three-constrained terminal reliability

This is an ordinary mathematical candidate, not accepted, counted, independently
reviewed, formalized, or established new to the literature. It addresses the
entire sparse-range open problem immediately after Lemma 27 in Romero,
arXiv:2610.36120v1, p10: for ALL integers n>=5 and 5<=m<=2n-3,
H_(n,m) is a 3-uniformly most reliable two-terminal graph in T_(n,m).
It does not claim the source's separate dense-range classification.

All graphs are finite, simple, undirected, with distinct terminals s,t. Isolated
vertices are permitted. Write p=1-rho for edge survival. Each edge survives
independently with probability p. A success is the existence of an s-t path of
length at most three. For m odd, H has st and k=(m-1)/2 internally disjoint
two-edge s-t paths, with the remaining vertices isolated. For m even, it has
st, k=(m-2)/2 such paths, and one edge between two of their interior vertices.
These are the intended graphs explicitly characterized in source Lemma23.
Printed Definition9 has an indexing defect: for odd m it runs v_i from3
through (m-1)/2, giving only (m-5)/2 common neighbors and m-4 edges.
The raw page4 was visually checked (definition9-page4.png). It is not a
literal m-edge definition. Here H always means the fully specified m-edge
graph above, equivalently the graph explicitly described in Lemma23.
We prove the source existential optimization question with that graph;
SOURCE review must retain this discrepancy. The indexing repair alone
is not a discovery or extra credit. We prove domination over EVERY
competitor and EVERY p in [0,1].

## 1. Elementary monotone reductions

We can suppose st is present. Otherwise remove any edge f and insert st,
coupling their survival indicators and all other edges. If an old successful
path uses f and f survives, the new direct edge survives. If the path avoids
f it remains. Thus success never decreases. This gives a coupling proof of
source Lemma 20; strict coefficientwise claims are unnecessary here.

Call a nonterminal vertex double if both terminal edges are present, single
if exactly one is present, and empty if neither is present. Suppose an interior
edge xy has a single endpoint x, say sx exists and xt does not. Replace xy
by xt, coupling their indicators. Every old successful path using xy must
be s-x-y-t, since x has no edge to t (and must have a terminal edge to
participate in any path of length three). The new s-x-t succeeds whenever
this old path did. Every other successful path remains. The argument with
s,t exchanged is identical. Hence the replacement cannot decrease reliability.
It turns x double and removes one interior edge. Repetition terminates.

An interior edge incident to an empty vertex lies on no s-t path of length
at most three, so it can be deleted without changing reliability. Once the
previous replacements terminate, every remaining interior edge has double
endpoints. All single terminal edges are now irrelevant too and can be
deleted. Keep their number in an unused edge budget; this is legitimate
because subsequent comparisons may use graphs with at most m edges, and
the final graph will have exactly m edges. Unused vertices remain available.

Consequently every competitor is dominated by a graph consisting of st,
a double vertices, an arbitrary simple interior graph F on those a vertices,
and isolated vertices, with 1+2a+e<=m, where e=|E(F)|. Let
t=m-1-2a-e>=0 be the unused budget. No step adds vertices to the fixed
n-vertex set. So far each comparison holds for all p by an explicit coupling.

## 2. A finite association lemma, including its proof

Use the ordered states T<N<S. For a finite product of these chains, suppose
the strictly positive weight is a product of positive one-site weights and
two-site factors whose matrices are TP2: for rows i<j and columns k<l,
M(i,k)M(j,l)>=M(i,l)M(j,k). Then increasing functions f,g have nonnegative
covariance under the normalized weight.

Proof by induction on the number of sites. One site is Chebyshev's identity:
2 Cov(f,g)=sum_(x,y) mu(x)mu(y)(f(x)-f(y))(g(x)-g(y))>=0.
For the induction step condition on the last site z. The conditional weights
on the other sites have the same form, hence are associated by induction.
If z<z', the ratio of the conditional unnormalized weights at z' and z is
a product of one-site nondecreasing functions, by TP2 of each incident
factor. It is therefore a positive nondecreasing function r of the other
sites. For any increasing h, induction gives E_z(hr)>=E_z(h)E_z(r),
so E_(z')h=E_z(hr)/E_z(r)>=E_z h. For an increasing f depending also
on z, first use pointwise f(x,z')>=f(x,z), then the preceding comparison.
Thus z -> E(f|z) and z -> E(g|z) are nondecreasing. The conditional
covariance identity and the one-site case give
Cov(f,g)=E Cov(f,g|z)+Cov(E(f|z),E(g|z))>=0.
This proves the lemma. Multiplication by positive one-site factors does not
affect the TP2 ratio argument. The proof applies to nonadjacent sites and
arbitrary underlying finite graphs; no tree, degree or planarity hypothesis
has been inserted.

## 3. Conditional failure model and its uniform correlation bound

Assume 0<p<1. Put rho=1-p, q=1-p^2 and u=p/(1+p)<1/2.
Conditional on each double vertex failing to form a surviving two-edge
path, its terminal-edge state is independently

    P(S)=P(T)=u,  P(N)=1-2u=rho/(1+p).

Here S means only its s-edge survived, T only its t-edge survived, N neither.
For an interior edge xy, a three-edge success occurs exactly when its endpoints
are opposite S,T and the edge survives. Integrating the independent interior
edges therefore gives

    U(F)=rho q^a Z(F),
    Z(F)=E_product [ product_(xy in E(F)) phi(sigma_x,sigma_y) ],

where phi is rho on opposite S,T states and 1 otherwise. The rho factor
is the probability that st fails. All events are thereby accounted for,
including paths with either orientation through an interior edge.

Normalize the weight in Z(F) to a probability mu_F. The ordered interaction
matrix is

    [1   1  rho]
    [1   1   1 ]
    [rho 1   1 ].

All its 2x2 minors with increasing rows/columns are nonnegative (they are
0, 1-rho, or 1-rho^2). Hence the association lemma applies. The measure
is invariant under exchanging S and T at EVERY site simultaneously.
Condition on all states except x. If x has b T-neighbors and c S-neighbors,
its conditional unnormalized weights for S,N,T are u rho^b, 1-2u,
u rho^c. Put A=rho^b, B=rho^c. Since A+B<=2,

    P(sigma_x != N | others)
       =u(A+B)/(1-2u+u(A+B)) <= 2u.

Global S/T symmetry then gives mu_F(S_x)=mu_F(T_x)<=u.
The event S_x is increasing and T_y is decreasing in the stated chain order.
Applying association to 1_(S_x) and -1_(T_y) gives, for x!=y,

    mu_F(S_x,T_y) <= mu_F(S_x)mu_F(T_y) <= u^2.

The same holds with S,T exchanged, so the probability of opposite states
at ANY two distinct sites is at most 2u^2. This bound holds for an arbitrary
F, including disconnected F, with no numerical or extremality premise.

## 4. Replacing two budget units by a fresh double vertex

Remove k interior edges, where k is 0,1, or 2, and let F0 be what remains.
Using mu_(F0), the product inequality product_(i=1)^k(1-p I_i)
>=1-p sum_i I_i and the preceding bound yield

    Z(F)/Z(F0) >= 1-2k p u^2 >= 1-p^2=q.

For k<=2 the last inequality follows from
4p u^2=4p^3/(1+p)^2<=p^2, equivalently 4p<=(1+p)^2,
whose difference is (1-p)^2>=0. For k=0 the same bound is immediate.
Replace these k removed edges and 2-k unused budget units by an independent
two-edge s-t path through a previously isolated vertex. The new failure
probability is rho q^(a+1) Z(F0), whereas the old one is
rho q^a Z(F)>=rho q^(a+1)Z(F0). Hence reliability does not decrease.

This is the universal replacement bridge; it is not inferred from the small
census. Independence of the newly added terminal edges is part of the model.

## 5. Termination and the full vertex/edge budget

While e+t>=2, choose k=min(e,2), remove k interior edges and spend
2-k unused units. If e>=2 this spends no unused units; if e=1 the condition
ensures t>=1; if e=0 it ensures t>=2. The operation is therefore always
legal. The identity 2a+e+t=m-1 is preserved, while a increases by one
and e+t decreases by two. Whenever a new vertex is needed,

    2a+2 <= m-1 <= 2n-4,

so a+1<=n-2 and an isolated nonterminal vertex exists. In particular no
hidden infinite supply of vertices is used. This ends with e+t=0 or 1.

If m is odd it ends with a=(m-1)/2,e=t=0, precisely H_(n,m).
If m is even it ends with a=(m-2)/2,e+t=1. If e=1,t=0 it is already
H_(n,m), since any one edge on the a double vertices gives the same
isomorphism class. If e=0,t=1, spend that last budget unit on an edge
between two double vertices. Adding an edge cannot hurt reliability and
a>=2 since even m>=6. Again the resulting graph is H_(n,m).

The final graph has exactly m edges and n vertices. All comparisons dominate
EVERY competitor at every 0<p<1. At p=0 every reliability is zero; at p=1
H succeeds with probability one, so domination also holds at both endpoints.
This proves the stated full sparse-range ordinary candidate.

## Classical-adaptation and novelty objection

The complete applicable classical bridge is explicit above: coupling reductions,
finite TP2 association (proved here), S/T symmetry, a union bound for two
interior edges, and budget induction. FKG association is classical; neither
association nor its formalization is claimed new. The source's earlier
induction does not contain this conditional-state replacement argument, and
its stated deletion equality is false (checks.json gives an exact witness).
This candidate is not excluded because it is short or uses classical tools.
Whether applying this complete bridge to the source question qualifies as
substantive requires independent root review. Literature novelty is HOLD:
the 2025 proceedings body and complete current registry bodies were not read,
and no all-history priority clearance is claimed. No larger dense-range
classification, separate lemma credit, Lean or manuscript investment follows.
