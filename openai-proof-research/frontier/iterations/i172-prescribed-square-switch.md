# I172: prescribed-switch transport and genuinely high-loss octagons

Date: 2026-10-10. **Eight accepted findings remain eight.** Technical
research iteration, not an acceptance or literature-priority nomination.

## Outcome

1. **I171 passes the independent audit in its stated scopes.** W171, C171,
   O171, the index-431 separator, and all three specified populations were
   checked independently. The ancestor verifier was authenticated but never
   executed, imported, or read as implementation.
2. **A restricted prescribed-square theorem is proved.** A signed affine
   certificate for the *prescribed* factor transports through a vertex splice
   away from its square, preserving its total coefficient on the lost
   Hamiltonian class. Consequently all remote-splice decorations of an even
   prism retain exclusion of $\alpha=-3/2$ at the protected square. This does
   not settle the coefficient for arbitrary braces.
3. **The minimal-octagon high-loss regime exists, with unbounded loss.**
   Opposite-corner cube splices of the even prism $P_m=C_m\square K_2$
   produce a genuine $(3,3)$ octagonal interface $G_m$, for every even
   $m\ge4$, with
   $$
   |V(G_m)|=2m+12,\qquad
   (\ell,t,\eta)=(m-3,m-4,1),\qquad
   (\delta_V,\delta_R,\epsilon)=(m-4,m-4,1).
   $$
   **All three compatible old families are empty.** An explicit residual
   rerouting, not the boundary toggle, recovers the $m-4$ missing within-class
   directions. The desired lower bound is sharp throughout this family.
4. The other attempted construction, two cap square expansions, **does not
   preserve high loss** in the specified 29 cases. Its complete failed
   construction evidence is retained.

Universal prescribed-square exclusion, the universal minimal-octagon lower
bound, universal exchange, (T), and Q164 remain **open**. The new high-loss
graphs have nontrivial three-edge cuts; no brace high-loss theorem is claimed.

## 1. Sources, scope, authentication, and methods

The full saved I172 brief and `AGENTS.md` were read first. All theorems of the
OpenAI repository at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated
true. No upstream truth audit was undertaken.

The actual statement of `cor:pfaffian-paths`, lines 812–828 in the authenticated
local `frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`,
was read: every three-edge path in a finite simple cubic 3-connected bipartite
Pfaffian graph extends to a Hamiltonian cycle; the text explicitly includes
planar graphs. Catalogue family 180 and the complete preprint tree identify
one manuscript. This supplies nonempty port/fibre classes when needed.
No external theorem retrieved during this iteration is a proof dependency.

Before use, the three I171 detached anchors matched:

| Artifact | SHA-256 |
|---|---|
| Report | `d9c61b5d49e778d80e376d39ee6ffee83ad11590fa68861d5bf66c25bfa7e5a6` |
| Seal | `0cd340b50cfd23a041bdab7baf827e1d8c26e279e9a7705caecd49a7d2eefedf` |
| Verifier | `a5c8a04f3e0f49b28151fb3d7c8c1fe127104e6e5b4373a5da810c7d1a3c2b45` |

The seal's inventory and successful-prevalidation bindings also matched.
The complete owned-file set equals the ancestor inventory: **53 entries**.
All **108 non-context external entries** match. The four inherited
context-ledger drifts are separately recorded, not excused mathematical
inputs. See `frontier/sources/i172_prescribed_square_switch/i171-authentication.json`.
The parent's stated 491.567906-second replay is inherited validation history,
not the runtime of an I172 run.

The first mathematical run, before populations, candidates, or searches,
tested indices

```
0,520,522,524,527,528,530,533,534,536,539,431
```

in that order, followed by C171's `two_component_forbidden_weight` witness at
step `[1,1,3]`. Index 0 and 431 give $(1,0,1)$; the ten high-loss indices give
$(7,6,1)$. Every subsequent diagnostic repeats these mandatory tests.

### Independent implementation

Only standard-library Python, invoked with `-I -B`, is used. No subagents or
third-party packages were used.

* Hamiltonian cycles: rooted vertex DFS agrees on complete incidence sets
  with a vertex-saturation prescribed-degree enumerator and connectivity
  filter. The full 2-factor set agrees with complements of an independent
  least-unmatched-vertex perfect-matching recursion.
* Spanning paths: endpoint DFS agrees on complete incidence sets with
  prescribed-degree enumeration. Two-path covers additionally require
  exactly two components and the actual prescribed endpoint pairing.
* Every rank is checked twice: gcd-normalized integer elimination in
  ascending pivot order, and independently written sparse `Fraction`
  elimination in descending pivot order. Caches store these double-checked
  answers, not modular estimates.
* Graph checks include simplicity, cubic degrees, bipartiteness, connectivity
  after every pair of vertex deletions, both directed edge incidences,
  single vertex links, and Euler characteristic two. These certify the
  supplied sphere embeddings. Generated expansions and splices receive
  the same checks.
* Inputs are authenticated data, not executable ancestors. Final replay uses
  immutable in-memory bound bytes, with all subsequent filesystem reads
  forbidden. Actual source bytes are compared before compilation.

The population audit freshly enumerates **201 labelled graph edge sets**
(105 source records plus the 96 generated descendants in this collection).
This is not an isomorphism census. The finite structural experiments retain
their full graphs, embeddings, cycles, families, exact offsets, rational
coefficients, and separators.

## 2. Notation and independent I171 verdicts

Let $\mathcal B$ be the finite simple cubic bipartite planar 3-vertex-connected
graphs with a specified plane embedding. An admissible expansion deletes
cofacial disjoint edges $e=uv,f=xy$ in cyclic order $u,v,\ldots,y,x,\ldots$,
and inserts arms $up,vq,xr,ys$ and square $pq,qs,sr,rp$.
All vector spaces and affine coefficients are rational. Coordinates are
sorted old edges, retaining zeros at deleted edges.

Let $N_{ij}$ be the Hamiltonian classes with the two deleted-edge statuses.
Write
$$
S=N_{10}\cup N_{01}\cup N_{11},\quad L=\operatorname{diff}(S),\quad
L_0=\sum_{ij\ne00}\operatorname{diff}(N_{ij}),\quad
V=\operatorname{diff}(N_{00}),
$$
$$
U=\operatorname{diff}(P_{ux})+\operatorname{diff}(P_{vy})
  +\operatorname{diff}(D_{11}),\quad
\ell=d(G)-\dim L,\quad t=\dim(L+U)-\dim L .
$$
Here $D_{11}$ has the pairing $u-v,x-y$, not an arbitrary two-path cover.
For actual representatives and $C_0\in S$, set
$$
b=P+Q+D+2e+2f-3C_0,\qquad
\eta=\dim(L+U+\mathbb Qb)-\dim(L+U).
$$
The six-fibre rank identity is $d(H)=2+\dim(L+U+\mathbb Qb)$.
Thus exchange is $t+\eta\ge\ell$. The two deleted coordinates have
$\rho(L)=\mathbb Q^2$, and $L\cap\ker\rho=L_0$.

For $A\in N_{10},B\in N_{01},C\in N_{11},N\in N_{00}$ retain the exact offsets
$$
\beta=P+Q+D+2e+2f-A-B-C,\qquad c=N-A-B+C.
$$
The compatible families, residuals, and deficits have precisely R170's
definitions: $F_J=\{N:N-q_J\in J\}$ tests binary entries **and** connectivity
and pairing; residuals use $J\setminus(F_J-q_J)$ with an actual class anchor.
Then $U=V_{\rm good}+R$, and
$$
\ell-t=\delta_V+\epsilon-\delta_R .
$$
No containment of $V$ in $U$ or $L+U$ is assumed.

### W171: PASS, with its conditional affine-span scope

For a facial square $u-v-y-x-u$, put $a=ux,c'=vy$,
$W=L+V$, $r=N-C_0$, and $s=e+f-a-c'$.
Deleting the surviving sides gives the three translation bijections, so
$U=V$ and $D_G=W+\mathbb Qr$. The factor $F=N+s$ has exactly two components:
deleting $a,c'$ gives the planar $u-v,x-y$ pairing, and $e,f$ close those
paths separately.

In the equality case $t=\ell-1$, $r\notin W$ and $b=3r+2s\bmod W$.
If $s\notin D_G$, the bridge is independent. **If $s\in D_G$**, write
$[s]=\alpha[r]$. Now, and only under this condition, $F$ lies in the
Hamiltonian affine span. Applying a functional with $w(W)=0,w(r)=1$ to
any signed affine representation of $F$ gives
$$
\sum_{C\in N_{00}}\lambda_C=1+\alpha .
$$
Thus exchange fails exactly at $\alpha=-3/2$. In
$\Gamma=\mathbb Z[r]+\mathbb Z[s]$, orient the primitive generator $g$
so $[r]=ag$ with $a>0$, and write $[s]=kg$, $\gcd(a,k)=1$.
The equation $3a+2k=0$ has primitive solution $(a,k)=(2,-3)$.
Also $[F-C_0]=g$ is exactly $a+k=1$, equivalently
$\alpha=-(a-1)/a$. This is arithmetic equivalence, not universal
positivity or a graph-structural proof.

The convex shortcut is impossible: at each zero or one coordinate of a
binary factor, every positive-coefficient summand of a convex representation
must have that same coordinate. Every such Hamiltonian summand would equal
the disconnected factor, a contradiction. Signed representations do not
have this restriction.

### C171: PASS, keeping $F$ and $T$ distinct

Fresh enumeration verifies the original order-32 graph, its sphere embedding,
the step `[1,1,3]`, **110 cycles**, **1,007 perfect matchings**, and extension
of **all 1,032 disjoint edge pairs**. An explicit extending matching for
each pair is retained. Therefore it is a brace under 2-extendibility.

The displayed rational functional annihilates every fresh $L,V$ generator
and has $w(N-C_0)=1$. The retained distinct two-component factors satisfy
$$
w(T-C_0)=-\tfrac12,\qquad w(F-C_0)=\tfrac1{14},\qquad T\ne F .
$$
Both component pairs have the certified spanning interpretation; the
negative $T$ is **not** the prescribed switch. These checks are in
`mandatory-attempt-01.json`, including complete factor and cycle vectors.
Neither “two components” nor “brace” makes generic factor positivity true.

### O171 and index 431: PASS

On a length-three arc the forced outer edges of $N\in N_{00}$ are removed
and its middle edge added. The result is binary exactly when the middle
edge was absent. Removing two cycle edges and adding one edge yields a path,
possibly with one cycle. Two such toggles give two paths, possibly with up
to two cycles; pairing still matters. This argument proves the stated
universal classification and does not imply compatibility.

At 431, fresh classes have sizes $2,4,4,14,4,4,14$ in order
$N_{00},N_{10},N_{01},N_{11},P_{ux},P_{vy},D_{11}$.
Both middle edges are present in one old cycle. For the other, the single
toggles give a path plus a cycle, and the double toggle two paths plus two
cycles. **All three $F_J$ are empty.**
Here $\dim L_0=8$, $U\subset L_0$, and
$(\delta_V,\delta_R,\epsilon)=(1,0,0)$.

The I171 separator
```
(1,-1,0,2,-2,0,2,0,4,0,1,0,1,0,0,0,-1,0,0,0,0,-1,0,0,0,0,1,0,0,0)
```
annihilates **all** of $L+U$. Its pairing with both the retained and fresh
bridge is **10**, and with the retained oriented old direction is **8**.
The retained and fresh bridges differ by $L+U$. This is the new I171
separator, not the earlier U-only separator.

### Finite populations: PASS, separately

The **806** square steps on **38** stored order-32 `walks` parents have:

```
(ell,t,eta):
(0,0,0):188; (1,0,1):237; (1,1,0):68; (2,2,0):37;
(3,2,1):98; (3,3,0):20; (4,4,0):9; (5,4,1):41;
(5,5,0):8; (6,6,0):4; (7,6,1):30; (7,7,0):2;
(8,8,0):6; (9,8,1):31; (11,10,1):11; (13,12,1):16.
```

There are **464** equality coefficients, all $-13/14$, and **342** null
coefficients, not 806 equality cases. Every retained equality functional
and its **full 2-factor weight histogram** is independently checked.

The **624** minimal-octagon steps on the 15 census records plus 90 walks
records of order at most 32 reproduce:

```
(ell,t,eta): (0,0,0):356; (1,0,1):202; (1,1,0):66.
(delta_V,delta_R,epsilon):
(0,0,0):356; (0,0,1):175; (1,0,0):27; (1,1,0):66.
```

The **96** targeted descendants are regenerated, not just read from their
retained graphs. They protect the exact 431 octagon; deleted square edges
avoid its perimeter. Depth one takes all choices, depth two all choices
from the first six children, depth three the first four choices from each
of the first six depth-two children. Repeated labelled edge sets are
suppressed. The generation levels are exactly **8,64,24**, at orders
24,28,32. Graphs and oriented face lists agree with I171. Their histograms:

```
(ell,t,eta): (1,0,1):63; (1,1,0):33.
(delta_V,delta_R,epsilon): (1,0,0):63; (1,1,0):33.
```

These are record populations, not disjoint graph-isomorphism censuses.
The inherited 914-step walks population has 610 equality occurrences:
914+806=1,720 steps and 610+464=1,074 equalities. The separate historical
206-step square population has 182 equalities, so 206+914=1,120 **steps**
and 182+610=792 equalities, before addressing overlap. I172 does not
reaudit the full 914 population or add it to the census as disjoint data.

## 3. New prescribed-switch result: exact signed transport

### Proposition S172: remote-splice certificate transport

Let $A,B\in\mathcal B$, let $A$ have a prescribed facial square, and splice
$A$ at a vertex $z$ **outside that square** to $B$ at $h$, using a planar
port bijection. Assume all three omitted-port Hamiltonian classes of $B$
are nonempty (the stipulated P4 result supplies this).

Suppose that for **every** $N\in N_{00}(A)$ the prescribed
$F=N+s$ has a rational signed affine Hamiltonian representation whose
total coefficient on $N_{00}(A)$ equals a fixed $q$.
Then for every lifted $N'\in N_{00}(A\star B)$, the prescribed
$F'=N'+s$ has such a representation with the **same total $q$**.
No coefficientwise nonnegativity is asserted.

**Proof.** A Hamiltonian cycle crosses the three-edge splice cut twice.
Restriction and restoration of the two deleted vertices identify its cycles
with compatible pairs $(C,D)$ having the same omitted port. This is the
usual cycle splice bijection, proved by cutting and joining the two
spanning paths, not assumed to preserve arbitrary factors.

For the particular $N'$, let $N,D_*$ be its pair, with port type $i_*$.
Choose one Hamiltonian cycle $D_i$ of each type in $B$, taking
$D_{i_*}=D_*$. In a signed representation
$F=\sum_C\lambda_C C$, let $a_i$ be the sum of coefficients in port type $i$.
The square avoids $z$, so the incident coordinates of $F$ are those of $N$.
The three port vectors $(0,1,1),(1,0,1),(1,1,0)$, together with total
coefficient one, force $a_i=1$ for $i=i_*$ and zero otherwise.
Consequently
$$
\sum_C\lambda_C D_{\operatorname{type}(C)}=D_* .
$$
Glue each $C$ to this chosen $D_{\operatorname{type}(C)}$.
On the $A$ coordinates their signed sum is $F$; on the $B$ coordinates it
is $D_*$; on cut coordinates it has the same port values as $N'$.
Thus the result is **exactly** $N'+s$, with no hidden offset.
The two deleted-square-edge statuses are unchanged by the splice, so
the $N_{00}$ coefficient total remains $q$. This explicitly preserves the
prescribed switch and proves the assertion. ∎

**Exclusion consequence.** If $q\ne-1/2$, every equality case of the lifted
square has $s\in D_{A\star B}$ and $\alpha=q-1\ne-3/2$, by W171.
Non-equality square cases already have $t\ge\ell$ because $U=V$ and
$D_G=L+V+\mathbb Qr$. Hence exchange holds for all these lifted square
steps. This consequence iterates over any finite sequence of splices at
vertices outside the protected square. It does not require a generic
2-factor positivity premise.

### Corollary: protected even-prism squares

For every even $m\ge4$, every lateral square of $P_m=C_m\square K_2$,
either deletion pair, and any such finite remote-splice decoration by
members of $\mathcal B$, the protected square satisfies exchange; any
equality coefficient remains
$$
\alpha=-\frac{m-3}{m-2},\qquad q=\frac1{m-2}>0 .
$$
This is governed by the **core rim length**, not the decorated graph order.

Here is the paid base calculation, already present in I170 and not claimed
as new. Write $t_i,b_i,r_i$ for rails and rungs. The complete Hamiltonian
list comprises $m$ cycles $C_j$ with every rail except $t_j,b_j$ and rungs
$r_j,r_{j+1}$, plus two cycles $X,Y$ using all rungs and opposite
alternating rail matchings. A proper nonempty block of used rungs has a
unique horizontal matching in each layer; multiple omitted matching edges
disconnect the factor. If all rungs occur, only opposite alternating
choices are connected. This proves exhaustiveness.
Horizontal and total-coefficient equations show these $m+2$ vectors
affinely independent, so $d(P_m)=m+1$.
Coordinatewise,
$$
(m-2)(r_0+r_1-t_0-b_0)
=(m-3)C_0-\sum_{j\ne0}C_j+X+Y .
$$
The right coefficients total zero. For rung deletion the lost cycles are
$C_2,\ldots,C_{m-2}$; summing coefficients gives
$-(m-3)/(m-2)$. Rail deletion reverses the square vector and has only
$C_0$ lost, giving the same coefficient. Adding this signed identity
to any lost $N$ yields the required total $q$. S172 applies.

**Finite validation.** Twelve steps, both deletion types on each splice
of $P_4,P_6,P_8$ at vertex 2 with $P_4$ or $P_6$, were checked.
Full lifted Hamiltonian sets, exact rational signed coefficients,
prescribed $F'$ vectors and lost-class totals are retained in
`remote-splices-attempt-01.json`. Every signed sum is verified at every
edge coordinate. This is an infinite special-case theorem with finite
validation, not a table extrapolation or a solution on all braces.

The earlier I165 affine-splice formula is acknowledged. S172's contribution
is transporting the **specific factor and class-total certificate**, with
the port totals and offsets paid explicitly; its literature novelty is
unestablished.

## 4. New high-loss minimal-octagon family

### Explicit construction

Use $P_m$ with top vertices $0,\ldots,m-1$, bottom vertices
$m,\ldots,2m-1$, and the lateral face $0,1,m+1,m$.
Take two labelled copies of the cube $P_4$, with vertices $a_0,\ldots,a_7$
and $b_0,\ldots,b_7$ in the same prism convention.
Delete $0,m+1,a_0,b_0$ and connect
$$
1a_1,\ (m-1)a_4,\ ma_3;\qquad
1b_1,\ mb_4,\ (m+2)b_3 .
$$
All other edges survive. These are two planar vertex splices at opposite
square corners. The new specified face is
$$
1,a_1,a_2,a_3,m,b_4,b_5,b_1,1 .
$$
Delete $e=a_3m$ and $f=1b_1$. With
$(u,v,x,y)=(a_3,m,1,b_1)$ the complementary arcs are
$a_3-a_2-a_1-1$ and $m-b_4-b_5-b_1$, both length three.
The two added cube pieces have seven vertices each, so the order is $2m+12$.

A planar port identification gives the displayed face, preserves bipartition,
and produces no loop or parallel edge. For 3-connectivity of a vertex
splice, consider deletion of at most two vertices. If both deleted vertices
lie in one piece, the intact other punctured piece connects all surviving
ports; every component on the damaged side has a port, since the original
piece minus those two vertices was connected through the removed splice
vertex. If one deletion lies on each side, each punctured piece minus that
one vertex is connected by 3-connectivity, and at least one of the three
cut edges survives. The cases of fewer deletions are included.
Thus $G_m\in\mathcal B$. These are non-brace examples with genuine splice cuts.

### Proposition K172: exact survival loss

For every even $m\ge4$ the displayed octagon has $\ell=m-3$.
In particular $\ell$ is unbounded; $\ell\le1$ is false for this precise
face/arc class in $\mathcal B$.

**Proof.** Let $\pi$ collapse the two cube pieces, reading their cut-edge
coordinates as the restored incident coordinates. Each Hamiltonian cycle
of the prism lifts in $2\cdot2=4$ ways, since each cube has two Hamiltonian
cycles in each omitted-port class. It keeps its $e,f$ statuses.

At one splice the kernel of the cycle-difference projection is the sum of
the attachment's three within-port difference spaces. For the cube this
has dimension $d(P_4)-2=3$: its six Hamiltonian vectors are affinely
independent and port differences have dimension two.
If a surviving family meets all three ports, all those kernel vectors
already occur as differences of surviving lifts, holding a base cycle
fixed. Therefore both $d(G)$ and $\dim L$ increase by exactly three.

For rung deletion in $P_m$, the survivors are
$C_{m-1},C_0,C_1,X,Y$. At either replaced vertex, $X,Y$ give the two
rail-omitted types and one of these ordinary survivors gives the rung-omitted
type. Thus survival meets all three ports at both splices. After the first
splice, any original survivor still has lifts, so this remains true at the
second. Initially $d(P_m)=m+1$ and $\dim L=4$. After both:
$$
d(G_m)=m+7,\quad \dim L=10,\quad \dim L_0=8,\quad \ell=m-3 .
$$
This proves the infinite quantifier without extrapolating the finite ranks. ∎

### Proposition R172: residual recovery and sharp lower bound

For every even $m\ge4$ in this construction,
$$
(\ell,t,\eta)=(m-3,m-4,1),\qquad
(\delta_V,\delta_R,\epsilon)=(m-4,m-4,1).
$$
Thus $\delta_R=\delta_V+\epsilon-1$ and exchange holds.

**Proof of class projection.** Every old Hamiltonian class projects to its
corresponding prism class. A $P_{ux}$ path has one endpoint inside the
$a$-cube piece. Its cut has odd usage, but $e$ is deleted, leaving at most
two available cut edges; it therefore uses exactly one. That edge cannot
be $1a_1$: the internal path would join its endpoint $a_3$ directly to
the other endpoint 1, omitting the rest of the graph. It must use
$(m-1)a_4$. Restoring vertex 0 gives the original prism $0$–$1$ spanning
path. The other cube has no path endpoint, so it uses its two available
cut edges. The $P_{vy}$ argument is symmetric.

For $D_{11}$, each cube has one path endpoint and hence exactly one cut
edge. The prescribed pairing excludes $1a_1$ and $mb_4$, respectively:
these would join the wrong pair of terminal endpoints. The remaining
ports are forced. Collapsing the two pieces gives exactly the original
$D_{11}$ cover. Conversely all these restricted prism objects lift,
with a spanning seven-vertex cube path for each required port pair.
Each such pair has exactly two paths, so all seven families have constant
fibre four. No binary-but-disconnected configuration is included.

Consequently $\pi(U)=V_{\rm prism}$, since all three old square path
difference spaces equal $V_{\rm prism}$. The same is true of $\pi(V)$.
The prism's $m-3$ lost cycles are part of an affinely independent list,
so their differences have dimension $m-4$ and intersect its surviving
difference space trivially.

To justify the ambient kernel assertion for the path differences, not
just Hamiltonian differences: $G_m$ is affine-full **by the paid splice
calculation**. Its homogeneous degree space has dimension
$|E|-|V|+1=m+7=d(G_m)$, since it is connected and bipartite. Hence every
within-path difference lies in $D_{G_m}$. The kernel of $\pi$ on this
space is the six-dimensional attachment kernel already contained in $L$.
It is also contained in $L_0$, because its deleted-edge coordinates vanish.
Therefore
$$
\dim(L+U)-\dim L=m-4,\qquad
\dim(L_0+V)-\dim L_0=m-4 .
$$
The cross-class $c$ projects to the remaining affine-independent prism
direction, so $\epsilon=1$. This uses fullness only for this explicit
splice family, not M168's refuted typed-fullness premise.

**Why the compatible old families are nevertheless empty.**
For an old lost cycle the $a$-piece is a spanning path between $a_1,a_4$.
Its two possibilities, in cube labels, are
```
1-5-6-2-3-7-4
1-2-3-7-6-5-4 .
```
The first omits middle edge $a_1a_2$. Its boundary toggle adds that edge
and isolates the cycle $a_1a_5a_6a_2a_1$.
The second already uses the middle edge and toggles nonbinary.
For the $b$-piece the old paths run from $b_4$ to $b_3$:
```
4-5-1-2-6-7-3
4-7-6-5-1-2-3 .
```
The first toggles nonbinary at $b_4b_5$; the second isolates
$b_4b_7b_6b_5b_4$. A double toggle cannot repair an isolated cycle in
either disjoint cube piece. Thus every $F_J$ is empty,
$V_{\rm good}=0$, and $R=U$.
The dimension calculation gives $\delta_V=\delta_R=m-4$.

**Explicit alternative residual translation.** Fix the first $a$-path above
and either fixed $b$-path in every lift of
$C_2,\ldots,C_{m-2}$. Remove cut edge $1a_1$ and replace the $a$-path by
```
3-7-6-2-1-5-4 .
```
It is a spanning cube-minus-$a_0$ path from $a_3$ to $a_4$.
The resulting whole graph is a spanning $a_3$–1 path, and the replacement
offset is independent of $j$. Differences of these $m-3$ residual paths
equal the differences of the fixed lifts exactly, recovering $m-4$
independent directions modulo $L$. This is not the alternating
length-three boundary toggle.

Finally, $\pi(b)$ is an actual prism bridge, because all three projected
objects and the $2e+2f-3C_0$ offset project exactly.
Modulo the prism's $L+V$, it is
$(3+2\alpha)r=\frac{m}{m-2}r\ne0$.
Since the kernel is in $L$, $\eta=1$. This proves all assertions. ∎

The same calculation gives $d(H)=m+9$ for the expanded child.
It does not imply a corresponding universal rank statement for braces.

### Finite certificates, separate from the infinite proof

The four checks $m=4,6,8,10$ give:

| $m$ | Order | Hamiltonian cycles | $(\ell,t,\eta)$ | $(\delta_V,\delta_R,\epsilon)$ |
|---:|---:|---:|---|---|
| 4 | 20 | 24 | $(1,0,1)$ | $(0,0,1)$ |
| 6 | 24 | 32 | $(3,2,1)$ | $(2,2,1)$ |
| 8 | 28 | 40 | $(5,4,1)$ | $(4,4,1)$ |
| 10 | 32 | 48 | $(7,6,1)$ | $(6,6,1)$ |

All four have $|N_{00}|=|P_{ux}|=|P_{vy}|=|D_{11}|=4(m-3)$,
$|N_{10}|=|N_{01}|=4$, $|N_{11}|=12$. Complete payloads:

* `cut-octagons-attempt-01.json`: full intermediate and final graphs, cycles,
  families, all toggle failures, $\beta,c,b$, old and recovered bases,
  rational bridge separators, and the two survival-kernel checks.
* `residual-certificates-attempt-01.json`: fixed-lift old cycles, actual
  residual paths, their exact constant translation, and independent
  recovered ranks $0,2,4,6$.
* `cut-projection-attempt-01.json`: complete projected sets for **all seven
  classes**, each fibre exactly four, bridge-offset check, and the exhaustive
  two-path lists of the seven-vertex cube gadget.

For either single toggle there are $2(m-3)$ nonbinary and $2(m-3)$ binary
path-plus-cycle failures. For the double toggle there are $3(m-3)$
nonbinary and $m-3$ binary two-path-plus-two-cycle failures.
Nothing is relabelled a compatible path merely because its entries are binary.

### Failed construction retained

Starting from $P_m$, square-expand $t_0$ with $t_j$ in the top cap, then
$b_0$ with $b_k$ in the bottom cap, preserving the two original rungs.
The selected lateral square becomes first a hexagon and then a genuine
$(3,3)$ octagon. For $m=6,8,10$, take every even
$j,k\in\{2,4,\ldots,m-2\}$, giving $4+9+16=\mathbf{29}$ cases.
All original losses were $m-3$, but the final histogram is
$(0,0,0):20$ and $(1,1,0):9$. Thus **this construction loses the high-loss
mechanism**. The complete intermediate/final graphs and cycle/path data
are in `cap-transport-attempt-01.json`. This failed proposal was not
silently replaced by an unexplained larger low-loss scan.

## 5. Boundaries, validation contract, and next step

D168 still blocks uniformly bounded bidirectional dual-face transfers;
M168 still refutes typed degree-and-port fullness. Neither is contradicted
by the explicit affine-full prism/cube splice family. Deleted-edge-only
separation is still blocked by $\rho(L)=\mathbb Q^2$. Index 431 still
refutes both blanket $V\subset U$ and $V\subset L+U$. No such premise
appears in either new proof.

The one development failure was an authentication schema mismatch:
I171 calls its owned-file list `files`, not `owned`. The failed source
snapshot and error receipt are retained; the corrected full authentication
passed. There were no mathematical diagnostic crashes, abandoned declared
scans, or network retrieval errors. Earlier I171 development failures and
the four inherited ledger discrepancies remain authenticated ancestor
data. Own source stages and every unsuccessful mathematical proposal
are retained in the inventory; `attempts.json` distinguishes them.

Actual literature searches and their limited returned primary-source
excerpts are recorded in `frontier/sources/i172_prescribed_square_switch/literature.md`.
No full external proof was inferred from a search snippet. Neither this
search nor the absence of a retrieved duplicate establishes literature
novelty. The propositions are at most new-to-this-project consequences.

### Immutable-first final evidence

The control order is: freeze this final report, source and payload bytes;
inventory every owned file and mathematical input; successfully run
`--prevalidate`; create `seal.json` **once by exclusive creation**; then
run the final read-only replay. No resealing or report edits follow sealing.

The verifier authenticates the complete inventory before compiling any
diagnostic. It supplies every input from immutable bound memory and
permits compilation only of exactly matching owned source bytes.
The audit guard rejects writes, filesystem mutation, network, subprocess,
all subsequent filesystem reads, outside compilation, outside execution,
and forged bytes under an owned source filename. Eight probes exercise
these eight prohibitions. Seven deterministic mathematical payloads are
recomputed and compared byte-for-byte. All modules are freshly written;
ancestor Python remains opaque hashed data.

The only context-only bindings are `README.md`, `frontier/README.md`,
`frontier/TEN-FINDINGS.md`, and `frontier/iterations/README.md`. Their
drift receipts remain explicit. No ancestor graph, theorem statement,
mathematical report, payload, or source file receives that exemption.
The outer read-only binding check checks current file bytes again after
replay; diagnostics themselves cannot suffer a pathname-only TOCTOU read.

Reproduce from the project directory with:
```
python -I -B frontier/experiments/i172_prescribed_square_switch/verify.py
```
The `--prevalidate` mode is for the initial unsealed package only.
The inventory and successful prevalidation receipt are sealed control
files. Detached report, verifier and seal hashes, replay timings and final
binding counts are emitted in the final receipt/response, avoiding a
self-hash or report/seal circularity.

**Recommended next step.** Audit S172 and the seven-class octagon collapse
first. Then seek a **brace** high-loss $(3,3)$ interface by breaking the
two cube splice cuts while protecting the octagon and tracking the
survival kernel and residual translation. The present family identifies
exactly which missing directions must survive such surgery. For the
primary problem, use S172 only to remove already-controlled remote
decorations; the remaining task is a genuinely brace-internal signed
relation excluding $(2,-3)$, with C171's $T\ne F$ obstruction mandatory.
The acceptance gate and the eight-finding count are unchanged.
