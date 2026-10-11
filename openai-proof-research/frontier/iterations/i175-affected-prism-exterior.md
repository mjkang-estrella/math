# I175: affected-P8 saturation, five-port anchors, and missing-type correction

Research iteration, 2026-10-10. **Technical only. Eight accepted findings
remain eight; two remain.** All OpenAI theorems at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.
No upstream truth audit, independent-review clearance, novelty claim,
or acceptance increment is made.

## Outcome

The proposed order-26 affected-P8 exterior exists in the stated sphere
embedding and starts at loss **3**. The **first two** permitted canonical
triples, `[0,0,6]` and `[0,0,8]`, produce order-30 graphs with
**loss zero and survivor rank 16**. Each is a brace, with actual perfect
matchings extending all **900** disjoint edge pairs. Their protected
interfaces are still **(3,1) hexagons**, not high-loss octagonal braces.
No second attachment or second-cut surgery is eligible or executed.

There are three structural conclusions:

1. A five-port path-packing criterion gives a uniform sufficient local
   rank/image/anchor condition for saturation, with an exact exhaustion
   and kernel argument. It is verified on the two affected-P4, two
   affected-P6, and two new affected-P8 constructions. **No infinite
   prism-family saturation theorem is claimed.**
2. For a proper active subset $I$ of available full types $T$, the
   splice-defect correction is exactly
   $$
   \ell_G=\ell_{H_T}+\dim K_T-\dim K_I,\qquad
   K_J=\sum_{i\in J}\operatorname{diff}(\mathcal A_i).
   $$
   These are sums of the **actual** attachment spaces, not sums of
   their dimensions and not assumed typed fullness.
3. At this protected exterior interface, all three types at vertex 7
   are forced by the stipulated three-edge-path theorem. Thus its
   missing-type boundary cannot be exploited while preserving the
   specified local geometry and admissibility.

## 1. Source contract and authentication

The full original saved I175 brief, `AGENTS.md`, immutable upstream
contract, relevant catalogue entry and complete manuscript-path listing
were read before new mathematical scans. The actual pinned statement
`cor:pfaffian-paths`, lines 812–828 of
`frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`,
was read with its hypotheses: finite simple cubic, 3-vertex-connected,
bipartite and Pfaffian; the text includes planar graphs. It states
that every three-edge path extends to a Hamiltonian cycle.

The detached I174 anchors match:

| Artifact | SHA-256 |
|---|---|
| Report | `5690d67776a455018d1906ba778ce6b4e3afd8258cbbaeb8b2e1f7e66bff8cca` |
| Seal | `b63e358e0506567a2098d61dfe164a2f2b4db721488105d16dd238cdc06886ef` |
| Verifier | `2a9df59029ea699daab69d4355e8934faf2791c230a6775102fb2e8e00aa4e83` |

The complete **107-owned** file set, **277 non-context external**
bindings, and inventory/successful-prevalidation control chain match.
The **four separate contexts** give **281 external/context entries**.
The contexts are only `README.md`, `frontier/README.md`,
`frontier/TEN-FINDINGS.md`, and `frontier/iterations/README.md`.
Their inherited and current bytes are recorded separately.

I174's parent disposition and receipts were read and bound. Its replay
PASS in **17.08744652697351 seconds**, four byte-identical payloads,
eight blocked probes, empty stderr and unchanged before/after bindings
is authenticated history, not an I175 execution time.

**The explicit pre-seal transition is preserved exactly.** I174's first
packaging build failed after the parent's late I173 whitespace note.
Both the 6,035-byte and 6,539-byte versions, the exact 504-byte inserted
note, failed source/report snapshots, empty stdout and assertion stderr
remain authenticated. Removing the note exactly recovers the first
version and its hash. No sealed ancestor or mathematical assertion
changed; this is not a fifth context exemption. The parent's retained
extracted-note EOF warning and its correction of the ordinary
`git diff --no-index` exit-1 misreading are preserved, not silently
“fixed” in sealed evidence.

Ancestor Python is opaque byte evidence. It was never executed,
imported, or copied as implementation. The enumerators, rank algorithms,
graph operations, audit routines, packaging and verifier here are fresh.
All writes are confined to the three authorized I175 paths. No agents,
shared-ledger edits, staging, commits or publication were used.

## 2. Definitions and mandatory first tests

All vectors use sorted undirected-edge coordinates over the rationals.
For facial order $u,v,\ldots,y,x,\ldots$, delete $e=uv,f=xy$.
The families are
$N_{00},N_{10},N_{01},N_{11},P_{ux},P_{vy},D_{11}$;
the last has exactly two spanning paths paired $u-v,x-y$, with
no isolated cycle. Put
$$
S=N_{10}\cup N_{01}\cup N_{11},\quad L=\operatorname{diff}(S),\quad
L_0=\sum_{ij\ne00}\operatorname{diff}(N_{ij}),\quad
V=\operatorname{diff}(N_{00}),
$$
$$
U=\operatorname{diff}(P_{ux})+\operatorname{diff}(P_{vy})
 +\operatorname{diff}(D_{11}),\quad
\ell=d(G)-\dim L,\quad t=\dim(L+U)-\dim L.
$$
For actual representatives $A,B,C,N,P,Q,D$ and an actual $C_0\in S$,
$$
b=P+Q+D+2e+2f-3C_0,\quad
\beta=P+Q+D+2e+2f-A-B-C,\quad c=N-A-B+C.
$$
The alternating odd-arc vectors are $q_A,q_B$. For
$J=P_{ux},P_{vy},D_{11}$, use $q_J=q_A,q_B,q_A+q_B$.
Compatibility is membership of $N-q_J$ in the actual family, not
just binary coordinates. The compatible-old within-class sum is
$V_{\rm good}$; $R$ uses actual residual-minus-anchor vectors.
Every full diagnostic checks
$$
U=V_{\rm good}+R,\quad
\delta_V=\dim(L_0+V)-\dim(L_0+V_{\rm good}),
$$
$$
\delta_R=\dim(L_0+V_{\rm good}+R)-\dim(L_0+V_{\rm good}),\quad
\epsilon=\dim(L_0+V+\mathbb Qc)-\dim(L_0+V),
$$
$$
\ell-t=\delta_V+\epsilon-\delta_R.
$$
It also checks $\rho(L)=\mathbb Q^2$, exact bridge displacement,
and equal bridge increments from $b,\beta$.

Before any new scan, the fresh implementation completed, in order:

`0,520,522,524,527,528,530,533,534,536,539,431`,
then C171, I172 $G_6,G_{10}$, and the first I174 P6/P6 surgery and
its contracted exterior. Later diagnostics repeat this prerequisite.

- The ten high-loss indices give $(\ell,t,\eta)=(7,6,1)$;
  indices 0 and 431 give $(1,0,1)$. Complete seven-family sets,
  residual sets, $b,\beta,c$, and ranks are compared.
- C171's actual prescribed square switch at `[1,1,3]` is reconstructed
  coordinatewise. The functional annihilates the fresh $L,V$ directions.
  Its prescribed $F$ has value $1/14$; the distinct generic $T$
  has value $-1/2$. Both have two components. There are 110 Hamiltonian
  cycles and fresh matching extensions for all 1,032 disjoint edge pairs.
- The index-431 separator annihilates every $L+U$ generator, evaluates
  to 10 on the bridge and absolute value 8 on the old difference.
  Both false containments $V\subseteq U$, $V\subseteq L+U$ are
  explicitly rejected. All three compatible-old families are empty.
- Fresh prism/cube splice constructions reproduce $G_6,G_{10}$
  and their losses 3 and 7. The first I174 square operation is rebuilt
  from its initial embedding. Its contracted exterior has order 26,
  survivor rank 14 and loss zero.

The first development failure was a **diagnostic schema mistake**:
`rankUV` denotes $\dim(U+V)$, not its increment over $\dim U$.
The failed source stage, empty JSON payload and assertion stderr are
retained. Correcting the field convention made every mandatory check pass.
No mathematical result was altered to fit a count.

## 3. Independent original-scope audit

### Q173: finite certificates, not re-execution of the whole search

Fresh checks cover all **236** retained histories. Each graph passes
simple cubic bipartite, every-two-vertex-deletion connectivity, and
oriented sphere checks. Every retained survivor used for rank is an
actual Hamiltonian cycle using a protected deleted edge. Two exact
rank algorithms find
$$
\dim L=|E|-|V|+1.
$$
For a connected bipartite graph, row signs transform its unsigned
incidence matrix into an oriented incidence matrix of rank
$|V|-1$. Hence this lower certificate attains the rational upper
bound, so all 236 losses are zero without assuming completeness
of the inherited cycle lists.

All **328,920** displayed matching extensions are checked coordinatewise,
and their coverage plus the retained failed pairs equals every disjoint
edge pair. Failed extensions are freshly ruled out by matching recursion.
Precisely **212** records are braces. This is a new certificate check,
not a rerun of all old cycle/path enumerations, the entire historical
search, or the exhaustive three-cut census. I174's additional absorption
and remote-transport audits remain authenticated evidence, not newly
repeated whole searches here.

### I174 finite graphs and applications

Fresh complete seven-family comparisons cover its **15** records:
three initial graphs, six first children and six contracted applications.
The initial prism splices are reconstructed from formulas and oriented
rotations. Their losses are 3. All six first children have loss zero.
Fresh matching recursion supplies **9,324** successes and **36** failures
on the nine decorated graphs, all non-braces. No second surgery was
eligible. The other **20** valid first triples remain untested.

The six applications freshly project all seven families onto their
contracted exteriors and retain every projection and fibre multiplicity.
The ranks of the untouched P4/P6 kernels are 3/5, not common cube
constants. There are only four reduced constructions: affected P4
has order 22/rank 12; affected P6 has order 26/rank 14. Their protected
faces are (3,1) hexagons.

A second development failure mixed full-coordinate local vectors with
shorter projected image vectors in a rank call. The empty failed payload,
IndexError stderr and sources are preserved. The corrected audit checks
zero exterior projection of local vectors, independent image rank and
the full survivor rank equal to their sum, in their proper coordinate
spaces.

### S174: proof audit in its exact scope

A Hamiltonian cycle crosses a splice three-cut exactly twice and restricts
to spanning paths. Cutting/restoring gives the typewise complete product.
For a zero-sum signed combination let $a_i$ be its type totals. The
cut equations are $a_2+a_3=a_1+a_3=a_1+a_2=0$, forcing all totals zero.
Thus the projection kernel is the sum of actual within-type attachment
spaces. Conversely, fixing an exterior cycle of each active type and
varying its complete attachment fibre realizes those spaces.

With all three exterior survivor types active and all three attachment
types nonempty, both full and survivor kernels are
$K_A=\sum_i\operatorname{diff}(\mathcal A_i)$, of dimension $d(A)-2$.
Actual type-anchor differences supply the two independent port images;
they are not discarded translations. Surjectivity and rank-nullity give
$\ell_G=\ell_H$, without assuming attachment affine fullness.

Ambient saturation additionally requires connected bipartite factors,
compatible bipartite gluing and the corresponding full-space hypotheses.
The finite applications pay those requirements. Changing only their
untouched attachment cannot restore defect under S174. Breaking that
cut is outside the lemma.

## 4. The bounded affected-P8 experiment

Take core $P_6$ on $0,\ldots,11$; attachment labels are $a_i=12+i$.
Remove core 0 and attachment 0. The cut is exactly
$$
1a_1,\quad5a_7,\quad6a_8.
$$
Keep vertex 7 contracted. The short attachment route is $1-9-8$.
The actual protected face is
$$
[1,13,21,20,6,7]=[1,a_1,a_9,a_8,6,7],
$$
and the deletions are $20-6$ and $1-7$.

The pieces use disjoint numeric labels. The unreversed attachment
rotation has Euler characteristic zero and is retained as a rejected
embedding. Reversing that local rotation gives the oriented sphere
embedding, including the protected face. Directed-dart coverage, a
single cyclic link at every vertex, Euler characteristic two, cubic
bipartiteness and every-two-vertex-deletion connectivity are checked.

The order-26 initial graph has 32 Hamiltonian cycles,
$d=14,\dim L=11,\ell=3$, with survivor type counts 2,4,8 at vertex 7.
Its three tight-cut disjoint pairs fail extension; the other 660 pairs
have explicit matching extensions. It is not a brace.

Faces are oriented, rotated to their lexicographically least numeric
sequence and sorted. Cross-affected-cut candidates use one internal edge
on each side, avoid the protected perimeter, and preserve bipartiteness.
There are **14 valid triples**, **14 orientation skips** and **4
perimeter skips**. All candidates/skips are retained. Only the first
two valid triples are executed, leaving **12 valid triples untested**.

Face 0 is
`[1,2,3,4,5,19,18,17,16,15,14,13]`.
The first edges are $1-2,17-18$; the second are $1-2,15-16$.
New vertices are 28,29,30,31 in each separate child.

| Construction | Seven counts $00,10,01,11,P,Q,D$ | $d$ | $\dim L$ | $\ell,t,\eta$ | Brace |
|---|---|---:|---:|---|---|
| Initial | 18,2,6,6,6,18,6 | 14 | 11 | 3,2,1 | no |
| `[0,0,6]` | 30,6,6,22,12,30,12 | 16 | 16 | 0,0,0 | yes |
| `[0,0,8]` | 36,4,6,30,24,36,24 | 16 | 16 | 0,0,0 | yes |

The initial $(\delta_V,\delta_R,\epsilon)=(0,0,1)$; both children give
$(0,0,0)$. Exact residual/bridge data, surviving anchors and full
survivor bases are retained. The children have 64 and 76 Hamiltonian
cycles, and 34 and 40 survivors. Their three port counts are respectively
6,18,10 and 4,22,14. All three types are active.

Each child's brace certificate contains all 900 matching extensions,
not an inference from cut disappearance. These are **low-loss braces**.
Since neither exterior retains $\ell\ge2$, no P4 is attached at 7 and
zero second surgeries are attempted. No (3,3) face is falsely claimed.
This tests two histories, not all 14 choices or all larger prisms.

## 5. A uniform five-port sufficient criterion

This section gives a proved criterion, not an unproved interpolation of
P4/P6/P8 ranks.

### 5.1 Exact path-packing exhaustion

In one of these first children, put in the local side $X$ the punctured
affected $P_k$ and the two new square vertices attached to it.
The exterior $Y$ contains the core minus 0 and the other two square
vertices. The cut has **five edges**, with distinct endpoints on each
side. There are $2k+1$ local and 13 exterior vertices.

For any Hamiltonian cycle the set $J$ of used cut edges is nonempty
and even, hence has size 2 or 4. Its restriction to either side is a
spanning path packing with degree one at the selected cut endpoints
and degree two elsewhere. It has **no isolated cycle**, since that
would be a separate component of the global Hamiltonian cycle.
Its components pair the labels in $J$.

Conversely, take local and exterior packings with the same $J$.
They glue to a Hamiltonian cycle exactly when the union of their two
endpoint pairings is connected. This proves completeness in both
directions, not just a toggle heuristic. For four ports the two pairings
must differ; for two ports the two paths form one circuit.

The protected edge $e$ is one of the five cut edges and $f$ is
internal to the exterior. Survival is therefore exactly:
$e\in J$, or the exterior packing contains $f$.
Filter exterior packings by that predicate. For every compatible
state $s=(J,\pi_X,\pi_Y)$ with both sides nonempty, **all**
local/exterior pairs remain available. Thus the surviving family
is the disjoint union of these actual products.

There are at most
$\binom52+6\binom54=40$ combinatorial compatible states, independent
of $k$. Planarity may reduce their number but is not used to invent
unproved packings.

### 5.2 Actual anchors and the exact dimension formula

Let $\mathcal X_s,\mathcal Y_s$ be the actual nonempty packing families
for the retained states. Embed their within-family differences into
the global edge coordinates and set
$$
W_X=\sum_s\operatorname{diff}(\mathcal X_s),\qquad
W_Y=\sum_s\operatorname{diff}(\mathcal Y_s).
$$
Choose actual packings in each family, glue them to an actual surviving
anchor $c_s$, and fix one state $s_0$. Then
$$
L=W_X+W_Y+\operatorname{span}\{c_s-c_{s_0}\}.
\tag{5.1}
$$
Indeed every product member differs from its anchor by one local and
one exterior difference, and every such difference is realized while
holding the other side fixed. The anchors connect the state classes.
This proves both inclusions.

The supports of $W_X,W_Y$ are disjoint and contain no cut coordinate,
so their intersection is zero. Writing
$$
a=\dim W_X,\quad b=\dim W_Y,\quad
h=\dim\big((W_X+W_Y+\langle c_s-c_{s_0}\rangle)/(W_X+W_Y)\big),
$$
gives the exact formula $\dim L=a+b+h$.
The **actual** anchors are essential; ranks of state counts or freely
translated representative vectors do not determine $h$.

### 5.3 Local kernel/image criterion, valid for every admissible even $k$

Let $B$ be the unsigned incidence matrix of the child and let $\pi$
retain its exterior and five cut coordinates. Its connected local
subgraph has $2k+1$ vertices and $3k-1$ edges. Bipartiteness gives
local incidence rank $2k$. Consequently
$$
\dim(\ker B\cap\ker\pi)=(3k-1)-2k=k-1.
$$
The whole child has $2k+14$ vertices and $3k+21$ edges, so
$\dim\ker B=k+8$ and $\dim\pi(\ker B)=9$.

**Sufficient condition.** If the actual local packing differences
have rank $k-1$, and the projected exterior differences together
with the projected actual anchor differences have rank 9, then
the child has $\ell=0$ and full survivor affine dimension $k+8$.

**Proof.** Equation (5.1) and complete products put $W_X$ inside
$L\cap\ker\pi$. The rank $k-1$ is its entire ambient kernel upper
bound. The projected vectors are realized by surviving differences
and reach the nine-dimensional ambient image. Thus
$$
\dim L=\dim(L\cap\ker\pi)+\dim\pi L=(k-1)+9=k+8.
$$
No lifted independent image combination can belong to the local kernel:
its projection would give a nontrivial relation in the image basis.
This pays the intersection cost. Since
$L\subseteq D_G\subseteq\ker B$, the defect is zero. ∎

More generally, if local within-state rank is smaller, relations among
projected actual anchors can supply extra kernel directions.
Equation (5.1) gives those directions exactly, rather than assuming
they are absent.

### 5.4 Finite verification and the unpaid infinite step

Fresh prescribed-degree packing enumeration on both sides, with
component/pairing tests, reconstructs **exactly** every survivor in all
six finite cases. No ancestor implementation supplies the packings.

| Affected prism, ordinal | Product survivors | States | $a$ | $b$ | $h$ | Image | Kernel | Extra anchor kernel |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| P4, first | 26 | 11 | 1 | 3 | 8 | 9 | 3 | 2 |
| P4, second | 22 | 12 | 1 | 4 | 7 | 9 | 3 | 2 |
| P6, first | 30 | 11 | 5 | 3 | 6 | 9 | 5 | 0 |
| P6, second | 36 | 11 | 3 | 3 | 8 | 9 | 5 | 2 |
| P8, first | 34 | 11 | 7 | 3 | 6 | 9 | 7 | 0 |
| P8, second | 40 | 11 | 7 | 3 | 6 | 9 | 7 | 0 |

The P4/P6 rows are representative contracted I174 constructions;
they are not additional new-surgery scans. Their independent local
packing check is smaller than a repeated historical search.

In particular, the first P6 and both P8 cases satisfy the simple
$(k-1,9)$ criterion. The other three show why dropping actual
anchor relations loses two kernel dimensions. Finite evidence does
**not** prove that all larger even prisms satisfy the rank hypotheses.
An infinite statement still needs explicit independent local
directions for every $k$, and a proof of the corresponding state
availability and projected-anchor image. None is inferred from this
table.

## 6. Exact missing-active-type correction

### Proposition M175

Let $H,A$ be finite simple cubic graphs, spliced at degree-three vertices
by a bijection of incident edges. Label omitted-port types $1,2,3$.
Let $T\ne\varnothing$ be exactly the full exterior types for which
both an exterior Hamiltonian cycle and an attachment Hamiltonian cycle
exist. Let $\mathcal H_T$ be all exterior cycles of these types.
Take a nonempty exterior survivor family
$\mathcal S_H\subseteq\mathcal H_T$, with active set
$\varnothing\ne I\subseteq T$.

Assume the full glued cycle family consists of all compatible pairs,
and the survivor family consists of **all** compatible lifts of
$\mathcal S_H$, with membership determined only on the exterior.
For every $i\in T$, let $\mathcal A_i\ne\varnothing$ be the actual
attachment Hamiltonian class. Define
$K_J=\sum_{i\in J}\operatorname{diff}(\mathcal A_i)$.
Then
$$
\ker(\pi:D_G\longrightarrow\operatorname{diff}\mathcal H_T)=K_T,
\quad
\ker(\pi:L_G\longrightarrow\operatorname{diff}\mathcal S_H)=K_I,
$$
with the natural zero-exterior embeddings, and both maps are onto.
Therefore
$$
\boxed{\ell_G=
  \big(\dim\operatorname{diff}\mathcal H_T-\dim\operatorname{diff}\mathcal S_H\big)
  +\dim K_T-\dim K_I.}
\tag{6.1}
$$
If every full exterior type has a nonempty attachment type,
$\mathcal H_T$ is the full exterior cycle family and the first
parenthesis is the ordinary exterior loss.

**Proof.** Cutting a Hamiltonian cycle gives the exact compatible-path
product, as in S174. Projection is onto each stated exterior family
because a compatible attachment exists for every included type.
In a zero-sum signed combination that projects to zero, let $a_i$
be the totals in each active type, zero outside that active set.
The three cut coordinates say
$\sum_{j\ne i}a_j=0$; together with $\sum_i a_i=0$ they give
every $a_i=0$. The attachment part is consequently a sum of
within-type differences, with no hidden cross-type kernel.
Conversely, fix an exterior cycle in each active type and vary
its attachment through the complete available fibre. This realizes
every summand of the indicated kernel. Rank-nullity proves (6.1). ∎

This proof uses neither attachment affine fullness nor individual typed
fullness. For nonempty $J$,
$$
\dim\operatorname{diff}\Big(\bigcup_{i\in J}\mathcal A_i\Big)
=\dim K_J+|J|-1,
$$
because the actual type-anchor differences have the affinely independent
omitted-port patterns as their images. For $T=\{1,2,3\}$, only the
full $K_T$ may be replaced by $d(A)-2$; replacing $K_I$ by an
assumed ambient typed dimension is unjustified.

Equality of defects holds **if and only if $K_I=K_T$**, since
$K_I\subseteq K_T$. All three active types are sufficient, not
automatically necessary in every graph.

### Small counterexamples and a non-necessity example

- **Drop all active types in the general survivor-family statement.**
  Splice two cubes and keep only the exterior cycles of one omitted-port
  type. This is a genuine cubic planar bipartite graph, and all compatible
  lifts of that predicate are present. Cube full dimension is 5;
  the selected exterior type has dimension 1, so exterior loss is 4.
  The attachment full kernel has rank 3 and its active kernel rank 1.
  The glued graph has full dimension 8, survivor dimension 2 and loss 6,
  agreeing with the correction $+2$. The payload contains every cycle.
  This predicate is **not** a protected two-edge-deletion interface.
- **Drop complete fibres.** On the same cube splice retain one fixed
  attachment per exterior type, lifted over all six exterior cycles.
  All types are active, but the restricted family has dimension 5
  instead of the full glued dimension 8. Exterior loss is zero while
  glued loss is 3. The missing attachment variations are the reason.
- **All three need not be necessary.** In the general cubic scope of
  S174, the tetrahedron $K_4$ has three singleton port classes and
  $K_T=0$. Every nonempty proper active subset also has zero kernel,
  so complete-fibre defect equality still holds. This is nonbipartite
  and is not advertised as an admissible high-loss target.

A bounded additional check searched the actual port spaces of the
index-431 and C171 attachment graphs for a two-type subset generating
the whole kernel; it found none. No necessity theorem follows.

## 7. Can a protected planar interface exploit missing types?

### Local forcing lemma A175

Suppose an admissible graph has protected disjoint deletions $ab,cz$,
and $z$'s neighbors are $b,c,d$, with $a,b,z,d$ distinct.
Define survivors as Hamiltonian cycles using at least one deletion.
Then all three omitted-port survivor types at $z$ are nonempty.

**Proof using the stipulated theorem.** Each of the two types using
$cz$ is specified by a two-edge path through $z$. Extend that path
to a simple three-edge path, possible in a simple cubic bipartite graph,
and apply `cor:pfaffian-paths`. The resulting cycle uses $cz$ and
the required two incident edges, so it is a survivor of that type.
For the type omitting $cz$, apply the theorem to the actual simple
path $a-b-z-d$. It uses $ab$ and the other two edges at $z$.
It too is a survivor. ∎

Here $a=20,b=6,z=7,c=1,d=8$. The path $20-6-7-8$ is present
before and after the two tested surgeries. More generally the same
proof applies to any admissible protected repair retaining this local
configuration. This is a genuine obstruction in the required planar
class, not just formal affine algebra.

For a bounded boundary test, all canonical admissible cofacial deletion
pairs on P4, P6 and P8 were considered, with every splice vertex outside
the four deletion endpoints. There are **720 interface/vertex records**
and **zero missing-active-type records**. These are boundary tests,
not further prism-surgery experiments. They do not exclude missing
types at arbitrary more remote protected interfaces in all admissible
graphs.

Thus the abstract correction is real, but there is no demonstrated
protected admissible interface exploiting it here. The local configuration
at 7 rules out that escape altogether while it is retained.

## 8. Validation and sealed-evidence protocol

Authoritative code is in
`frontier/experiments/i175_affected_prism_exterior/`.
Only standard-library Python under `-I -B` is used.

- Hamiltonian cycles: complete perfect-matching complements plus connectivity,
  checked against independent rooted path DFS on mandatory and new graphs.
- Path families: prescribed-degree enumeration, component/pairing tests,
  and endpoint DFS comparisons for the one-path families.
- Ranks: gcd-normalized integer elimination with ascending pivots versus
  sparse exact `Fraction` elimination with descending pivots.
- Embeddings: oriented darts, single vertex links and Euler characteristic,
  plus graph simplicity, cubicity, bipartition and all two-vertex deletions.
- Brace certificates: explicit perfect matching for every disjoint edge pair.
- Five-port products: fresh local/exterior degree enumeration, no isolated
  cycles, actual pairing compatibility and equality with the full survivor set.

All development source stages, successful and failed payloads, rejected
rotation, and **empty** captures are retained. The two failed mathematical
development runs are the field-convention and coordinate-schema errors
described above. They are not hidden or replaced by the later successes.

The complete immutable-first inventory binds the final report, every
owned input/output/source-stage file, primary-literature receipt and
authenticated ancestor chain before final diagnostics. Only
`inventory.json`, `prevalidation.json`, `seal.json` are non-self-hashed
controls. All used external mathematical inputs are bound; only the
four named shared ledgers are contexts.

The verifier authenticates every byte into immutable memory before
compiling only the exact owned `math175.py` and `research175.py` byte
strings. Ancestor executables remain opaque. The five deterministic
replays are mandatory witnesses, historical certificates, the bounded
experiment, missing-type boundary, and local saturation.
Every replay must be byte-identical to its final retained payload.

Eight live probes require blocking write, mutation, network, subprocess,
unbound read, outside compilation, outside execution and forged bytes
under an owned source filename. Before/after checks cover all bound
bytes, complete owned file membership, controls and current contexts.
The order is complete inventory, successful prevalidation, **one exclusive
seal**, then read-only sealed replay. No source/report edit or reseal
is permitted afterwards.

Replay command:

```text
python3 -I -B /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/experiments/i175_affected_prism_exterior/verify175.py
```

Detached report/seal/verifier hashes, actual inventory counts and replay
runtime are returned outside this report to avoid circular bindings.
The Python audit guard is **not OS sandboxing**; interpreter and
standard-library behavior remain runtime dependencies. Clean-clone
reconstruction was not tested.

## 9. Limits, unresolved objections and concrete next step

The literature queries and primary-source leads are recorded in
`frontier/sources/i175_affected_prism_exterior/literature.md`.
Only selections/metadata were returned, not full primary proofs.
Neither the affine formula nor the local criterion receives literature
priority or substantiality clearance from that search.

D168's bounded bidirectional-transfer obstruction, M168's typed-fullness
counterexample, $\rho(L)=\mathbb Q^2$, the failed containments involving
$V$, isolated-cycle toggle failures, and C171's distinction $F\ne T$
remain binding. S172 remains a remote-decoration result.
S174/M175 do not cover internally defined survival, restricted fibres,
or operations breaking the splice cut.

No genuine high-loss brace was found. On the two low-loss braces the
computed $\delta_V,\delta_R,\epsilon,\eta$ are all zero; the desired
lower bound and exchange are therefore vacuous there. Universal square
exclusion, the substantive brace lower bound
$\delta_R\ge\delta_V+\epsilon-1$, exchange
$\delta_R+\eta\ge\delta_V+\epsilon$, (T), Q164 and the high-loss brace
target remain open.

**Concrete next step:** attack the unpaid local-rank step analytically,
not by sweeping larger prisms. For the first canonical surgery
`[0,0,6]`, work with its at-most-40 five-port states and fixed
13-vertex exterior. Construct $k-1$ explicitly independent local
packing differences for every even $k\ge6$, with common compatible
surviving exterior partners, and nine independent projected directions
using the actual anchors. A strip-extension recurrence must verify
state availability, connected pairings and the new independent local
directions; the exceptional P4 anchor correction cannot be ignored.
Success would prove a genuine uniform obstruction for this surgery
family. Failure would identify a specific missing local direction or
state, rather than encourage an unsupported larger-prism search.
