# I164: structural graph discovery, sharp linear multiplicity remains open

Date: 2026-10-10. Author research, Factory/Astra. **GAP REPORT, not an acceptance recommendation.**

## 1. Outcome and exact residual target

Write $\mathcal B$ for the finite simple undirected **cubic, bipartite,
planar, 3-vertex-connected** graphs. Count Hamiltonian cycles as edge
sets, without orientations or starting points. The one residual target is

$$
\tag{Q164}
\forall G\in\mathcal B,\qquad
h(G)\ge |V(G)|/2+2.
$$

**Q164 is unproved and unrefuted here.** This is a research question,
not a claim that the literature leaves it open. No full-scope classical
reduction was established, and no worldwide-priority certification is
made. Its plausibility is supported by exact sharp prism examples and
bounded tests, not by a general proof.

The developed approaches are:

1. **Structural counting and affine-span approach.** Prove an exact
   four-terminal counting identity for the classical square expansion;
   reduce its monotonicity to a concrete uncompensated family of lost
   cycles. Prove the easy cube/splice part and a restricted induction.
   An independent affine-rank formulation identifies the missing global
   exchange information, rather than treating local pattern coverage as
   linear independence.
2. **Signed paired-state approach.** Extract a rigorous
   $c_{\min}+1$ lower bound on surviving forest states from the actual
   source exponential sum, prove injectivity into fixed-edge-avoiding
   Hamiltonian cycles, and show explicitly why this can stay constant
   on arbitrarily large prisms.

All positive bridges below are author-level deductions with written
proofs, not independently reviewed results. Their contribution is
**technical/supporting**: the reductions are given below at their full
claimed scopes. None proves Q164. The original two failed prism
diagnostics are retained separately from the corrected passing run.

No shared ledger, acceptance count, sibling output, or prior evidence was
changed. No children were spawned, and nothing was staged, committed,
or published. This does not duplicate I161/I163 or reopen I05/I07.

## 2. Source contracts and early primary comparison

### Stipulated corpus

All results **and lower proof operations** of
`openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are premises.
There is no upstream audit or ex-falso argument.

The operative manuscript is
`preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/build/paper.tex`.
It was read in full, lines 1–838, including the proof endings.
`build/references.bib`, lines 1–151, was also read.
The owned copies and exact immutable raw URLs, SHA-256 values, Git blob
identities, and original cache locations are in
`frontier/sources/i164_structural_graph_discovery/contracts.json`.
Each copied blob was compared with the complete `sources/preprints-tree.json`.
No corpus-building or ancestor script was executed.

Exact interfaces:

| Label | Original lines | Contract used |
|---|---:|---|
| `thm:main` | 79–82; 760–792 | Every graph in $\mathcal B$ is Hamiltonian. |
| `thm:partition` | 208–237; 725–758 | A simple sphere triangulation with properly black/white-colored faces admits two induced trees, prescribing the same-label edge at **one** facial triangle. |
| `prop:pairs` | 239–345 | With no separating triangle, two disjoint incidence states exist, via the stated capacity-two flow. |
| `lem:disk` | 347–403 | The signed circulation is $\pm3$ for directed cycles made from a state; not for arbitrary cycles. |
| `prop:forest-state`, `lem:cancel` | 405–483 | Fixed-second-state cancellation removes cyclic opposite-edge subgraphs. |
| `lem:circulation`, `eq:group-product`, `eq:leading-coefficient` | 485–589 | Positive spoke circulations give exact vanishing order $c_{\min}$ for the finite exponential sum. |
| `lem:root-components`, `lem:P-forest` | 591–718 | Rooted forest, white-face tree, selected-edge forest, complementary Hamiltonian cycle. |
| `cor:edge-avoidance` | 794–805 | Avoid any one specified edge. |
| `cor:pfaffian-paths` | 807–828 | Every three-edge path in every finite simple cubic, 3-connected, **Pfaffian bipartite** graph extends to a Hamiltonian cycle. Planarity is not required for this interface. |

The stronger Pfaffian/path consequence is already explicit, not an I164
discovery. Separating-triangle assembly retains one prescription; it
does not promise independent prescriptions at many triangles. The source
expressly uses its finite weighted sum for existence, not for a
polynomial-time construction (168–170).

### Bounded companion screening

Read `AGENTS.md`, `sources/upstream.json`, catalogue entries 173, 180, 181,
and the current opening/status sections of `TEN-FINDINGS.md` and the
iteration README. Their full current bytes were frozen for context, not
as mathematical dependencies.

The complete flat original-position map supplied by I160 was used to
screen **8,791 `.tex`/`.md` corpus bindings**, including ignored files.
Patterns and complete hit lists are in `screen.json`.
`Barnette`, `P_4...Hamilton`, and the relevant three-edge-path hit point
back to this family; one three-edge-path hit is unrelated
Kazhdan–Lusztig text. The broader Pfaffian screen also returned unrelated
analytic/algebraic manuscripts. This is lexical coverage, not an
exhaustive semantic review of 749 manuscripts or all PDF contents.
The full family-180 body and the primary companions below were actually
read. No claim of exhaustive semantic absence in old iterations is made.
Families 173 and 181 were not developed: family 180 retains a concrete
residual question after screening, so the conditional permission to
pivot was unnecessary.

### Primary literature read before developing Q164

1. Gorsky–Steiner–Wiederrecht, *Matching Theory and Barnette's
   Conjecture*, arXiv:2202.11641v3, published in Discrete Mathematics
   346 (2023), 113249.
   `gsw2023.txt` 288–607: Theorems 4.3, 4.4, 4.16, Lemmas 4.5, 4.12,
   the Pfaffian trisum interface and proof endings.
   Lines 657–708: square/cube expansions and Theorem 5.1.
   The three-edge-path statement is a **published equivalence** of
   Barnette, with explicit gluing operations. It is not new even though
   its quantifiers look stronger. The discussion at 402–416 explicitly
   warns that four-edge-path extension fails.
2. Björklund–Kaski–Nederlof, *Another Hamiltonian Cycle in Bipartite
   Pfaffian Graphs*, arXiv:2308.01574v2 (2024).
   `another2024v2.txt` 1–320, 680–869, 1130–1194.
   Corollaries 4–5 already give at least four cycles through each
   Hamiltonian edge and at least six cycles in the cubic case.
   Theorem 1's switching retains a local edge choice; repeated switching
   is **not** proved to reach every needed edge (161–179).
   The perfect-matching representation has exactly
   $2^{n/2-1}$ port-labelled matchings per represented cycle (753–757),
   so counting those witnesses without dividing the fibre is invalid.
   The six/four-cycle baselines are independently rederived from the
   stronger stipulated path interface below; no unread recursive
   dependency of this external algorithm is used as a new proof step.
3. Goedgebeur–Meersman–Zamfirescu, *Graphs with few Hamiltonian
   Cycles*, arXiv:1812.05650v2 (2019).
   `few2019.txt` 830–894: prisms as classical few-cycle examples;
   cyclically 4-edge-connected **non-bipartite** planar cubic families
   with four cycles. Their scope cannot be silently transferred to
   $\mathcal B$. This already made an unrestricted exponential claim
   untenable; the exact bipartite prism count is proved below.
4. Holton–Manvel–McKay, *Hamiltonian cycles in cubic 3-connected
   bipartite planar graphs*, JCT B 38 (1985), 279–297.
   Original author-hosted scanned PDF `hmm1985.pdf`, visually read:
   printed pp. 280–284 (local reductions/expansions), 294–296
   (Theorem 4 and proof, computed pattern properties and counterexamples).
   Theorem 4 supplies the cube/square generation theorem used below,
   as restated precisely by GSW Theorem 5.1.
   Page 295 already reports failure of arbitrary two-edge avoidance on
   a 12-vertex example and failures of stronger simultaneous patterns.
   The PDF's automatic text extraction is empty; `hmm1985.txt` retains
   that outcome, and no machine-text reading of it is claimed.

The PDFs, successful URLs, hashes and failed request are retained.
An initial request for nonexistent `2308.01574v3` returned HTTP 404;
v2 was fetched separately. Search queries included exponential/linear
multiplicity, exact-six-cycle questions, prescribed paths, and affine
spans. They do **not** establish worldwide absence of Q164 or of a
classical reduction. A secondary Florek exponential-multiplicity lead
was not verified in a primary source and supplies no premise here.
No MathDB featured/ranking evidence was retrieved; no numerical
importance score or MathDB certification is asserted.

## 3. Exact baselines and genuine obstructions

### 3.1 What the existing path interface already pays for

At an edge $uv$ of a cubic bipartite graph there are four three-edge
paths $xuvy$, with $x\in N(u)\setminus\{v\}$ and
$y\in N(v)\setminus\{u\}$. All four vertices are distinct. The four
extension families are disjoint, since a Hamiltonian cycle containing
$uv$ makes exactly one of the two other choices at each endpoint.
Thus the source gives **four cycles through every edge**.

To avoid an edge $vz$, force the other two edges $vu,vw$, and
extend at $u$ in its two different ways. These are two distinct
three-edge paths and two disjoint extension families. Therefore at
least two cycles avoid every edge. At a fixed vertex, partition cycles
by its omitted incident edge: **$h(G)\ge6$**. This proof works for
the full source Pfaffian class, not merely planar graphs.

Equivalently, there are $6n$ undirected three-edge paths, and each
Hamiltonian cycle contains $n$ of them; incidence counting gives
only six. Neither that coverage calculation nor repeated gadget
replication yields the $n/2+2$ target.

### 3.2 Even prisms: a complete count, not extrapolation

For even $m\ge4$, let $L_m=C_m\square K_2$, with vertices
$a_i,b_i$, subscripts modulo $m$, rim edges
$a_i a_{i+1},b_i b_{i+1}$, and rungs $a_i b_i$.
This graph is simple, cubic, bipartite and planar. It is 3-connected:
if two deleted vertices lie on one rim, the other rim and surviving
rungs connect every remaining rim segment; if they lie on different
rims, both remaining rim paths are linked by at least $m-2$ rungs.
The cases of fewer deletions are immediate.

**Proposition P.** $h(L_m)=m+2=|V(L_m)|/2+2$.

Proof. Let $S$ be the columns whose rungs a cycle uses. On each rim
the omitted edges form a matching with vertex set exactly $S$.
If $S$ is nonempty and proper, its consecutive runs must be even,
and each run has a unique perfect matching. The two rim omission
matchings therefore coincide. If that matching has $r$ edges, the
remaining graph consists of $r$ ladder-boundary cycles; it is
Hamiltonian precisely when $r=1$.
This gives the $m$ cycles $H_i$ obtained by omitting the two rim
edges at index $i$, retaining all other rim edges and just rungs
$i,i+1$. If $S$ is empty there are two separate rim cycles.
If $S$ is all columns, each rim has one of its two perfect matchings
omitted. Equal choices give $m/2$ disjoint squares; opposite choices
give exactly two Hamiltonian cycles, denoted $A,B$, using all rungs
and alternating opposite rim parities. These exhaust the cases. ∎

Consequences, in the original graph class:

* No universal bound $h(G)\ge \exp(c|V(G)|)$, $c>0$, is possible.
* The three-edge path
  $P_i=b_i a_i a_{i+1} b_{i+1}$ has **exactly one** extension, $A$
  or $B$ according to $i$'s parity. No uniform growth of
  prescribed-$P_4$ multiplicity is possible.
* Choose even $m\ge10$ and odd $j$ with $5\le j\le m-5$.
  $P_0,P_j$ are disjoint and have no common Hamiltonian extension,
  although they lie in a common spanning 2-factor: take the squares at
  columns $0,1$ and $j,j+1$, and the ladder-boundary cycles on
  the intervals $2,\ldots,j-1$ and $j+2,\ldots,m-1$.
  Both intervals contain at least two columns. Taking $j$ near
  $m/2$ makes the distance between the patterns arbitrarily large.
  Thus distance, degree feasibility, and even a supplied common
  2-factor do not suffice.
* Delete top-rim edges at indices $0$ and a distant odd $j$.
  Each $H_i$ avoids only one top edge, and $A,B$ each avoid only
  one parity. No Hamiltonian cycle survives. These are disjoint
  defects in a graph of the required class, not an application of
  Barnette to the now noncubic deleted graph.

The counting example and two-edge obstruction are classical in spirit
and partly explicitly anticipated by HMM. They are not findings to
count. The simultaneous-pattern proof above is a scoped obstruction,
not a characterization of all compatible patterns.

## 4. Approach A: classical expansions, with the lost mass exposed

### 4.1 Splices and cube expansions really are routine

Splice $G_1,G_2\in\mathcal B$ by deleting vertices $v_1,v_2$ and
matching their three incident ports in a planar, bipartition-compatible
way. Let $a_i,b_i$ count cycles in the respective pieces omitting
port $i$, for $i=1,2,3$. A Hamiltonian cycle in the splice crosses
the three-edge cut exactly twice. Restriction and gluing give the
**bijection**

$$
\tag{1} h(G_1\star G_2)=\sum_{i=1}^{3}a_i b_i.
$$

Each $a_i,b_i\ge2$ by §3.1. In particular, since each port count
in the cube is two, a cube expansion **doubles** $h$, while adding
six vertices. This preserves Q164 whenever the old graph satisfies
it. More generally, if both pieces satisfy Q164, then
$a_i b_i\ge a_i+b_i$, so
$$
h(G_1\star G_2)\ge h(G_1)+h(G_2)
\ge(n_1+n_2)/2+4>(n_1+n_2-2)/2+2.
$$
This is exactly the known cut-gluing operation with its fibres counted.
It cannot be promoted into a substantial exponential-multiplicity
theorem for all graphs, because graphs need not have many such cuts.

### 4.2 Exact square-expansion identity

Use the precise GSW square expansion. In a facial cycle of
$G\in\mathcal B$, take disjoint edges $e=uv,f=xy$ with boundary
order $u,v,\ldots,y,x,\ldots,u$, $u,y$ in one bipartition class,
and the two paths left by deleting $e,f$ odd.
Replace them with arms $up,vq,xr,ys$ and square edges
$pq,qs,sr,rp$, producing $G'\in\mathcal B$ with four new vertices.
Let $K=G-\{e,f\}$, and define:

* $N_{00}$: Hamiltonian cycles of $G$ avoiding both $e,f$;
* $P_{ux}$, $P_{vy}$: spanning simple paths in $K$ with the
  indicated endpoint pairs, counted without orientation;
* $D_{11}$: spanning 2-factors of $G$ with exactly two components,
  using both $e,f$, with these edges in different components.

**Proposition E (proved).**

$$
\tag{2} h(G')=h(G)-N_{00}+P_{ux}+P_{vy}+D_{11}.
$$

Proof. Intersect a cycle with the four arms. It uses two or four.
It cannot use zero, which would isolate the square.
With two arms, the square portion is its unique spanning path
between adjacent corners. The endpoint pairs $u,v$ and $x,y$
correspond bijectively to old Hamiltonian cycles using just $e$
or just $f$. The other adjacent pairs $u,x$ and $v,y$
correspond bijectively to the two displayed spanning-path families.
Opposite square corners cannot be endpoints of a spanning square path.

With four arms, the square contributes one of its two perfect
matchings. The exterior must be two vertex-disjoint paths covering
the old vertices. Since the terminals are cofacial, the crossing
pairing $(u,y),(v,x)$ is impossible: close the removed face to a
disk and apply the Jordan separation of disjoint arcs in the other
disk. The two remaining exterior pairings are
$(u,x),(v,y)$ and $(u,v),(x,y)$.
In each case exactly one of the two square matchings joins everything
into one cycle; the other closes two components. The first exterior
pairing corresponds to an old Hamiltonian cycle using both $e,f$;
the second to a member of $D_{11}$. All restrictions and extensions
are inverse and edge-set preserving outside the square.
These disjoint cases account for every cycle and prove (2). ∎

The old $N_{00}$ cycles have no local spanning extension that keeps
their old edges: all old vertices already have degree two and no arm
can be used. Thus “every cycle lifts, plus two more” is not a proof.

The source does imply separately
$$
\tag{3} P_{ux}\ge1,\qquad P_{vy}\ge1,\qquad D_{11}\ge1.
$$
For the first, prescribe the three-edge path $u p q s$ in $G'$.
Cubicity forces $sr,rx$: choosing $sy$ instead would leave $r$
with only one available incident edge. The exterior is a spanning
$u,x$-path. Symmetrically use $v q p r$ for the second.
Prescribe $u p r x$ for the third; the other square corners must
use $qs,vq,ys$. Noncrossing and connectedness force the exterior
pairing $(u,v),(x,y)$, giving exactly the two components of $D_{11}$.
This is a direct use of the already-paid $P_4$ interface.

Hence (2) proves $h(G')\ge h(G)+3-N_{00}$.
In particular, **Q164 holds along every cube/square construction
sequence whose square steps have $N_{00}\le1$**. Start with the
cube, which has six cycles; cube steps double the count and square
steps add at least two. This restricted statement is a technical
consequence of the classical operations plus source $P_4$, not a
substantial nomination.

### 4.3 The actual unpaid counting step

HMM Theorem 4 supplies construction sequences for the full class,
but does not supply the restriction $N_{00}\le1$.
A sufficient full induction would prove, at every admissible step,

$$
\tag{M}
P_{ux}+P_{vy}+D_{11}\ \ge\ N_{00}+2.
$$

This is stronger than bare Q164 and is **not established** here.
I tried the natural extension map; it loses the entire $N_{00}$
family. Source-prescribed paths supply three nonempty families, not
an injection from the lost family or a comparison of their sizes.
Generic gadget replication changes the graph and repeats these
fibres; it does not fix this same-graph deficit.

The 198 tested admissible square expansions all had gain at least two.
They are expansions of seven selected small examples, not all Barnette
graphs or even all graphs of those orders. This is evidence for trying
(M), not evidence that it has been proved.

### 4.4 A distinct diagnostic within the structural approach: affine rank

Let $B$ be the unsigned vertex-edge incidence matrix of a connected
bipartite cubic graph with $n$ vertices and $3n/2$ edges.
Its row rank over $\mathbb R$ is $n-1$: a row dependence satisfies
$\alpha_u+\alpha_v=0$ on every edge, and connectedness leaves exactly
one scalar, with opposite values on the two bipartition classes.
Consequently
$$
\dim\{z:Bz=2\mathbf1\}=3n/2-(n-1)=n/2+1.
$$
If Hamiltonian-cycle incidence vectors affinely span this space,
Q164 follows, since an affine space of dimension $d$ needs at least
$d+1$ points.

The exact missing assertion is: if an edge weighting has the same
total on **every** Hamiltonian cycle, must it have the form
$w_{uv}=\alpha_u+\alpha_v$?
This is stronger information than extension of each three-edge path.
It is an unproved criterion, not a lemma claimed as progress on its
own. Exact rational elimination verifies full rank on the seven prism
orders and the seven selected search minima. It does not establish
the criterion in general. In particular, neither source cancellation
nonvanishing nor the external one-switch algorithm proves that its
available differences span all of $\ker B$.

## 5. Approach B: what the actual signed-state sum can count

Work with exactly the source setup: a properly face-two-colored simple
sphere triangulation $T$, **no separating triangle**, fixed outer
black face $t_0$, three roots, nonroots $X$, and ordered disjoint
states $(r,s)$. For each undirected union $D$ of their chosen
edges, let $c(D)$ be its number of cycles and
$c_{\min}=\min_D c(D)$. Let $F$ be the set of second states having
a partner and with $Q_s$ a forest.

**Proposition S (proved under the exact source operations).**
For any prescribed outer edge $e_0$, the construction yields
at least $c_{\min}+1$ different complementary Hamiltonian cycles
avoiding $e_0^*$. Moreover
$$
\tag{4} h(T^*)\ge 3(c_{\min}+1).
$$

Proof, including witness fibres:

1. A forest second state has a **unique** partner. Orient each edge of
   $Q_s$ from the first state's choice toward its third corner.
   Source `lem:root-components` puts one root in each tree component;
   every nonroot has outdegree one. Such an orientation must point
   toward its root: following successors in a finite tree cannot
   cycle or stop at a nonroot. It is unique. Black-face ownership of
   edges then recovers every $r(t)$.
2. After the source fixed-$s$ cancellation,
   $$
   Z(x)=\sum_{s\in F}\alpha_s e^{x\omega(s)},\qquad
   \alpha_s=i^{J(r,s)}\ne0.
   $$
   Its exact order of vanishing at zero is $c_{\min}$, by the
   source positive-circulation product and leading-coefficient
   argument, not merely by existence of some nonzero value.
3. Collect equal real exponents and discard any zero combined
   coefficients, leaving $q\le|F|$ distinct exponents. A nonzero
   sum of $q$ exponentials with distinct exponents has vanishing
   order at most $q-1$. Otherwise its first $q$ derivatives
   give a Vandermonde linear system with nonsingular determinant
   $\prod_{i<j}(\lambda_j-\lambda_i)$, forcing all coefficients
   to vanish. Hence $|F|\ge c_{\min}+1$.
4. The source output does not hide another multiplicity loss:
   from the complementary Hamiltonian cycle recover its selected
   dual forest $P$, then remove the fixed $e_0$.
   The resulting rooted forest $P_0$ has one root in each
   component. Orienting it toward the roots recovers $s(t)$ as
   the tail of the selected edge owned by black triangle $t$.
   Thus different $s$'s give different cycles.
5. Run the recovery with each of the three choices of $e_0$ in
   the same $t_0$. Each cycle omits exactly one of the three edges
   at the corresponding primal vertex. These three families are
   disjoint and have the same $F,c_{\min}$, proving (4). ∎

This is a complete supporting deduction, but the novelty operation is
only elementary Vandermonde rank and explicit inversion of the source
rooted-tree maps. A new quantitative theorem cannot be claimed just
because the manuscript originally used the sum for existence.

### Why this does not scale to Q164

The dual of $L_m$ is the even bipyramid with rim $0,\ldots,m-1$
and apices $a,b$. Choose outer black face $(a,0,1)$.
The other black faces are
$(a,i,i+1)$ for even $i\ge2$, and $(b,i+1,i)$ for odd $i$.
Its state incidence graph, after suppressing face names, is the
alternating chain of rim vertices $2,\ldots,m-1$, with apex $b$
available at the odd faces.

There are exactly $m/2$ states: choose the odd face assigned to $b$;
the two remaining chain portions then force all rim assignments.
Two such states differ only on the interval between their choices
of the $b$-face. To differ at **every** face, those choices must be
the two terminal odd faces, $1$ and $m-1$.
Thus there are exactly two ordered disjoint pairs. Their union $D$
is the one cycle on $b,2,\ldots,m-1$, so $c_{\min}=1$.
Their opposite-edge graphs are rooted forests (also follows from
source nonzero order one plus the two available second states).
Hence $|F|=2$, independent of $m$.

The rooted signed-state count therefore yields only six cycles,
whereas the exact count is $m+2$. This obstruction is inside the
actual class and actual source state construction, not an arbitrary
signed-sum countermodel. Varying weights at this fixed root cannot
manufacture additional forest states. Varying the outer root may
produce more cycles, but summing such witnesses without controlling
overlap is not a proof. No root-by-root de-duplication or independent
global exchange argument closing that gap was obtained.

## 6. Finite evidence, failures, and reproducibility

Owned experiment directory:
`frontier/experiments/i164_structural_graph_discovery/`.
Owned source directory:
`frontier/sources/i164_structural_graph_discovery/`.

* `explore.py` and `discovery-01.json`: deterministic labelled search
  using an anchored cycle plus an opposite-bipartition perfect matching.
  Chord crossings must be two-colorable, certifying an inside/outside
  planar embedding; deletion of every set of up to two vertices checks
  3-connectivity. Perfect matchings are enumerated recursively and their
  connected complements counted. The small-order permutation loops
  are exhaustive **in this anchored encoding**, not an isomorph-free
  enumeration claim. Larger orders use 30,000 seeded trials each.
  Accepted distinct encodings at orders
  $8,10,12,14,16,18,20,24$ number
  $2,0,8,28,30,30,13,2$, respectively (113 total).
  Observed minima where nonempty are $6,8,12,10,16,20,32$.
* `expansion_probe.py`, `expansion-discovery-01.json`: 198 facial,
  parity-compatible expansions of the seven selected minima; minimum
  gain two. This is bounded, deliberately not an exhaustive search of
  expansion monotonicity.
* `state_probe.py`, `state-discovery-01.json`: all states and pairs
  of even bipyramids for $m=4,6,\ldots,20$; exactly two forest
  second states, unique partners, $c_{\min}=1$.
* `diagnostics_v3.py`, `diagnostics-03.json`: seven prism counts and
  affine ranks; 1,680 directed three-edge-path checks; four full
  boundary identities (2); 465 exact Vandermonde rank checks;
  corrected simultaneous-pattern and deletion counterexamples.
* **Retained failed attempts:** `diagnostics.py` used same-parity
  paths at $m=8$, so its incompatibility assertion failed.
  `diagnostics_v2.py` fixed parity but incorrectly asserted a common
  2-factor at $m=8$, where a singleton leftover column blocks it.
  Both tracebacks and both resolution notes are retained. V3 restricts
  the stronger compatibility example to $m\ge10$, as proved above.
  Neither old run is relabelled a PASS. An optional `networkx` import
  probe failed; the implementation and replay use the standard library.

The one canonical inventory is `owned-files.json`; it lists every owned
file except itself and `seal.json`, including this report, failures,
source copies, verifier, and the prevalidation record. The seal binds
the inventory and is created with exclusive-create **after** successful
prevalidation. It is not regenerated or corrected in place.

Replay command, from any working directory:

```sh
python -I -B /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/experiments/i164_structural_graph_discovery/verify.py --replay
```

Replay is read-only, bytecode-disabled, standard-library only, with an
audit hook denying writes, subprocesses, and network. It executes only
the explicitly owned I164 diagnostic modules, never ancestor code.
It reproduces the seeded discovery JSON, the state and expansion
diagnostics, the corrected exact checks, and the two expected historical
failure locations. It validates source blob identities and the
inventory/seal. PDF-to-text extraction was done during preparation;
replay checks bytes, not a subprocess re-extraction. Likewise, lexical
coverage is a frozen recorded search, not a full-corpus replay or a
semantic completeness gate.

**These are finite/provenance checks, not a universal mathematical proof
gate, human peer review, formal verification, or acceptance.**

## 7. Contribution verdict and concrete next action

* **Main target Q164:** GAP, neither proved nor refuted.
* **Source strengthening screen:** $P_4$/Pfaffian extension is
  already paid by the source and published equivalence; six total/four
  through an edge/two avoiding an edge are technical or classical.
* **Positive bridges:** (1), (2), (3), restricted construction-sequence
  induction, and (4) have complete author proofs. They are technical
  operations, not substantial findings. The full Q164 contribution
  cannot be declared technical-only without actually proving a
  full-scope reduction; none is supplied.
* **Rejected shortcuts:** universal exponential multiplicity,
  growing multiplicity through an arbitrary $P_4$, independent remote
  pattern extension, arbitrary two-edge resilience, all-cycle local
  lifting, witness counting without fibre correction, and root-wise
  counting without de-duplication.
* **Remaining gap:** a same-graph quantitative comparison, not
  existence of a cycle or ability to choose one short local pattern.

**Next action:** investigate inequality (M) for one admissible square
expansion. Seek an explicit injection from cycles avoiding both removed
edges into the three boundary families with two unused outputs, or a
counterexample to that inequality. Retain the exact noncrossing/parity
interface of (2); test graphs with large $N_{00}$, not just the seven
minimum-count representatives. A counterexample to (M) would invalidate
that induction, not Q164. A proof of (M) would first require a renewed
primary comparison against HMM-style counting/gadget arguments before
being treated as a substantial contribution.

Return this as research to the parent. Acceptance remains eight; this
report neither changes that count nor recommends adding one.
