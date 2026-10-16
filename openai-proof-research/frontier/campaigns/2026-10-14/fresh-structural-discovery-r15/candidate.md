# Linear intersecting covering obstruction: structural discovery r15

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party materials remain
private and retain their original rights.

**UNRESOLVED_FULL_LR.** No finite witness and no universal impossibility
proof was obtained. The full frozen target remains unchanged. This round
has two complete construction-obstruction checkpoints, not a substantial
result nomination. There is no independent mathematical/contribution PASS,
manuscript, Lean package, acceptance or count increase. The campaign stays
4/10. FT2 was not reopened, and no excluded family was continued.

## Exact assertion and stipulated source

LR asks for ONE integer r>=2, pairwise disjoint finite parts V_1,...,V_r,
and a nonempty set E of edges such that every edge meets every part once,
EVERY two distinct edges meet in EXACTLY ONE vertex, and EVERY vertex set
of size<=r-1 misses some edge. Equivalently, the finite hypergraph is
r-partite, r-uniform, linear and intersecting, with tau=r. Any edge gives
the upper bound r. No rank, field, edge count, side size, degree or model
restriction is part of LR. A refutation must prove tau<=r-1 for EVERY
finite linear intersecting partite hypergraph, not one construction class.
The scope was frozen before sustained work in original-scope.md, SHA256
`dc98c7a1b62d7a44ead17140b057e82fdfc5e42083c01b3f679fcf3782e4345c`.

Pinned source family162, at openai/math
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, provides the distinct family.
The balanced manuscript thm:main gives tau=r=q+1 with r nonisolated vertices
in each part, for every sufficiently large PRIME q. The extension-field
companion thm:main has q=s^n for sufficiently large prime s congruent2mod3
and every sufficiently large odd n, with threshold depending on s; it does
not assert balance. Both permit multiple intersections and already contain
the ordinary monochromatic tree-cover transfer. Their truth is stipulated,
not audited. The exact deterministic balanced construction and its full
proof were read. Exact path/blob identities and reading extents are in
source-contracts.md and inputs/pinned-records.json.

The operation chosen BEFORE sustained work was simultaneous partition
refinement to remove duplicate pair agreements. Refinement preserves the
cover lower bound: any cover by refined blocks maps to at most as many
original blocks. But intersection must survive every split, and each
part's equal-label relation must remain transitive. Choosing one shared
color for each pair does not enforce that transitivity. The primary fair
detachment theorem balances degrees and edge multiplicities, without this
pairwise-intersection condition. Thus that condition is a real unpaid
operation, not an already paid transformation. The work below proves that
this tempting lift cannot work for the actual balanced source.

## Checkpoint1: the entire source has no linear intersecting refinement

Write A=F_q^2. In every direction d the source merges two constituent lines
M_d^0,M_d^1, splits two other parallel lines into opposite pairs of four
designated points each, and keeps ordinary line blocks elsewhere. Let S be
all split lines, R=A minus their union, and X=R union their designated
points. Compatibility gives S0 intersect X equal to its four designated
points for each split line S0. At most B constituents pass through any
point. Occupancy supplies at least rho*q points of X on EVERY nonsplit
line, including both constituents; each constituent also meets R. The
source requires rho*q>2(1+B). For its main construction B=ceil(log q).

Here is the full obstruction argument. On X intersect a nonsplit line L
of direction d, join pairs whose original edges have exactly one agreement.
Each pair already agrees in d. An additional agreement in h!=d can only
come from different constituents of the merged h-block. For a fixed point
a on L, at most B such h-constituents contain a, and each partner line
meets L at most once. Hence a has at most B nonneighbors. A graph on
n>2B vertices with that property is connected: each component would have
size>=n-B, and two components would imply n>=2(n-B), a contradiction.

Intersection-preserving refinement must retain every unique agreement in
its original part, since it cannot create other agreements. Transitivity
along these paths forces all X intersect L into one refined d-block.
This applies to every nonsplit line, including each constituent individually.
If a refined d-block identifies ANY point on the two different constituents,
it therefore identifies both entire retained constituent sets. Choose
x in R intersect M_d^0 and y in R intersect M_d^1. Their joining line J is
nonsplit (neither point of R lies on a split line), and its direction h
is not d. The same connectivity forces x,y together in h. They now have
two common vertices, contrary to linearity.

Finally choose a designated consecutive pair a,b in any split four-cycle.
They have different opposite-pair labels in its joining direction g.
Any agreement in a different direction is a merged cross-identification:
ordinary blocks cannot contain two points whose joining direction is g.
An intersecting refinement must retain one of those cross-identifications,
which the preceding paragraph prohibits. This proves that NO simultaneous
refinement of all these partitions is both intersecting and linear.
No uniqueness of a pair's adjacency generator was assumed.

The statement is stronger than failure of a particular greedy split.
There is no part-preserving vertex map from ANY linear intersecting
hypergraph onto this source that is surjective on source edges. Choose one
preimage edge for each distinct source edge; their equal-vertex partitions
would give exactly the prohibited refinement. This rules out arbitrary
edge-surjective clone/lift constructions with the usual cover-pushforward
argument. It is not a theorem about other sources or all possible trades.
refinement-checkpoint.md gives every hypothesis and the full lift argument.

## Checkpoint2: a different exact-intersection construction loses its cover size

A separate attempt starts again in F_q^2, q>=3. In part d use old vertices
[d,L] for the q lines of direction d and arbitrary fresh vertices T_d.
For an arbitrary subset X of the plane include ordinary edges
 e_x={ [d,x+d]: d a direction }.
Allow arbitrarily many exceptional edges
 f(p,g,t)={t} union { [d,p+d]: d!=g }, with t in T_g.
Thus each exception keeps a punctured pencil and adds one fresh coordinate.
Centers and ordinary subsets are unrestricted within this model.

If this hypergraph is linear and intersecting, each part has at most q
NONISOLATED vertices, and hence tau<=q=r-1. To prove it, fix f(p,g,t)
and L=p+g. An ordinary center x on L either equals p, sharing q labels,
or differs from p, sharing none. So no ordinary edge uses old [g,L].
An exception with omitted direction h!=g could use [g,L] only with its
center p' on L. If p'=p the two exceptions share q-1>=2 old labels; if
p'!=p they share no old label and no fresh label. Both are prohibited.
Exceptions omitting g use a fresh label there. Thus old [g,L] is unused
in the ENTIRE hypergraph.

All centers using a fixed fresh label t in g lie on one g-line L(t):
otherwise their edges share t and their joining-direction old label.
Different fresh labels in g must give different L(t): centers on the same
line would yield either q shared old labels (equal centers) or no common
vertex (distinct centers). Hence used fresh labels inject into unused old
labels. If u old labels are unused, there are at most (q-u)+u=q usable
labels in that part. Selecting them gives the claimed cover.
This proof includes any number of exceptions per line and X empty;
adding a second exception to cure degree-one fresh vertices does not help.
The full definitions and proof are in pencil-checkpoint.md.

This is a separate actual mechanism failure, not a numerical scan. It
covers only exceptions with ONE fresh coordinate and a pencil in all the
other coordinates. Multiple fresh coordinates, nonpencil old labels,
and other finite linear spaces remain outside its scope.

## Primary comparison and honest remaining operation

LR itself is the negation of the known linear intersecting Ryser assertion,
not a new conjecture. FHMW's actual Lemmas2.1-2.2/Theorem2.3 already impose
strong degree restrictions; their Theorem2.8 handles r<=9. Their13-partite
linear example obstructs edge-minus-one covers but has a displayed9-cover,
so that local condition is insufficient. Bahmanian's actual Theorem4.1
and its laminar splitting step pay fairness, not preservation of intersection
of each pair. These antecedents and full source transfers are credited in
primary-comparison.md. The new checkpoints are elementary source-specific
support, not demonstrated substantial contributions or worldwide firsts.

Still unpaid is ONE finite object meeting ALL frozen quantifiers, or a
cover theorem for EVERY finite linear intersecting partite hypergraph.
A source-based trade would have to introduce new agreements (escaping the
proved refinement obstruction), retain exactly one for every pair, and
independently exclude ALL r-1-block covers. No such trade, cover estimate,
alternative full construction or universal cover theorem was obtained.
Neither conditional design equations nor a restricted-class obstruction
is being substituted as a solution. No guarantee a discovery exists.

## Continuity, scope of validation, and handoff

The exact mandatory FT2 historical brief was read and hash-checked, but
its superseded target was not attempted. All current campaign exclusions,
4/10 count and separate analytic/crossing work remain intact. The complete
nontruncated tree was parsed; all 372 numbered family titles and selected
complete catalogue entries were surveyed. Actual theorem/proof extents
are separately recorded; authentication is not reading. Mutable ledger
context is snapshotted internally. Large histories are precise read-only
references, never dependencies on future live bytes.

No mathematical search program, third-party research code, historical
program or numerical diagnostic ran. Both checkpoints are proofs for all
their stated inputs. Integrity checks establish only artifact identity.
The read-only verifier checks an EXTERNAL seal anchor, exact owned files
AND directories, sizes/SHA256, input/output roles, scope/status and retained
pinned Git identities. It reads internal snapshots, not future live ledger
state. Before/after source receipts are historical observations. The final
seal is reported externally; the verifier is inspected and authenticated
before execution. All writes are confined to this r15 directory. There
were no nested agents, staging, commits, uploads, external messages,
publication, submission, manuscript or Lean work.
