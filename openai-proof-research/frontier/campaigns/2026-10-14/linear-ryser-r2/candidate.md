# Unchanged full LR: focused research attempt 2

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party materials remain
private and retain their original rights.

**UNRESOLVED_FULL_LR_AFTER_TWO_ATTEMPTS.** No LR witness and no universal
cover theorem was obtained. The work below realizes a different
two-coordinate, pair-changing trade, classifies its saturated K_4 form,
and proves that even its permitted extensions have an explicit (r-1)-cover.
There is no independent mathematical/contribution PASS, nomination,
manuscript, Lean package, publication, submission or count increase.
The campaign remains 4/10; analytic r13 and crossing work remain separate.

## Frozen assertion and authenticated continuity

The target is existence of ONE integer r>=2 and ONE nonempty finite SET
of r-partite r-uniform edges, such that EVERY distinct pair meets in
EXACTLY ONE vertex and EVERY vertex set of size at most r-1 misses an
edge. Equivalently tau=r, since any edge is a cover. No restriction on
r, fields, degrees, part sizes, edge count, dimension or construction is
imposed. Refutation requires tau<=r-1 for EVERY such hypergraph.

`original-scope.md` was copied byte-identically from r15, SHA256
`dc98c7a1b62d7a44ead17140b057e82fdfc5e42083c01b3f679fcf3782e4345c`.
Its historical method paragraph is retained as fixed original text, not
an instruction to repeat the failed refinement. The current focused brief
supersedes the old distinct-family discovery assignment.

Before relying on r15, this round authenticated its external seal
`87339b6771c8e4e08a05f3a346baeb6d0199459618a8a0b46550564e2ed8f482`,
its manifest and exact 39-file/5-directory membership, and all sizes and
hashes (7058130 bytes including manifest/seal). The full candidate, both
checkpoints, source contracts and comparison were then read from those
authenticated files. `inputs/r15-authentication.json` is the exact receipt;
the historical package was not copied wholesale and its code was not run.
The full 1078-line mandatory historical FT2 brief was read and hash-checked,
without reopening its superseded target. Mutable ledger and current parent
context are snapshotted internally.

Accepted source truth remains openai/math
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The balanced `thm:main`
provides tau=q+1, q+1 nonisolated vertices per part, at sufficiently large
PRIME q. The extension companion's `thm:main` instead uses q=s^n, with
s sufficiently large prime congruent to 2 modulo 3 and n sufficiently
large odd, its threshold depending on s; balance is not asserted. Neither
asserts linearity. Both already prove `cor:tree-cover`. The full balanced
deterministic construction and the full two paper.tex files were read;
their truth was not audited. Exact retained paths, Git blobs and actual
reading limits appear in `source-contracts.md` and the input records.

## Selecting and paying a different operation

The design formulation identifies hypergraph edges with points, and each
part with a partition. Every pair of points must occur in precisely one
block across the partitions, and every r-1 blocks, from arbitrary classes,
must fail to cover the points. `design-checkpoint.md` proves this exact
equivalence, including singleton blocks and distinctness of the dual edges.

Primary reading showed why standard substitution does not settle the
problem. Stinson's actual weighted GDD substitution and disjoint-block
assembly in Theorems 2.1/2.4 construct a particular parallel class, not the
full resolution and cover inequality needed here. A synchronized resolvable
transversal-design inflation CAN supply all partitions and exact pair
coverage, but it has an independent explicit upper cover: if the master
has a classes, fibers have size m, and b>=1 internal classes are added,
then R=ma+b and c_output<=m c_master<=ma<=R-1. The proof covers mixed
classes, not only same-class covers. This elementary screen is support,
not a substitute target or a claim about all Wilson constructions.

The sustained attempt instead introduced two fresh coordinates per
exception and actual new pair agreements. Four fresh labels z_0,...,z_3
occupy distinct affine directions d_0,...,d_3. Six exceptions f_ij, indexed
by K_4 edges, use z_i,z_j and old pencil labels at a center p_ij in all
other directions. Fresh equality is a literal common vertex, so each
part's equivalence relation is automatically transitive.

The unpaid mechanism was to realize these six centers with exactly one
agreement for every pair, recover all omitted old line labels, and then
exclude ALL q-covers at rank q+1. Unlike one-coordinate punctures, adjacent
exceptions can now replace lost old agreements by a shared fresh label in
their OTHER omitted direction. The old injection obstruction does not
apply. We carried this operation through actual geometry and the global
cover test, rather than assuming counts realize a design.

## Checkpoint 1: the saturated K_4 trade is realized over F_4

Demand that every d_i-line omitted at p_ij contains another of the six
centers whose edge uses that old label. An ordinary edge cannot recover
such a line while intersecting f_ij exactly once. At the three centers
incident with any fresh label z_v, recovery directs an arrow u->w when
p_vu p_vw has direction d_u. Each of the three vertices needs an outgoing
arrow and each pair supports at most one. The arrows therefore form a
directed 3-cycle.

Normalize d_0=infinity, d_1=0, d_2=1, d_3=t with t!=0,1, and the cycle
at 0 as 1->2->3->1. The first three centers are
p_01=(0,0), p_02=(1-t,0), p_03=(1,t). Checking the two orientations at
each other vertex forces

    p_12=(1-t,1-t), p_13=(0,t), p_23=(1,t^2),
    t^2-3t+1 = t^2+t-1 = t^2-t-1 = 0.

Subtracting gives characteristic two and t^2+t+1=0. Conversely these
coordinates work over every F_{4^n}. Put a=t^2=1+t. The complete centers are

    01:(0,0), 02:(a,0), 03:(1,t),
    12:(a,a), 13:(0,t), 23:(1,a).

All twelve adjacent K_4 pairs have joining direction in the union of
their omitted directions; they share exactly their common fresh label
and no old one. All three opposite pairs have joining direction t^2,
which neither omits; they share exactly that one old label. The complete
15-pair table and normal-form derivation are in `k4-checkpoint.md`.

Delete all twelve omitted affine lines from the ordinary set. Every
remaining ordinary point has its joining direction to each p_ij outside
{d_i,d_j}, giving exactly one old agreement. Ordinary-ordinary pairs
also agree exactly once. This is a rigorously realized finite linear
intersecting hypergraph, not an LR witness. At q>12, keeping the complement
of those lines gives q+1 nonisolated vertices in each of the FOUR affected
parts: the q old labels are all used, plus its fresh label. Other parts
still have at most q vertices. No lower-cover claim follows from this count.

## Checkpoint 2: extensions cannot repair its private old labels

Each affected direction has three omitted lines, with one old user each
among the six gadget edges. Each exception has two such private old
vertices, in the other two affected parts. Initially these have degree one.
One might try to add further exceptions reusing the fresh labels and
raising those old degrees. The following all-field obstruction pays that
repair question instead of stopping at the initial degree-one failure.

For q>=5, a new two-coordinate exception cannot have a gadget center:
it would share at least q-3>=2 old labels with that gadget edge. It also
cannot use two gadget fresh labels, since the corresponding f_ij already
uses both. If it uses exactly one, normalize that label as z_0. Write its
other omitted slope h and its center (x,y). Against the three nonincident
edges, absence of fresh agreement forces x notin {0,1,a}. Against the
three incident edges, sharing z_0 prohibits old agreement, leaving

    y=0 or hx;
    y=x+a or h(x+a);
    y=tx or h(x+1)+t.

Two first alternatives meet only at excluded centers. Thus two h-lines
must coincide, forcing h=0,1 or t. Substitution gives respectively
x=0, x=a or x=1 (or an impossible nonzero constant equal to zero).
No such new exception exists. The normal-form proof can normalize ANY
gadget label as 0, so no gadget fresh label can be reused at all.

An additional exception using no gadget fresh labels cannot use one of
the private old vertices either: its center would be on an omitted line
of a gadget edge, so their sole possible old joining-direction agreement
is absent and they are disjoint. An ordinary edge cannot use it for the
same reason. Therefore these old vertices remain degree one in EVERY
linear intersecting extension by arbitrary ordinary subsets and arbitrary
additional TWO-fresh-coordinate pencil exceptions, including attempted
fresh-label reuse. The theorem applies to every q=4^n>=16.

If v is one such vertex and e its gadget edge, e minus {v} is an explicit
q=(r-1)-cover of the ENTIRE extension. Every other edge intersects e
somewhere other than v. This is a genuine global upper-cover proof. It
does not infer tau=r from a failure of a restricted family of covers.

## L1-L5 and the exact unpaid full operation

L1 is met by literal partitions/vertex labels and complete pair proofs.
L2 is retained: no balanced-source refinement or edge-surjective lift was
retried. L3 is retained: the local q+1 part counts are not cover evidence;
the primary 13-partite example has its displayed 9-cover. L4 is retained:
all agreements and the resulting global cover above were independently
proved, without importing the source's lower estimate. L5 is retained:
the one-coordinate theorem remains within its original scope, and this
new obstruction is restricted to extensions CONTAINING the specified
K_4 gadget inside the TWO-coordinate pencil model. No fair-detachment
statement is read as preserving every pair intersection.

Still unpaid is ONE full LR witness, or a universal cover theorem.
A repair of this attempt must replace the gadget, change more coordinates,
alter old labels away from a single pencil, or carry out another global
trade so that its private-label obstruction disappears. It must prove
all pair agreements and exclude EVERY r-1 vertex cover afresh. No such
repair, independently valid lower-cover mechanism, or universal argument
was obtained. Other two-coordinate gadgets are not ruled out, nor are
three-or-more-coordinate exceptions or other finite linear spaces.

The exact F_4 diagnostic checks only the displayed 15 joins and twelve
old singleton labels; it was inspected and hash-authenticated before
execution. The normal form, arbitrary-field extension obstruction and
global cover are symbolic proofs. No broad SAT/finite search, historical
program or third-party mathematical code ran. The new deductions are
elementary supporting checkpoints without a demonstrated substantial
contribution or worldwide priority claim.

All writes are confined to this directory. Exact membership, sizes/hashes,
source-reading extents, historical unchanged-source receipts, and the
read-only externally anchored verifier accompany the report. The verifier
reads internal snapshots only and does not depend on future live ledger
state. Its success establishes integrity only, not mathematical acceptance.
