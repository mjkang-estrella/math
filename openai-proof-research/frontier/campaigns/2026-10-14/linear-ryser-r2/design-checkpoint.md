# Resolvable designs: exact translation and the synchronized inflation attempt

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party rights retained privately.

This screen is supporting work only. The main sustained attempt is the
two-coordinate K_4 trade in `k4-checkpoint.md`. Neither calculation solves LR.

## Exact dual formulation, with singleton blocks permitted

For a finite nonempty edge set E of an r-partite hypergraph, put X=E.
In part i, partition X according to its incident vertex; omit isolated
vertices and use a separate block label for every part. Every pair of
distinct X-points is in exactly one common block across all partitions
if and only if the original hypergraph is linear and intersecting.
Selecting hypergraph vertices covers edges if and only if their blocks
cover X. This preserves EVERY mixed-part cover, not just whole classes.

Conversely, given r partitions of a nonempty finite X with precisely one
common block per distinct pair, take one vertex per block, labelled by
its partition, and one edge per point. Distinct points give distinct
edges: otherwise they would share all r>=2 vertices. These operations
are inverse up to labels after isolated vertices are discarded. Thus LR
is exactly the existence of such partitions with block cover number r.
Singleton blocks may appear in this general translation. Excluding them
would narrow the target. An LR witness cannot have them, because if {x}
is a block through x, the other r-1 blocks through x cover ALL points:
each other point has its unique agreement with x somewhere else.

The partitions automatically impose equivalence transitivity. Merely
partitioning the PAIRS of X into colors does not provide this structure.

## A restricted assembly that genuinely realizes pair coverage

Let a>=2 and let P_1,...,P_a be partitions of a finite master set Z,
|Z|>=2, with every distinct pair in exactly one common block. Assume all
master blocks have size at least two. Write c_M for the minimum number
of master blocks covering Z. Fix m>=2. For each z take a disjoint fiber
F_z of m points. For each master block B require an ACTUAL resolvable
TD(|B|,m) on the fibers F_z, z in B: every block meets every fiber once,
every pair in different fibers occurs once, and its m^2 blocks are
partitioned into m parallel classes, each of m blocks. The existence of
these ingredients is a hypothesis, not inferred from divisibility.

On each F_z take b>=1 internal partitions having exactly one common
block per distinct pair. Require the same number b of internal classes
on every fiber. Internal class j on the output is the union of internal
class j over all fibers. For each i and each t in {1,...,m}, an output
cross class is the union of local TD class t over B in P_i. Blocks in
these unions are disjoint and cover all fibers, since P_i partitions Z.
There are exactly

                         R=ma+b

output partitions. A same-fiber pair occurs precisely once internally
and never in a cross block. A different-fiber pair projects to a unique
master block, then occurs in a unique block of its TD, and nowhere else.
Thus this is a proved resolvable pairwise balanced design, not necessary
incidence equations or an assertion that a general WFC preserves resolutions.

## The full cover estimate for this operation

For every selected master block B, one local TD parallel class consists
of m OUTPUT blocks covering the entire union of its fibers. Select a
minimum master block cover, of size c_M, and do this for each of its
blocks. The output has a cover by at most m c_M blocks. Choices for
different B can belong to different output classes; this is a valid
mixed-class cover. The blocks through any fixed master point cover Z,
by pair coverage, so c_M<=a. Therefore

                c_output <= m c_M <= ma = R-b <= R-1.

No cover estimate from the pinned source is used. Even a hypothetical
master with c_M=a would not make this synchronized inflation an LR
witness. The additional internal classes increase R without preventing
the m-fold lifted cover. The result applies to nonuniform master blocks
and arbitrary ingredient resolutions satisfying the stated hypotheses.

The ingredients are not vacuous. Take a master consisting of the three
two-point partitions of a four-point set. For m any prime power, a local
TD(2,m) is given on two copies of F_m by pairs (s,s+t), with t fixed
within a parallel class. Put the whole fiber in its one internal block,
so b=1. This explicitly realizes the output on 4m points with 3m+1
partitions and a cover of at most 2m blocks, by lifting a master parallel
class. This example is illustration of the operation, not a proposed LR
witness or a meaningful new construction family.

## Scope and primary comparison

Stinson's `arXiv:2403.17602v1`, Construction 1.1, substitutes weighted
ingredient GDDs for master blocks. The actual proofs of Theorems 2.1
and 2.4 additionally choose disjoint ingredient blocks and assemble ONE
parallel class, which is then treated as a group partition. They do not
supply the R full partitions required here or a lower bound on all
mixed-class covers. The synchronized construction above adds those
explicit stronger ingredient hypotheses, proves its resolution, and
finds the displayed upper cover. It is elementary use of established
design substitution, not a substantial contribution claim.

The inequality does not concern all weighted WFC constructions, arbitrary
frames, nonsynchronized color recycling, or arbitrary resolvable PBDs.
To go beyond it one must change the assembly so that no such m-block
cover of each selected master fiber union is available within an R-1
budget, and independently prove all pair and covering clauses. No such
assembly or universal cover theorem was obtained. This is not a
conditional-system substitute for the frozen full target.
