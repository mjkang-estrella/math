# I189 parent disposition: complete patch classification passes; transport still conditional

2026-10-11. **Original E183: UNRESOLVED. The restriction
classification, admissibility analysis and stated conditional transports
PASS at their stated scopes. Eight accepted, two remaining.** The
local-ear mechanism remains parked. No substantial finding is
nominated; the verified deductions are technical progress, not a ninth
finding.

This was the first dispatch on the new provider driver
([task archive](iteration189-patch-route-transport-task.json)); it
completed without interruption and returned detached hashes for exactly
the five assigned files, with no other writes.

## Written proof review

The parent read all five outputs in full and checked the original
arguments. Two parent-side enumeration scripts were also written and
run (below); they caught no error in the child's mathematics.

**Complete restriction table.** Splitting on the chord $xy$ and solving
the degree-two equations at the six patch vertices gives exactly ten
degree-feasible restrictions: the isolated-cycle rows $Z$ (six-cycle),
$Z_{\mathrm{top}}$, $Z_{\mathrm{bottom}}$ (four-cycles), and the seven
Hamiltonian candidates $K_A, K_B, F, L_{ab}, L_{cd}, L_{bc}, L_{ad}$.
The parent independently re-derived this table by exhaustive
enumeration of all $2^{11}$ subsets of the eleven local edges: exactly
ten solutions, matching every claimed internal edge set, continuation
set, path/cycle component structure, terminal pairing and complementary
local matching edge list, with no missing or extra row. The three
closed-cycle rows are correctly excluded as Hamiltonian restrictions
since $Y$ is nonempty and disjoint from such a component. Verified
completely.

**Admissibility (1).** For the two-continuation rows the rest must be a
single spanning path on the indicated terminals, and this is also
sufficient; for the four-continuation rows the rest is two spanning
paths, and the union is one cycle iff the rest pairing differs from the
patch pairing — the contraction to two perfect matchings on four labels
is exactly the gluing lemma the parent verified exhaustively in the
I188 review. The planarity exclusion of $\gamma=(a'd')(b'c')$ via the
boundary order $(a,b,d,c)$ of the outgoing incidences (paid in I188) is
correct: an $a$-to-$d$ arc separates $b$ from $c$ in the complementary
disk. Hence $K_A,K_B$ are admissible exactly with rest pairing $\beta$
and $F$ exactly with $\alpha$, and the canonical-versus-alpha two-cycle
obstruction is exact. The color analysis (balanced $R$, used terminals
balanced, forbidding $ac$ and $bd$ as two-letter used sets) checks out
against the terminal colors $a',c'$ black and $b',d'$ white. Verified.

**Port threading.** The labelled-incidence tracing rule is a lossless
description of how the used continuations and patch routes determine
the five-port type; in particular $K_A$ and $K_B$ have identical
labelled endpoints and pairing, so the hexagon replacement preserves
the full type, not only $U$. Verified; the direct transport of Section
3.1 follows, and with criterion (S) every $K_B$ survivor yields E183
for its instance.

**Four-continuation obstruction and witnesses.** For $F$, fixed-rest
replacement by $K_A$ closes exactly the two displayed cycles; each rest
path uses an even number of cut edges since it starts and ends in $X$;
an empty cut distribution leaves a closed $X$ component immune to
exterior-only repair. In the balanced $(2,2)$ case the new local
pairing equals the old exterior pairing $\sigma$, so reconnecting with
the other noncrossing exterior pairing restores one Hamiltonian cycle.
All eight displayed $Y$-path witnesses were verified by the parent
edge-by-edge: every consecutive pair is a declared edge of the
thirteen-vertex $Y$, the two paths of each row are vertex-disjoint and
span all thirteen vertices, and the labelled endpoints realize exactly
the claimed pairings (six distinct cut-2 pairings plus the two no-cut-2
pairings). The $U=0134$ conclusion — reconnection succeeds at
Hamiltonicity but converts survivor $03,14$ to lost $D=01,34$ — agrees
with the parent-verified complete no-cut-2 exterior table. Verified.

**Two-continuation repair.** Fixed-rest replacement is impossible
(degree three at the unused terminals), so a compensating rest change
is mandatory. The symmetric-difference argument against the known $q$
completion supplies a perfect-matching repair: the difference has
degree one exactly at the two unused terminals, hence contains one
alternating path between them, and flipping along it repairs the
degrees. The parent checked this degree-and-alternation proof; it is
elementary and correct, and its stated limits (uncontrolled topology,
pairing and type; using all components would recover the known lost $q$
completion) are honest. The one-edge repair subcases check out: cutting
an internal edge of a spanning path separates its endpoints, so the old
path endpoints land in different components and the resulting pairing
is $\beta$ or $\gamma$; planarity excludes $\gamma$; and for the mixed
rows the two traversal orders give $\alpha$ and $\beta$ exactly as
tabulated. The conditional transports are all correctly conditioned on
adjacency/order hypotheses not implied by E183. Verified.

**Residual statement (T_R).** The claimed necessary-and-sufficient
condition over all perfect matchings of $R=G-V(C)$ — cycle-free
complement with pairing $\beta$, plus survivor type after tracing — is
a correct restatement: necessity by deleting $A$ and the patch from the
desired pair, sufficiency by (1), cubic complementation and (S). The
class disposition table in Section 5 accurately summarizes which
classes are settled (canonical/toggled outright; balanced cut-2 $F$;
the proved short-repair subcases) and which remain open (unbalanced $F$
and $F$ of type $0134;03,14$; the four $L$ rows outside their short
repairs). A counterexample instance would need every survivor to
concentrate in open classes; the record neither constructs such an
instance nor proves concentration impossible. The verdict UNRESOLVED is
honest.

## Limits that remain binding

E183 remains UNRESOLVED. The open classes require an unrestricted
change of the rest inside $X$ that simultaneously yields cycle-free
spanning paths with pairing $\beta$ and a survivor five-port type;
neither existence nor impossibility is shown. The complete eleven
survivor fibres are not shown to meet the settled classes. No fully
hypothesized counterexample is supplied, so E183 is not refuted either.
The fixed-root source implication (18) from I188 remains separately
unpaid; this route addresses the full population (17) and claims no
surjectivity. Z184, E182/E181/H180/L179, exchange, (T) and Q164
receive no new implication. The I189 record is unsealed.

## Authentication and independent checks

The [validator](../experiments/i189-parent-validate.py) authenticates
all five detached outputs, exact five-file membership, twenty input
records and all eleven supplied anchors (ten I187/I188 outputs plus the
manuscript), confirms the archive write scope, and re-authenticates the
I188/I187/I183 chain. The
[verification receipt](../experiments/i189-parent-verification.json)
passes: the inherited 23-stage replay in **8.788 seconds** with empty
stderr.

Independent finite checks, all parent-side: exhaustive enumeration of
all $2^{11}=2048$ subsets of the eleven local edges reproduces the
ten-row classification exactly (edge sets, continuations, component
structures, terminal pairings, complementary matchings, color
constraints); all eight Section 3.3 exterior witnesses verified against
the declared thirteen-vertex $Y$ (edges, disjointness, spanning,
labelled pairings, and the $T_Y$ cross-check against the I188 named
packings). Two parent-script defects were caught and fixed during
development (an omitted internal edge in the expected $L_{ad}$ row and
a wrong distinct-pairing count); the final run passes on the corrected
script with the child's mathematics untouched. Pairing/planarity,
matching-repair and transport arguments are prose-reviewed as written.
Neither acceptance gate is lowered; the twelve facial and 626 matching
controls remain inherited finite evidence, not rerun.

## Next bounded step

Both geometric routes now terminate at one point: over all perfect
matchings $N$ of $R$, some canonical candidate $F_N$ must be
Hamiltonian with survivor type (I189's (T_R)), and the source route
needs one survivor in its marked image (I188's (18)).
[I190](iteration190-beta-pairing-survivor-brief.md) attacks the pairing
layer directly: classify what the brace hypothesis, the two-edge
matching extension consequences and the manuscript's circulation and
Pfaffian operations force about cycle-free $\beta$-paired complements
of perfect matchings of $R$, and either supply a survivor-typed one,
exhibit a fully hypothesized counterexample, or return an exact
obstruction. The five-file policy and both acceptance gates remain
unchanged.
