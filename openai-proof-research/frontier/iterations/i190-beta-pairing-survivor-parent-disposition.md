# I190 parent disposition: residual pairing deductions pass; concentration still open

2026-10-11. **Original E183: UNRESOLVED. The residual connectivity,
matching-table, parity/sign and conditional square-switch deductions
PASS at their stated scopes. Eight accepted, two remaining.** The
local-ear mechanism remains parked. No substantial finding is
nominated.

First dispatch on the current provider driver for this brief
([task archive](iteration190-beta-pairing-survivor-task.json));
completed without interruption with detached hashes for exactly the
five assigned files and no other writes.

## Written proof review

The parent read all five outputs in full. Finite identities were
independently re-derived by enumeration (below); the structural
arguments were checked in prose without substantive repairs.

**Residual connectivity (§1.2).** $R=G-V(C)$ is connected (a second
component would need at least three of the four patch attachments, by
the paid exclusion of one- and two-edge cuts), bridgeless (a bridge
would give a nontrivial three-edge cut of $G$, excluded by the paid
small-cut deduction), and has no cut vertex (a cut vertex of a
bridgeless connected subcubic graph needs at least four incident
edges). The residual cycle shore bound (at least four outgoing matching
edges) follows from the same cut exclusions. Verified.

**Matching/deletion alternatives (§1.3).** The exact table of patch
matchings by continuation set $J$ (ten matchings over six balanced
groups; $ac$, $bd$ and odd $J$ impossible by color) was independently
re-derived by the parent: enumeration of all $2^{11}$ subsets of the
eleven local edges selecting patch-perfect matchings reproduces the
claimed table exactly, including consistency with the I189
complementary matchings of the seven Hamiltonian rows. The consequence
$R-\{a',b',c',d'\}$ has a perfect matching (request $aa',cc'$; balance
forces $J=abcd$) is correct, and the stated limits of two-edge
extension at the terminal boundary are honest: the manuscript contains
no brace lemma, and the two-extendability premise is the explicit
inherited hypothesis consequence, used as such. Verified.

**Universal alpha terminal-deletion paths (§1.5).** For the fixed
perfect matching $N_0$ of $R$ minus all four terminals and any perfect
matching $N$ of $R$, the symmetric difference has degree one exactly at
the four terminals, both ends of each path use $N$ edges, so each path
has odd length with opposite-color endpoints; the pairing is $\alpha$
or $\gamma$, and planarity excludes $\gamma$. The conclusion — every
$R$ matching carries two disjoint $\alpha$-paired alternating
terminal-deletion paths — is a genuinely new structural fact, correctly
proved, and its stated non-consequences (the paths are not complement
components; flipping them leaves terminal defects) are correctly
flagged. Verified.

**Parity and crossing identities (§2.1).** The component-count identity
(1) ($k+2$ for $\alpha$, $k+1$ for $\beta$) is exactly the
parent-verified four-label gluing dichotomy, re-checked. The crossing
identity (2) is color bookkeeping along a path with the
cycle-free hypothesis; the resulting minimum cross-edge counts (alpha:
at least two, balanced by direction; beta: at least three, surplus one)
use the four-edge cut bound correctly. Verified.

**Constant Pfaffian sign (§2.3).** The written computation — each
alternating difference cycle is oddly oriented because its complement
is perfectly matchable (in $G$, adding $A$), giving edge-sign ratio
$(-1)^{l+1}$ against permutation ratio $(-1)^{l-1}$, hence total sign
ratio $+1$ — is the standard identity, correctly derived from the read
stipulated assertions (planar Pfaffian orientation, lines 807–810 and
825–827). The conclusion that sign cannot separate $\alpha$ from
$\beta$, and the negative control that a survivor filter breaks the
group-product factorization, are both correct and honestly stated as
limits. Verified.

**Square switch (§3, §4.2).** The alternating four-cycle exchange (6)
cuts each alpha path once, rejoins intervals across paths, and yields
exactly two spanning paths with pairing $\beta$ or $\gamma$; planarity
forces $\beta$. When the square lies in $W$, simultaneous canonical
patch replacement keeps the cut set and $Y$ packing, and the
noncrossing-pairing uniqueness argument preserves the FULL local type —
so any $F$ survivor with a $W$ square settles E183 for its instance,
including $U=14$ and $0134;03,14$. The existential gap (no proof such a
square exists) is stated without inflation. Verified.

**Concentration analysis (§5).** The negation (C190) of (T_R) is
correct, and the derived restrictions are correct: all survivors avoid
every settled class; every $F$ survivor avoids a $W$ square; and every
cycle-free beta matching has cut profile $\{e_2,e_3,e_4\}$ (type $P$)
or $\{e_2\}$ (type $D$) — the parent verified this mapping
computationally (at each port $e_i\in N$ iff $i\notin U$; the lost
fibres give exactly those profiles). Restriction 5 correctly notes the
existence theorems ($q$, the marked image, the prescribed path
$c$-$x$-$y$-$d$) specify no survivor condition. The verdict UNRESOLVED
at (R190) is honest: neither the concentration contradiction nor a
fully hypothesized counterexample is supplied.

## Limits that remain binding

E183 remains UNRESOLVED at (R190): some perfect matching of $R$ with
cycle-free $\beta$ complement and survivor-typed canonical trace must
exist; no argument supplies or excludes it. (C190) is a hypothesis
about instances, not a constructed instance. The fixed-root source
implication (18) remains separately unpaid. Z184,
E182/E181/H180/L179, exchange, (T) and Q164 receive no new implication.
The I190 record is unsealed.

## Authentication and independent checks

The [validator](../experiments/i190-parent-validate.py) authenticates
all five detached outputs, exact five-file membership, twenty-six input
records and all sixteen supplied anchors, confirms the archive write
scope, and re-authenticates the I189/I188/I187/I183 chain. The
[verification receipt](../experiments/i190-parent-verification.json)
passes: the inherited 23-stage replay in **8.689 seconds** with empty
stderr.

Independent finite checks, all parent-side: exhaustive enumeration of
all $2^{11}$ local subsets reproduces the Section 1.3 $J$-grouped
matching table exactly (ten perfect matchings, six groups, same-color
pairs impossible, consistency with the I189 complementary matchings);
the four-label gluing identity and the lost-type cut profiles (8) are
re-verified; the six inherited Section 4.1 exterior witnesses match the
parent-verified I189 witness edge sets byte-for-byte. Two parent-script
defects were caught and fixed during development (the matching filter's
terminal semantics and an internal/full index representation mismatch);
the final run passes with the child's mathematics untouched.
Connectivity, tight-shore, sign and square-switch arguments are
prose-reviewed as written. Neither acceptance gate is lowered; the
twelve facial and 626 matching controls remain inherited finite
evidence, not rerun.

## Next bounded step, with a stopping rule

Three consecutive iterations have sharpened E183 without closing it;
the residual is now the single assertion (R190) with rigid necessary
conditions (C190)(8). [I191](iteration191-concentration-exclusion-brief.md)
makes one final focused attempt on this line: derive a contradiction
from the joint concentration constraints (complete fibres, brace
premise, cut-profile rigidity, excluded $W$ squares, universal alpha
terminal-deletion paths) or construct a fully hypothesized
counterexample. **Stopping rule:** if I191 returns UNRESOLVED without a
decisive new constraint, the E183 line is PARKED like the local-ear
mechanism, and the next iteration pivots to the dormant Q164/universal
exchange surface. The five-file policy and both acceptance gates remain
unchanged.
