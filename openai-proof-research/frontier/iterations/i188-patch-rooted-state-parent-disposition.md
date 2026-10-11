# I188 parent disposition: patch phase and frozen recovery pass; survival still unpaid

2026-10-11. **Original E183: UNRESOLVED. Steps 1–5 and the step-6
exterior classification PASS at their stated scopes. Eight accepted, two
remaining.** The local-ear mechanism remains parked. No substantial
finding is nominated; the verified deductions are technical progress
toward the target, not a ninth finding.

This was the third transport attempt: the first two runs failed at the
provider with no outputs ([recovery records](i188-provider-failure-recovery.md),
[second](i188-provider-failure-recovery-2.md)); the
[second resume](iteration188-patch-rooted-state-codex-astra-resume2-task.json)
completed on a different provider driver. The salvaged drafts of the
failed runs were passed only as labelled unverified leads; the completed
run independently re-derived every step from the authenticated sources,
and the parent re-checked the arguments from the written record, not
from the salvage.

## Written proof review

The parent read all five outputs in full and checked the original
arguments without substantive repairs.

**Faciality.** Each square $S_1,S_2$ has exactly four off-cycle
incidences ($cx,aa',bb',yd$ and $xa,yb,dd',cc'$ respectively), and its
two potential chords join same-color vertices, so no chord exists. If
both sphere sides contained vertices, the two side boundaries would be
disjoint subsets of the four incidences, each of size at least three by
I187's paid exclusion of one- and two-edge cuts — impossible since
$3+3>4$. The empty side is then a face, and at $x$ (and $y$) the two
squares occupy the two distinct sectors adjacent to $xy$. The argument
needs no embedding-uniqueness theorem. Verified.

**Dual identifications.** The propagation $t_x=(o,\ell,r)$,
$t_a=(\ell,o,u)$, $t_b=(\ell,u,v)$, $t_y=(\ell,r,v)$, $t_d=(r,v,w)$,
$t_c=(r,o,w)$ was re-derived from the two face sectors at each primal
vertex; the parent caught and the record avoids the false identification
$v=w$ that a hasty sector count suggests (the face across $by$ from
$S_1$ is the same face as across $yd$ from $S_2$, and that is $v$
itself, consistently). All fifteen pairs of the six names are closed:
eleven by dual no-loops and $(o,v),(u,w),(\ell,w),(r,u)$ by explicit
parallel-edge contradictions ($(aa')^*\!\parallel\!(bb')^*$,
$(aa')^*\!\parallel\!(cc')^*$, $(dc)^*\!\parallel\!(xy)^*$,
$(ab)^*\!\parallel\!(xy)^*$), all excluded by paid dual simplicity.
$\deg_T(\ell)=\deg_T(r)=4$; the six triangles tile a disk $\Delta$ with
boundary $\Gamma=(o,u,v,w)$ dual to $\partial V(C)=\{aa',bb',cc',dd'\}$;
every other dual vertex lies strictly in the complementary disk; roots
$\{o,\ell,r\}$ with $u,v,w$ nonroots. Verified.

**One consistently signed marked cycle.** In every undirected group the
side at $t_b$ must join two nonroots, forcing $uv$, and similarly $vw$;
both share $v$, so $u,v,w$ are consecutive on one cycle $C_0$, and the
mark $\eta$ retains exactly the orientation $u\to v\to w$: exactly one
fixed sign per group, sharpening I187's generic bound of two. The
return path of $C_0$ from $w$ to $u$ avoids the roots and $v$, hence
lies in the complementary disk (its interior vertices can only be the
roots $\ell,r$); the root-free bounded disk of $C_0$ is therefore
always the lens on the side of the directed arc $u\to v\to w$ opposite
$\Delta$, so the fixed sign $\varepsilon_*$ is a single
embedding-determined bit, identical for every group. The chord-$uw$
and triangular-$C_0$ edge cases are covered. Verified.

**Marked nonvanishing.** With $F_D=\{C_0\}$, I187 (13)–(14) give
leading Taylor coefficient $(-i)^{c(D)}\varepsilon_*\prod_{j\ne0}2d_j$
in degree $c(D)-1$, with $d_j>0$ by the source's positive circulation.
At minimum degree $c_{\min}-1$ the phase is common across groups, the
magnitudes strictly positive, and at least one group exists by
prop:pairs under the paid hypotheses; hence $Z_\eta\not\equiv0$, and
fixed-$s$ cancellation (the mark depends on $s$ alone) yields a
partnered forest state with $s(t_b)=v$, $s(t_d)=w$. The parent verified
the one-fixed-sign phase identity against I187 (14) modulo 4 for all
$c$ and the retained-orientation count $2^{c-1}$. Verified.

**Frozen recovery.** The deleted-spoke tree $W_s$ must span $t_y$; its
only candidate incidences there are $\tau_{t_b}$ (iff $s(t_b)=v$) and
$\tau_{t_d}$ (iff $s(t_d)=v$), and bijectivity allows at most one, so
every partnered forest state has exactly one. Under the mark, $t_y$ is
a nonroot leaf with parent edge $\tau_{t_b}$, and symmetrically $t_c$
is a nonroot leaf with parent edge $\tau_{t_d}$ (the $t_{c'}$ spoke is
excluded by bijectivity once $s(t_d)=w$). Both I187 (4)/(5) parent-edge
tests are therefore automatic, $f_0=(xa)^*$ is prescribed, and
$A^*\subseteq K_s$: every marked partnered forest state recovers a
perfect matching $M_s\supseteq A$ with Hamiltonian complement
(lem:P-forest). The separate consistency check (omitting $dc$ while
$xa,by\in M$ closes the proper four-cycle $c\!-\!x\!-\!y\!-\!d\!-\!c$)
is correct. So the $A$-containing fixed-root source image is nonempty,
and by endpoint necessity it is exactly the marked image. Verified.

**Survival analysis.** Every marked recovery has the lost completion's
patch routes $a'\!-\!a\!-\!b\!-\!b'$ and $c'\!-\!c\!-\!x\!-\!y\!-\!d\!-\!d'$,
and the hexagon toggle interchanging $A\leftrightarrow B$ preserves the
continuation pairing and full local type while changing which half lies
in the matching, so it cannot move between lost and survivor rows. The
written degree casework in the exact thirteen-vertex exterior is
complete: without cut 2 the used sets are $01,04,14,0134$ by the color
balance (15); $04$ forces an isolated cycle; the admissible packings
are exactly $R_1,R_2,R_3$ (type $01;01$, lost $P$), $S$ (type
$14;14$, survivor), the three $R_i$-tails with edge $1\!-\!28$ (type
$0134;03,14$, survivor), and $T$ with edge $28\!-\!29$ (type
$0134;01,34$, lost $D$). The parent independently re-derived this table
by exhaustive enumeration (below). The residual obligations are stated
correctly: (17) for the full quantifier and (18) for the source route,
and the generic-weights remark only reformulates survivor existence
inside the image without proving it. The honesty boundaries are all
respected: no lost-completion preimage, no surjectivity, no fully
hypothesized counterexample, no sequel.

## Limits that remain binding

E183 remains UNRESOLVED: the nonempty marked image could a priori
consist entirely of $P,D$ completions, and the route's remaining
implication (18) — some marked state uses cut 2 or has type $14;14$ or
$0134;03,14$ — is unpaid. Conversely E183 could hold outside the
fixed-root image; no surjectivity is claimed in either direction. The
complete survivor fibres establish existence without the forced patch
routes, and the forced patch routes establish neither survival nor its
failure. Z184, E182/E181/H180/L179, exchange, (T) and Q164 receive no
new implication; neither E183$\Rightarrow$Z184 nor separation is shown.
The two earlier drafts' overlapping content was treated strictly as
unverified leads; nothing was accepted from them.

## Authentication and independent checks

The [validator](../experiments/i188-parent-validate.py) authenticates
all five detached outputs, exact five-file membership, seventeen input
records and all six supplied anchors, and confirms the prior proof
records and sealed reference unchanged.
The [verification receipt](../experiments/i188-parent-verification.json)
passes on its first execution: the inherited 23-stage replay in
**8.706706 seconds** with empty stderr.

Independent exact checks, all parent-side: an exhaustive enumeration of
all $2^{17}=131072$ binary assignments to the declared exterior edges
confirms the complete no-cut-2 classification (exactly the packings
$R_1,R_2,R_3$ for $U=01$; none for $U=04$; exactly $S$ for $U=14$;
exactly the three $R_i$-tail packings with pairing $03,14$ and $T$ with
$28\!-\!29$ pairing $01,34$ for $U=0134$; 24 valid packings total), the
$Y$ bipartition making (15) automatic, realizability of exactly the six
expected cut-2-using used sets, and the gluing lemma that distinct
pairings on four ports give one cycle while equal pairings give two.
Phase and orientation-count algebra for the one-fixed-sign
specialization (16 and 8 cases) and the inherited I187 formal checks
(276 Fourier identities, 64 endpoint cases) also pass. The faciality,
disk, sign, nonvanishing and white-tree arguments are prose-reviewed as
written. The enumeration validates a written symbolic casework on the
fixed declared exterior; it is not an instance-population scan, and
neither acceptance gate is lowered. The I188 record is unsealed; the
twelve facial and 626 matching controls remain inherited finite evidence.

## Next bounded step

The verified deductions reframe E183 exactly: a Hamiltonian complement
contains $A$ iff its patch restriction is the canonical pair of routes,
and the known survivor fibres supply survivors with unrestricted patch
behavior. [I189](iteration189-patch-route-transport-brief.md) therefore
attempts survivor transport: a complete symbolic classification of the
possible patch restrictions of a Hamiltonian cycle, and for each class a
proof that some survivor-typed member with canonical routes exists, or a
precise obstruction, or a fully hypothesized counterexample settling
E183 negatively. This is a finite local classification plus global
pairing analysis, not a revival of the parked local-ear mechanism and
not another filter computation. The five-file policy and both
acceptance gates remain unchanged.
