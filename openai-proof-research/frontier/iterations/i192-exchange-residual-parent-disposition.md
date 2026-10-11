# I192 parent disposition: facial-translation classification passes; exchange residual open at J192

2026-10-11. **Universal exchange: UNRESOLVED at J192. The
facial-translation classification, the long-gap bridge bookkeeping,
the short-gap equality reduction and the prism verification PASS at
their stated scopes. Eight accepted, two remaining.** The E183 line
and the local-ear mechanism remain parked. No substantial finding is
nominated.

First dispatch for this brief on the current provider driver
([task archive](iteration192-exchange-residual-task.json)); completed
without interruption with detached hashes for exactly the five assigned
files and no other writes.

## Written proof review

The parent read all five outputs in full. Finite claims were
independently re-derived (below); structural arguments were checked in
prose without substantive repairs.

**Exact domain and coordinates (§§1–2 of the analytic attempt).** The
step class, the spaces $L,L_0,U,V$, the bridge $b$, $\beta$, $c$,
$\eta$, and the derived identities
$d(H)=2+\dim(L+U+\langle b\rangle)$, $d(H)-d(G)-2=t+\eta-\ell$, and
$\Delta:=\ell-t=\delta_V+\varepsilon-\delta_R$ are restated correctly
from the parent-reviewed I168–I170 sources; the parent verified the
$\Delta$ bookkeeping algebra and the bridge identity
$b=3r+2s_{arc}+a_P+a_Q+a_D$ symbolically. The six-family nonemptiness
argument from `cor:pfaffian-paths` (manuscript lines 812–828, actually
read) is correctly scoped: existence only, no span conclusions. Verified.

**Matching lemma and classification (4).** The noncrossing-pairing
argument is correct in prose (even-odd pairing, whole-pair intervals,
connectivity forcing the shifted pairing, including the $m=2$
parallel-edge case). The parent independently enumerated all
noncrossing even-odd perfect matchings of $2m$ cyclically ordered
points for $m=1..8$ (Catalan populations 1,2,5,...,1430): in every
case the **unique** matching whose union with the selected matching is
a single cycle is the claimed shifted pairing
$(1,2),(3,4),\dots,(2m-1,0)$. The component-count consequences ($N-q_A$
= one $ux$ path + exactly $k_A$ cycles; $N-q_A-q_B$ = two $uv,xy$
paths + exactly $k_A+k_B$ cycles) follow, giving the complete
classification $F_J=N00$ on short arcs and $\varnothing$ otherwise, and
the long-gap collapse $V_{good}=0$, $R=U$, $\delta_R=t$. The chord
exclusion (a cross-terminal edge is a one-edge facial arc in this
3-connected class) is correct. Verified, with the $m\le8$ check
understood as confirmation of the combinatorial core, the general
proof being prose-reviewed.

**Short-gap equality branch (§5).** The restatement of H170 with the
actual spanning two-factor $F_Q=Q-a+e+f$ (exactly two components,
$z=F_Q-C_0$) is correct and genuinely new bookkeeping; the parent
verified the quotient algebra: with $D_G=W'+\langle r\rangle$ in the
equality case, $\eta=0\iff\lambda=-1/2$ where $z=\lambda r\bmod W'$,
and on quadrilaterals ($z=r+s$, $b=3r+2s$) this is exactly the paid
S169 failure $\alpha=-3/2$. The negative conclusion — no brace or
manuscript argument excludes $w(F_Q-C_0)=-1/2$, since the normalized
functional need not be $[0,1]$-valued on a disconnected two-factor — is
honest and correct. Verified.

**I178 scoping (§6).** The four lifted relations, the functional
equations (15), the completion residuals (16), and the statement that
no identification with an arbitrary four-terminal step's spaces exists
are faithful to the parent-reviewed I178 record; the refusal to count
relations as a rank bound is correct. Verified.

**Prism family (§7).** The parent independently enumerated all
Hamiltonian cycles of $C_m\square K_2$ for $m=4,6,8$: exactly $m+2$
cycles ($m$ two-rung cycles $C_i$ missing rails $t_i,b_i$, plus the two
all-rung twisted cycles with alternating, unequal layer matchings);
affine independence with $d(G)=m+1$ (exact rational rank); identity
(17) holds as an integer vector identity in all three cases. For both
deletion types the parent recomputed everything from scratch: adjacent
rungs lose exactly $C_2,\dots,C_{m-2}$ with
$(\ell,t,\eta)=(m-3,m-4,1)$; opposite rails lose exactly $C_0$ with
$(\ell,t,\eta)=(1,0,1)$; all six families $N10,N01,N11,Pux,Pvy,D11$
are nonempty; $\eta=1$ was computed directly as bridge independence
from the enumerated families, and
$\alpha=-(m-3)/(m-2)\ne-3/2$ since $3+2\alpha=m/(m-2)>0$. The general-$m$
exhaustion and independence proofs are correct in prose; the
admissibility (3-connectivity) argument is sound. Verified.

**Remaining assertion (§8).** J192 — universally
$\Delta\le1$, and $\beta\notin L_0+U$ whenever $\Delta=1$ — is an exact
restatement of exchange (since $\eta\in\{0,1\}$), with the failure
locus $\Delta\ge2$ or ($\Delta=1$ and $\beta\in L_0+U$). The settled
subcases ($\ell=0$, $t\ge\ell$, $\Delta=1$ with independent $\beta$,
short-gap $\Delta\le1$) are correctly proved. The counterexample
accounting (all 636 historical steps satisfy exchange; step 431's
$\Delta=1$ is paid by $\eta=1$; the I165 count-decreasing pair still
satisfies the affine equality) is quoted as inherited finite evidence,
correctly not rerun. The Q164 naming clarification (historical count
bound $h(G)\ge n/2+2$ vs the stronger affine target $d=n/2+1$, the
latter implying the former) is accurate and worth retaining in the
ledger. Verdict UNRESOLVED is honest.

## Limits that remain binding

Universal exchange remains UNRESOLVED at J192. On short gaps only the
equality case $\lambda=-1/2$ survives; on faces with both arcs long,
both clauses of J192 are open. The equality coefficient is not excluded
even for quadrilaterals (the I171–I172 weight line did not settle it).
No Q164 consequence is claimed; no all-brace generation is assumed.
I178's relations do not transfer to the general step. The I192 record
is unsealed.

## Authentication and independent checks

The [validator](../experiments/i192-parent-validate.py) authenticates
all five detached outputs, exact five-file membership, the five
required anchors (I168/I169/I170/I178 reports and the manuscript,
matching the brief), thirteen additional input records, and the archive
write scope, and re-authenticates the I191–I183 chain. The
[verification receipt](../experiments/i192-parent-verification.json)
passes: matching-lemma enumeration $m=1..8$ (unique single-cycle
pairing in all 1,2,5,14,42,132,429,1430 populations), full prism
enumeration and rational ranks for $m\in\{4,6,8\}$ (structure,
independence, identity (17), lost/survivor sets, $\ell,t,\eta$, family
sizes), the symbolic bridge identity (10), and the inherited 23-stage
sealed replay in **8.639 seconds** with empty stderr. Three
parent-script defects (multigraph cycle traversal, cyclic rung
adjacency at $C_{m-1}$, non-spanning $uv$ paths in $D11$ enumeration,
all in the parent's own code) were caught and fixed; the child's
mathematics needed no repair. All other arguments are prose-reviewed as
written. Neither acceptance gate is lowered.

## Next bounded step

[I193](iteration193-equality-bridge-brief.md) attacks the surviving
failure mode directly: the equality-case bridge exclusion
$\lambda\ne-1/2$ (equivalently $w(F_Q-C_0)\ne-1/2$) on short-gap steps,
with the quadrilateral instance $\alpha\ne-3/2$ as the sharp core, and
the long-gap clause $\Delta\le1$ as the secondary front. Proof,
fully specified counterexample step, or exact obstruction. The
five-file policy and both acceptance gates remain unchanged.
