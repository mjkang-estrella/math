# I195: the long-gap deficit — the remaining clauses of J192

Work only in `/home/mj-kang/Documents/Dev/math/openai-proof-research`.
Read AGENTS.md and `sources/upstream.json`; all OpenAI results at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.
Eight accepted, two remaining. Neither bookkeeping nor technical
progress automatically supplies a substantial finding.

**Program state note:** the E183 line is PARKED (do not reopen
E183/Z184/E182/E181/H180/L179). The short-gap exchange front is PARKED
at J194/J193 under the I194 brief's stopping rule (do not propose
another short-gap iteration; the parking record is the
[I194 parent disposition](i194-quotient-sign-parent-disposition.md)).
I192 paid the facial-translation classification and reduced universal
exchange to J192; on short gaps $\Delta\le1$ is paid and the equality
bridge is the parked J194/J193 residue. This iteration attacks the
**long-gap clauses of J192**, the remaining surface with the most paid
entry structure.

## Focused context and target

Read these reports in full before any new deduction; their stated
results are parent-reviewed and reusable at their exact scopes:

* [I194](../iterations/i194-quotient-sign.md) and its analytic
  attempt: the exact flip-connectivity criterion (components of the
  flipped factor $=$ components of $\tau\cup\beta$; $q=2$ failure iff
  $\beta=\tau$); the conditional fractional block lemma (7)/(8); the
  three-matching decomposition $F+F_{01}+F_{02}=2E$ with
  $\lambda=\kappa-h(F_{01})-h(F_{02})$; the cube brace obstruction
  (no universal direct-flip certificate); and the exact parked
  assertion J194.
* [I193](../iterations/i193-equality-bridge.md) and its analytic
  attempt: the quotient functional $w$ on $D_G/W'$, the pairing
  symmetry, the central-square composition with
  $\lambda_c=\lambda/(1+2\lambda)$, and the sufficient subcases.
* [I192](../iterations/i192-exchange-residual.md) and its analytic
  attempt: the facial classification (4) ($F_J=N00$ on short arcs,
  $\varnothing$ otherwise, via the noncrossing matching lemma); the
  long-gap collapse (5) ($V_{good}=0$, $R=U$, $\delta_R=t$,
  $\ell=\delta_V+\epsilon$); the bridge extension (6)
  ($b=3r+2s_{arc}+a_P+a_Q+a_D$ with the completed $a$-objects not old
  Hamiltonian cycles on long arcs); the exact residual (3)
  ($\Delta=\delta_V+\epsilon-\delta_R$); and J192 itself.
* [I168](../iterations/i168-cross-class-exchange.md),
  [I169](../iterations/i169-bridge-independence.md),
  [I170](../iterations/i170-quadrilateral-coefficient.md): the original
  residual and H170/R170; D168 and M168 are paid method obstructions.

The target is the **long-gap deficit bound**. On a long-gap step (both
complementary arcs of length $\ge3$, i.e. $k_A,k_B\ge1$), I192's
classification collapses the residual to

$$
\Delta=\ell-t=\delta_V+\epsilon-\delta_R,\qquad
\delta_R=t,\qquad \ell=\delta_V+\epsilon,
$$

so the first clause of J192 is exactly $t\ge\ell-1$ on long gaps,
without the short-gap bijections that proved it there; the second
clause is $\beta\notin L_0+U$ whenever $\Delta=1$. Prove both clauses
(equivalently J192 on long-gap steps; combined with the paid short-gap
bound $\Delta\le1$ this would reduce universal exchange exactly to the
parked short-gap bridge), exhibit one fully specified admissible
long-gap step violating a clause ($\Delta\ge2$, or $\Delta=1$ with
$\beta\in L_0+U$ — a decisive structural datum, and a refutation of
universal exchange if the step is verified), or isolate the exact
remaining assertion. State explicitly in your verdict what a proof
would and would not settle: the short-gap bridge J194/J193 stays
parked, and Q164/(T) gain a conclusion only through the full exchange
theorem.

## The route to investigate

1. **Restate the long-gap residual exactly** from I192 (2),(3),(5),(6),
   including the precise definitions of $L_0,V,U,R,E_J,\delta_V,
   \delta_R,\epsilon,\beta$ and the honest caveat that the absence of
   translated old objects does not imply $U\cap V=0$: directions
   recovered by other linear combinations are the issue.
2. **A paid test family: polygonal-face deletions of even prisms.**
   On the $m$-gon face of $C_m\square K_2$ ($m$ even), deleting two
   facial edges whose removal leaves odd arcs of lengths
   $2k_A+1,2k_B+1$ (summing to $m-2$) gives genuine long gaps exactly
   when $k_A,k_B\ge1$, first at $m=8$ with the $3+3$ split. Determine
   for this family, in writing with complete families: admissibility
   of the step, $N00$ and the six classes, $\ell$, $t$, $\epsilon$,
   $\Delta$, and whether $\Delta\le1$ holds and with what margin;
   check whether $\Delta=1$ occurs and whether $\beta\notin L_0+U$
   there. The parent can verify $m=8$ by exact enumeration (ten
   Hamiltonian cycles), so every claimed value must be exact.
3. **Attack $t\ge\ell-1$ generally on long gaps.** Levers: the
   multi-component generalization of the short-gap two-factor
   machinery (on a long gap, $Q$ minus its positive arc edges plus
   $e,f$ is a $(k_B+1)$-component spanning two-factor; I194's flip
   criterion and matching decompositions generalize); the noncrossing
   matching lemma's control of facial translations; the bridge
   extension (6) and what its $a$-objects contribute to $L+U$; brace
   matching extension in the brace restriction. The I178 five-port
   annihilator relations are scoped to a fixed thirteen-vertex
   exterior; any use must first establish that an arbitrary
   four-terminal long-gap step embeds in that interface, which I192
   explicitly leaves open.
4. **Counterexample branch.** A refutation must be one fully specified
   admissible long-gap step with the families, ranks, and the
   violating clause exhibited and verified in writing; formal rank
   patterns are not counterexamples.
5. **Three-way verdict:** LONG-GAP CLAUSES PROVED (with the exact
   corollary boundary stated: universal exchange reduces to the parked
   short-gap bridge), CLAUSE VIOLATION EXHIBITED (verified step), or
   UNRESOLVED with one precise remaining assertion J195 and every
   settled subcase proved. Do not nominate a substantial finding.

## Stopping rule

This is the focused attempt on the long-gap surface. If the outcome is
UNRESOLVED without a decisive new constraint (a proved structural
dichotomy or a verified violating instance), report so plainly; the
parent will then park the long-gap front beside the short-gap front and
E183, and reconsider the remaining surfaces (the numerical count bound
Q164, (T), or a fresh surface).

## Sources, evidence and exclusive output scope

Use the retained pinned manuscript at
`frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`,
SHA-256 `03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56`.
Read actual needed statements and record ranges; no external theorem
may be invoked unread. The sealed computational infrastructure of
I164–I180 is inherited historical evidence: authenticate referenced
reports by hash, but do not rebuild, rerun or extend any sealed
computation, and do not write research code. This iteration is
proof-only written analysis.

Only these five paths may be written:

- `frontier/iterations/i195-long-gap-deficit.md`
- `frontier/experiments/i195_long_gap_deficit/analytic-attempt.md`
- `frontier/experiments/i195_long_gap_deficit/reading-and-failures.md`
- `frontier/experiments/i195_long_gap_deficit/input-authentication.json`
- `frontier/sources/i195_long_gap_deficit/literature.md`

No research code, graph/state/matching scans or tests, experiments,
historical replay/control rebuild, source copies, snapshots or seals.
No further agents, ancestor/shared-ledger edits, staging, commits or
publication. Preserve failed written routes and reading limits. Write
the five files early with explicit partial status and update them
incrementally as sections stabilize, so an interruption leaves verified
partial state.

Before proof work authenticate all seven anchors:

| Output | SHA-256 |
| --- | --- |
| I194 report | `21f8e32eec69b89d7e6eade2763a3f7b125c6575121f5f05bddb0d37ab21b2b2` |
| I193 report | `e1402e6ec2561f35f3b6d0b5c67361afdb907652b5815134fb2215b6bcb59cb5` |
| I192 report | `ffc58919a1ce84f086e36e7b7b85c803dbd47c0dd7609046fc44711aa14c126d` |
| I168 report | `696a15a676ba0ecd6e90cb196673c3d21e2f8450755113c7ee1a70d6c285db31` |
| I169 report | `1b36713181c4f3f5b2ea6f084558dca6553bf86a7b863bfca867fee126f17fcf` |
| I170 report | `8345e1d12991cc328a5910e735c6d0fa625f27715b50bbd91af9917974c74096` |
| manuscript | `03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56` |

Also hash this brief, the six reports' finalized parent dispositions,
the I191 disposition (E183 parking record) and actual additional
inputs. The inherited replays remain finite historical evidence and
must not be rerun here. Return detached hashes, full written deductions
or gaps, the original-target verdict and source/contribution limits.
This is an unsealed proof record.
