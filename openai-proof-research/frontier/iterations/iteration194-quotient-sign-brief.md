# I194: the quotient sign conjecture — positivity of w on the canonical two-factor

Work only in `/home/mj-kang/Documents/Dev/math/openai-proof-research`.
Read AGENTS.md and `sources/upstream.json`; all OpenAI results at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.
Eight accepted, two remaining. Neither bookkeeping nor technical
progress automatically supplies a substantial finding.

**Program state note:** the E183 line is PARKED (do not reopen
E183/Z184/E182/E181/H180/L179). I192 paid the facial-translation
classification and reduced universal exchange to J192; I193 paid the
pairing symmetry and central-square composition and reduced short-gap
exchange to J193. This iteration attacks the sharp residue of J193.

## Focused context and target

Read these reports in full before any new deduction; their stated
results are parent-reviewed and reusable at their exact scopes:

* [I193](../iterations/i193-equality-bridge.md) and its analytic
  attempt: the short-gap equality case is exactly $\lambda=w(F_Q-C_0)
  =-1/2$, where $w$ is the unique normalized functional on
  $D_G/W'$ with $w(r)=1$ and $F_Q$ is the actual spanning
  two-component two-factor $Q-a+e+f$; the pairing symmetry (5)–(7);
  the central-square composition (8)–(12) including
  $\Delta_c=\eta_{first}$ and $\lambda_c=\lambda/(1+2\lambda)$; the
  proved sufficient conditions (single-flip Hamiltonicity gives
  nonnegativity; integer span gives integrality; odd primitive lattice
  value $m$ excludes $-1/2$); and the exact remaining assertion J193.
* [I192](../iterations/i192-exchange-residual.md) and its analytic
  attempt: the facial classification, the bridge identity, J192, and
  the prism values $\lambda=1/(m-2)>0$.
* [I168](../iterations/i168-cross-class-exchange.md),
  [I169](../iterations/i169-bridge-independence.md),
  [I170](../iterations/i170-quadrilateral-coefficient.md): the original
  residual and H170/R170; D168 and M168 are paid method obstructions.

The target is the **quotient sign conjecture**: for every admissible
short-gap equality-case step, $w(F_Q-C_0)\ge0$. A proof implies J193
(since $-1/2<0$) and hence the short-gap exchange theorem. The parent
has verified $\lambda=1/(m-2)>0$ on the prism family, so all verified
instances satisfy strict positivity. Prove the conjecture, exhibit one
fully specified admissible step with $w(F_Q-C_0)<0$ (a decisive
structural datum: if the value is exactly $-1/2$ it refutes short-gap
exchange; any negative value refutes the conjecture and redirects the
line), or isolate the exact remaining assertion. State explicitly in
your verdict that even proving the conjecture leaves the long-gap
clauses of J192, universal exchange and Q164 open.

## The route to investigate

1. **Restate the sign question exactly** from I193 §§1,5, including
   anchor independence and the quotient uniqueness of $w$ on $D_G$.
2. **Extend the single-flip subcase.** I193 proves $w(F_Q-C_0)\ge0$
   when every alternating-cycle flip from a surviving $C$ toward $F_Q$
   stays Hamiltonian. Characterize when a flip fails (the flipped
   two-factor gains a component), and whether brace structure forces a
   flip order whose intermediate factors stay Hamiltonian or whose
   $w$-contributions telescope with controlled signs.
3. **Decomposition with signs.** $F_Q$ splits into perfect matchings
   $M_1,M_2$; its complement is a third matching $M_0$. Investigate
   signed relations among the unions $M_0\cup M_1$, $M_0\cup M_2$,
   $M_1\cup M_2$ and Hamiltonian cycles that could bound $w(F_Q-C_0)$
   below zero, using only proved facts (the manuscript operations are
   stipulated; read actual statements before any use).
4. **Counterexample branch.** A refutation must be one fully specified
   admissible step with the families, $w$, and the negative value
   exhibited and verified in writing; formal patterns are not
   counterexamples.
5. **Three-way verdict:** SIGN CONJECTURE PROVED (and J193 /
   short-gap exchange stated as its corollary, with the long-gap
   boundary explicit), NEGATIVE VALUE EXHIBITED (verified step), or
   UNRESOLVED with one precise remaining assertion and every settled
   subcase proved. Do not nominate a substantial finding.

## Stopping rule

This is the final focused attempt on the short-gap front. If the
outcome is UNRESOLVED without a decisive new constraint (a proved
structural dichotomy or a verified negative instance), report so
plainly; the parent will then park the short-gap front beside E183 and
reconsider the remaining surfaces (the long-gap clauses of J192, the
numerical count bound, (T)).

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

- `frontier/iterations/i194-quotient-sign.md`
- `frontier/experiments/i194_quotient_sign/analytic-attempt.md`
- `frontier/experiments/i194_quotient_sign/reading-and-failures.md`
- `frontier/experiments/i194_quotient_sign/input-authentication.json`
- `frontier/sources/i194_quotient_sign/literature.md`

No research code, graph/state/matching scans or tests, experiments,
historical replay/control rebuild, source copies, snapshots or seals.
No further agents, ancestor/shared-ledger edits, staging, commits or
publication. Preserve failed written routes and reading limits. Write
the five files early with explicit partial status and update them
incrementally as sections stabilize, so an interruption leaves verified
partial state.

Before proof work authenticate all six anchors:

| Output | SHA-256 |
| --- | --- |
| I193 report | `e1402e6ec2561f35f3b6d0b5c67361afdb907652b5815134fb2215b6bcb59cb5` |
| I192 report | `ffc58919a1ce84f086e36e7b7b85c803dbd47c0dd7609046fc44711aa14c126d` |
| I168 report | `696a15a676ba0ecd6e90cb196673c3d21e2f8450755113c7ee1a70d6c285db31` |
| I169 report | `1b36713181c4f3f5b2ea6f084558dca6553bf86a7b863bfca867fee126f17fcf` |
| I170 report | `8345e1d12991cc328a5910e735c6d0fa625f27715b50bbd91af9917974c74096` |
| manuscript | `03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56` |

Also hash this brief, the five reports' finalized parent dispositions,
the I191 disposition (parking record) and actual additional inputs. The
inherited replays remain finite historical evidence and must not be
rerun here. Return detached hashes, full written deductions or gaps,
the original-target verdict and source/contribution limits. This is an
unsealed proof record.
