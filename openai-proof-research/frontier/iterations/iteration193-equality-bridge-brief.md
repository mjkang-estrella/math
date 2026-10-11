# I193: the short-gap equality bridge — exclude the coefficient −1/2, or refute

Work only in `/home/mj-kang/Documents/Dev/math/openai-proof-research`.
Read AGENTS.md and `sources/upstream.json`; all OpenAI results at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.
Eight accepted, two remaining. Neither bookkeeping nor technical
progress automatically supplies a substantial finding.

**Program state note:** the E183 line is PARKED (do not reopen
E183/Z184/E182/E181/H180/L179). I192 reduced the universal exchange
residual to the exact assertion J192 and paid the facial-translation
classification. This iteration attacks the surviving short-gap failure
mode.

## Focused context and target

Read these reports in full before any new deduction; their stated
results are parent-reviewed and reusable at their exact scopes:

* [I192](../iterations/i192-exchange-residual.md) and its analytic
  attempt: the exact exchange bookkeeping; the classification (4)
  (compatible facial-translation families are N00 on short arcs, empty
  otherwise); the bridge identity $b=3r+2s_{arc}+a_P+a_Q+a_D$; and the
  short-gap equality reduction: for a step with a one-edge arc $a=ux$,
  in the equality case $t=\ell-1$ one has $D_G=W'+\langle r\rangle$,
  $z=\lambda r\bmod W'$, and **exchange fails iff $\lambda=-1/2$**,
  where $z=F_Q-C_0$ for the actual spanning two-component two-factor
  $F_Q=Q-a+e+f$. On quadrilaterals ($U=V$, $z=r+s$,
  $s=e+f-a-a'$, $s=\alpha r\bmod(L+V)$) failure is exactly
  $\alpha=-3/2$. J192 is the exact unpaid universal assertion.
* [I168](../iterations/i168-cross-class-exchange.md): the original
  residual $t+\eta\ge\ell$ and its three obligations; D168 and M168
  are paid method obstructions — do not reattempt them.
* [I169](../iterations/i169-bridge-independence.md): the prism exchange
  theorem and quadrilateral recovery at scope.
* [I170](../iterations/i170-quadrilateral-coefficient.md): H170 and
  R170; the refuted blanket containments are paid negative results.

The target is the **short-gap exchange theorem**: for every admissible
step $G\to H$ (the I168–I170 class, hence in particular brace steps)
with at least one one-edge complementary arc, $d(H)\ge d(G)+2$. By the
paid reductions this is exactly:

> For every short-gap equality-case step, $\lambda\ne-1/2$;
> equivalently the normalized functional $w$ on $D_G/W'$ with $w(r)=1$
> satisfies $w(F_Q-C_0)\ne-1/2$; on quadrilaterals, $\alpha\ne-3/2$.

Prove it, refute it by one fully specified failing step (all spaces,
ranks and the bridge computed and verified in writing against retained
or freshly derived data for that step), or isolate the exact remaining
assertion. Note the honesty boundary: even a full proof leaves the
long-gap clause of J192 (both arcs longer than one edge) open, so
universal exchange and Q164 are NOT claimed by this target; say so
explicitly in your verdict.

## The route to investigate

1. **Restate the equality case exactly** from I192 §§4–5, with the
   two-factor interpretation and the quotient uniqueness of $\lambda$.
2. **Structural constraints on $w(F_Q-C_0)$.** $F_Q$ is an actual
   spanning two-factor with exactly two components, one through $e$ and
   one through $f$. Investigate whether brace structure, the stipulated
   manuscript operations (paired states, circulation/Pfaffian sign
   constraints — read actual statements before use), or a parity /
   symmetric-difference argument relating $F_Q$ to Hamiltonian fibres
   bounds $w$ away from $-1/2$.
3. **Two-pairing composition.** On a quadrilateral both arcs are edges;
   the same face admits the complementary deletion pair. Study whether
   combining the two expansions (or expanding an already expanded
   square) constrains the coefficient $\alpha$.
4. **Counterexample branch.** A refutation must be one fully specified
   admissible step with $\lambda=-1/2$ exhibited and verified in
   writing; formal coefficient patterns alone are not a counterexample.
5. **Secondary front (only if the primary resolves):** the long-gap
   clause $\Delta\le1$ of J192. Record any progress separately; do not
   let it displace the primary target.
6. **Three-way verdict:** SHORT-GAP EXCHANGE PROVED (with the long-gap
   boundary stated), REFUTED (verified failing step), or UNRESOLVED
   with one precise remaining assertion and every settled subcase
   proved. Do not nominate a substantial finding.

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

- `frontier/iterations/i193-equality-bridge.md`
- `frontier/experiments/i193_equality_bridge/analytic-attempt.md`
- `frontier/experiments/i193_equality_bridge/reading-and-failures.md`
- `frontier/experiments/i193_equality_bridge/input-authentication.json`
- `frontier/sources/i193_equality_bridge/literature.md`

No research code, graph/state/matching scans or tests, experiments,
historical replay/control rebuild, source copies, snapshots or seals.
No further agents, ancestor/shared-ledger edits, staging, commits or
publication. Preserve failed written routes and reading limits. Write
the five files early with explicit partial status and update them
incrementally as sections stabilize, so an interruption leaves verified
partial state.

Before proof work authenticate all five anchors:

| Output | SHA-256 |
| --- | --- |
| I192 report | `ffc58919a1ce84f086e36e7b7b85c803dbd47c0dd7609046fc44711aa14c126d` |
| I168 report | `696a15a676ba0ecd6e90cb196673c3d21e2f8450755113c7ee1a70d6c285db31` |
| I169 report | `1b36713181c4f3f5b2ea6f084558dca6553bf86a7b863bfca867fee126f17fcf` |
| I170 report | `8345e1d12991cc328a5910e735c6d0fa625f27715b50bbd91af9917974c74096` |
| manuscript | `03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56` |

Also hash this brief, the four reports' finalized parent dispositions,
the I191 disposition (parking record), the I192 disposition and actual
additional inputs. The inherited 23-stage replay and the sealed line's
replays remain finite historical evidence and must not be rerun here.
Return detached hashes, full written deductions or gaps, the
original-target verdict and source/contribution limits. This is an
unsealed proof record.
