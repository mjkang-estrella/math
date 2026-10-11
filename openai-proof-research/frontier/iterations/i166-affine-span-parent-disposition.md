# I166 parent disposition: brace sample exhaustive-affirmative, theorem still open

Date: 2026-10-11. **Gap report retained; no substantial nomination.
Eight accepted findings remain eight.**

The parent read the complete [I166 report](i166-affine-span-braces.md),
all owned diagnostic and sealing scripts, and reproduced its sealed
evidence. Its conclusions are author-level results backed by exact finite
certificates and sealed replay, not an independently proof-passed
universal theorem.

## What I166 established

- **Audit:** every audited I165 interface passed independent
  re-derivation with a fresh toolkit (counterexample certificates,
  cycle sets 576/572, boundary decomposition 138/52/38/44, family
  arithmetic checked at five orders with splice/expansion commutation,
  affine ranks 26/28, facial-toggle witness, short-side injection,
  and the affine splice formula proof checked line by line). The GSW
  tight-cut/brace-reduction contracts were re-read against the actual
  text and pass in stated scope.
- **Exact sample evidence:** 452 diagnosed records (443 distinct graphs,
  438 distinct braces, orders 8–64), every graph with Hamiltonian cycles
  enumerated by two independent enumerators with set equality enforced,
  every affine rank computed by exact rational elimination. **Every
  sampled graph has full affine dimension $d=n/2+1$; no Q164 violation;
  tightness exactly on even prisms.** Generation is anchored to the
  published census OEIS A007083 through order 20.
- **New certified structural facts (technical, new to this project):**
  1. The 18-vertex brace B18 has **no brace-only C4-generation from the
     cube** — certified three independent ways (expansion-DAG
     reachability, an order argument, and a direct 12-application
     contraction sweep). Brace induction cannot stay within braces.
  2. A **proved** face-toggle lemma: toggling a Hamiltonian cycle along
     any face on which it alternates always disconnects; empirically
     0 of 5795 sample faces are toggleable. Facial switches can never
     witness affine spanning.
  3. A quantified **survival obstruction**: in 136 of 142 tested
     expansion steps the cycles using the expansion edges fail to span
     the parent affine hull (deficit up to 5), so a transport proof of
     the exchange step $d(H)\ge d(G)+2$ cannot work; the extra two
     dimensions must be carried by the spanning-path classes.
- **Not achieved:** the brace theorem (T) $d(B)=n/2+1$ is neither proved
  nor refuted; Q164 remains unproved and unrefuted. Sample evidence
  proves nothing universal.

## Parent replay and preserved scope

The [parent verification receipt](../experiments/i166-parent-verification.json)
records a successful isolated, bytecode-disabled replay (~1479 seconds).
The parent checked the exact owned domain, all 26 payload hashes, the 20
external byte bindings (I165 payloads as data, family-180 blobs, context
snapshots), and the seal/prevalidation hashes **before** any diagnostic
execution. The replay recomputed the self-tests, the I165 audit, the
expansion BFS and census match, both walk batches, the 240 splice checks,
the survival sweep, and the C4-contraction sweep, with full JSON equality.

One parent-side note: the first replay wrapper wrongly required empty
stderr; the owned verifier legitimately writes progress counters there.
The replay itself passed with the sealed hashes; the wrapper contract was
narrowed and everything rerun from the byte prechecks. This is recorded
in the receipt. No sealed bytes changed.

Report SHA-256:
`b85346fd77aca2a38bcbdb9e29d10fbb5c6b025e42fb16e7ff1777b61ef1b7ec`.
Seal SHA-256:
`8e080e006b78700ad4487adb569fabf236fd96f8fba615376d5260dd02a4c717`.

Literature status: no source found stating or refuting the affine-span
statement for this class; retrieval-only, not a novelty certification.
McCuaig's brace-generation theorem (J. Graph Theory 38, 2001) remains an
unread lead. Clean-clone reconstruction untested. The
[integration receipt](../experiments/i166-parent-integration.json)
records exact dependency, syntax and staging scope checks.

## Focused continuation

[I167](iteration167-exchange-step-braces-factory-astra-task.json) is a
fresh Factory/Astra round. It independently audits I166's new content
(face-toggle lemma, B18 certificate, survival analysis, census anchor),
then attacks the exchange step $d(H)\ge d(G)+2$ through the
constant-weight system at a C4 expansion — knowing the spanning-path
classes must carry the two extra dimensions — and evaluates McCuaig's
brace generation as an alternative induction backbone compatible with
the proved affine splice formula.

A failure of the exchange step redirects the route but refutes neither
(T) nor Q164. Any proposed complete theorem still needs renewed primary
comparison and separate acceptance gates. The parent read back the
complete dispatch without truncation. No existing task, I31 work, or
closed oracle/BFSS contribution gate is duplicated.
