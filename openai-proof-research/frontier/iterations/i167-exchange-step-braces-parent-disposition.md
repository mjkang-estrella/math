# Parent disposition: I167 exchange-step audit and corrected constant-weight system

**Date:** 2026-10-10. **Scope:** parent-side verification and integration
decision for [I167](i167-exchange-step-braces.md). The original I164,
I165 and I166 reports and seals are unchanged. No finding-count change.

## Verification performed by the parent

1. **Hash precheck before any child code execution.** All 27 owned
   payloads (report, four diagnostic/support/audit scripts, three JSON
   payloads, preserved attempt artifacts) match the sealed inventory.
   All 68 non-context external bindings match, including the immutable
   I166 report SHA-256
   `b85346fd77aca2a38bcbdb9e29d10fbb5c6b025e42fb16e7ff1777b61ef1b7ec`
   and seal SHA-256
   `8e080e006b78700ad4487adb569fabf236fd96f8fba615376d5260dd02a4c717`.
   Receipt: `frontier/experiments/i167-parent-verification.json`
   (replay output) plus the precheck transcript below.
2. **Sealed replay.** `python3 -I -B .../verify.py` (sealed-replay mode)
   returned PASS in 28.13 s with empty stderr. All three diagnostics
   (`diagnostics.py`, `support.py`, `reduction_audit.py`) regenerated
   byte-identical payloads deterministically. Seal bindings, report hash
   `3e23c1ff...`, prevalidation hash all match; the audit hook forbade
   writes, network, subprocesses and ancestor-code execution.
3. **Context-ledger exclusions reviewed.** The replay policy excludes
   exactly the two shared progress ledgers (`frontier/TEN-FINDINGS.md`,
   `frontier/iterations/README.md`) that the parent edited concurrently
   during the I166 integration, after I167 bound them at launch. The
   preserved `context-drift-01.json` records the original and drifted
   hashes; the parent precheck confirmed the drift receipt's initial
   hashes equal the original binding values. These files are progress
   context, not mathematical premises; no original I164/I165/I166 byte,
   source or payload is excluded. This is the same drift pattern recorded
   in `i166-parent-integration.json`, handled pre-seal this time.
4. **Mathematical reading.** The parent read the full report and all
   owned scripts (`kernel.py`, `diagnostics.py`, `support.py`,
   `reduction_audit.py`, `verify.py`, `seal.py`) and source manifests.
   Payload summary numbers were independently re-read and match the
   report: 636 face-labelled expansions, 0 exchange failures, required
   extra-rank distribution $2{:}138, 3{:}441, 5{:}34, 7{:}13, 9{:}10$,
   single-class path fullness $0/636$, joint within-class fullness
   $8/636$, 240/240 splice rows, 161 faces all alternating with none
   toggleable, retract witness $14$ unrestricted versus $8$ typed
   Hamiltonian cycles.

## Verdict on the audit failure (preserved, not repaired)

I167's explicit witness that **I166's Section 5 aggregated
constant-weight equations fail as written** is accepted. On the expanded
cube with the unit vertex potential at the new corner $p$, every child
Hamiltonian cycle has weight 2 and $\delta=0$, but the length-three
aggregated parent weights give $N_{10}$ aggregate 2 and $N_{01}$
aggregate 0, so no common $\gamma$ exists. The witness is a genuine
vertex potential on an actual admissible expansion, so the failure is of
the stated necessary condition, not of an auxiliary hypothesis. The
original I166 report bytes are untouched; the failure stands in the
record exactly as I163's and I154's original failures do.

The corrected complete six-class system **CW167** (normalized parent
weights $W(uv)=t_u+t_v-a$, $W(xy)=t_x+t_y-b$; per-class equations with
exact cross-class offsets for $P_{ux}$, $P_{vy}$, $D_{11}$; no $N_{00}$
equation) is proved in the report by exact fibre bookkeeping, and the
signed-weight replay checks every coefficient formula on complete class
sets for all 636 tested expansions. The parent reviewed the proof's six
fibre decompositions and the planarity exclusion of the crossing pairing;
the argument is elementary and complete. CW167 is a corrected interface,
not a solved exchange lemma.

## Verdicts on the new I167 content

- **P167 (universal fixed-terminal path-rank deficit):** accepted as
  proved. The forced-edge observation plus the connected bipartite
  incidence-rank formula on $G-\{v,y\}$ is a valid full-scope argument;
  the strict inequality $\dim\operatorname{aff}P_{ux}\le\beta(K)-2+
  \epsilon<\beta(K)$ is correctly derived. Its consequence (within-class
  path constancy alone cannot force potentials) is correctly drawn.
- **Transported-hull identity:** accepted; the lift map is explicitly
  invertible, so the transported affine dimension equals $d_{\rm surv}$,
  and the new classes must supply $2+(d(G)-d_{\rm surv})$ directions.
- **A167 (dual-tree antichain):** accepted as proved; the two-boundary-edge
  argument for a component between nested tree partitions is correct and
  the 3-edge-connectivity hypothesis applies to the planar dual. The
  conclusion (no one-direction face transfer preserves Hamiltonicity) is
  a genuine method exclusion, not a lower bound.
- **McCuaig typed-port interface:** accepted as a correct statement of an
  affine injective correspondence (avoiding cycles = typed retract
  cycles), with the 14-versus-8 witness showing the untyped transport is
  already false at order 16. The needed typed affine theorem for noncubic
  retracts remains unpaid; the original McCuaig 2001 article stays
  retrieval-blocked (HTTP 403), distinguished from absence.
- **Audit passes:** face-toggle lemma, B18 three-way certificates and
  minimality, census anchoring (correctly narrowed: aggregate OEIS
  agreement is an anchor, not program-correctness proof), 240 splice
  instances, original survival statistics, and the exact-rank methodology
  (two independent rank implementations) all pass independent
  re-derivation. The HMM scope correction (order > 8, cube excluded)
  matches the read theorem statement.
- **Honest limits retained:** the 452-record campaign receives metadata
  checks plus 11 independently enumerated samples, not a full dual-
  enumerator replay; the 636 steps are expansion steps, not distinct
  graphs; the single-switch-spanning converse remains an open gap and is
  not used.

## Disposition

**Technical research only; no ninth nomination; no count change. Eight
accepted findings remain eight.** The exchange inequality $d(H)\ge d(G)+2$,
the brace theorem (T) and Q164 all remain unproved and unrefuted. I167's
contribution is a preserved audit failure with a proved correction
(CW167), two proved full-scope obstructions (P167, A167), an exact typed
interface for the McCuaig route, and enlarged exact evidence. These are
the strongest kind of technical results — they repair and redirect the
program — but they close no universal statement.

**Next step (I168).** Work modulo vertex potentials with CW167's
cross-class equations intact. Objective: recover the $d(G)-d_{\rm surv}$
transported-loss directions **and** the two genuinely new directions from
the path classes *jointly* — single-family affine fullness and
within-family-only arguments are excluded by P167 and the $8/636$ joint
statistic. Mandatory first tests: the expanded cube's three singleton
new classes and the recorded expansion steps requiring nine new
directions. Alternative paid target: a typed-port affine theorem for
McCuaig degree-four retracts. A proof of the exchange inequality via
CW167, or a certified counterexample expansion, would each be a
candidate for independent review; neither is assumed.
