# W003: fixed-width encodings give observable input distinction

Date: 2026-10-07. Status: independently reviewed limited formal result;
integrated checks passed. Parent milestone: `c99e349` (W001/W002).

Question: can fixed-width point encodings eliminate W002's blank-tape input
ambiguity without modifying the interpreter or cyclic problem interface?
Falsifier: two distinct scalars with fixed-width encodings and no differing
head observation in the supplied input width, under the original moveRight.

Sol `/root/small_curve` implemented only `Research/Framing.lean`. Seventeen
public theorems cover known-width read recovery, input list injectivity,
observable distinction at a position below the total input length, and the
SmallCurve specialization. `input_observation_distinct` witnesses an actual
different head value after repeated `Machine.Tape.moveRight`, rather than just
different internal tape records. `smallCurve_input_observation_distinct` gives
a position below 25 (18-bit header plus seven-bit coordinates).

Command: `timeout 60 ./scripts/lake.sh env lean Research/Framing.lean`.
Author's first compile passed with no failures. Its temporary audit checked
all 17 public theorems, finding only allowed standard logical dependencies.
Coordinator read the whole source and independently found the proofs match
the statements. Native Astra `/root/encoding_review` independently reran the
compile and reviewed the source: qualified PASS, no blockers or warnings.

Limitations emphasized by reviewer and retained: width is externally supplied;
no parser discovering width, machine decoder program, runtime cost, solver,
secrecy, or advice resistance is proved. A fixed-width encoding can still leak
the secret, as W002 demonstrates. This result resolves observable input
distinction under its explicit hypothesis, not the entire challenge-admissibility
problem. No new acceptance policy or altered core definition.

No experiments, random seeds, preprocessing tables or hardware calibration are
needed for this proof. All public theorem names are listed in Audit.lean;
normal source/dependency checks remain honest-mistake validation only.

Next: retain this property in an independently reviewed concrete EC input
layer, alongside fixed parameter encoding and generation-cost obligations;
continue algorithm/cost baseline work separately.

Integrated `./scripts/check.sh` passed: 12 screened source files, 27 build jobs,
all 70 named dependency audits and executable smoke output. The 17 new framing
theorems use only `propext`/`Quot.sound` or no logical dependencies. No failed
framing builds or counterexamples occurred.
