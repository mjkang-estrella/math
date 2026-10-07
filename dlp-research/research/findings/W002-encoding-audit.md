# W002: input admissibility is not enforced by the cyclic interface

Date: 2026-10-07. Status: independently reviewed, kernel-checked negative
examples; final commit diff review pending. This is not an ECDLP improvement.

## Question and falsifiers

Does an injective orbit and an injective bit-list encoding suffice to give a
meaningful ECDLP challenge to the machine? No: it neither ensures operationally
distinct inputs nor prevents uncharged inverse information in those inputs.
Falsifiers for our specific negative examples would be an invalid interface
instance, changed core semantics, non-kernel proof dependencies, or a mismatch
between the stated machine behavior and the actual definitions.

## Reproduced evidence

Opus `claude-opus-5-5`, request `ecdloop-w1-spec-opus-20261007-r1`, task
`node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w1-spec-opus-20261007-r1`
completed an independent read-only audit, with scratch proofs in
`/tmp/dlp-review/Leak.lean` and `Leak2.lean`. Coordinator read both and integrated
their definitions/proofs in `Research/EncodingAudit.lean` under a dedicated
namespace, sharing duplicate helper lemmas and importing Goals directly.

- `leakyFamily` has orders 2^n and uses n-bit scalar values as public point
  encodings. `breakthrough_trivial` satisfies `ExponentBreakthrough` with
  `[halt]`, zero transitions, k=1 and C=1. `concrete_trivial` satisfies the
  fixed-size target with three program bits and zero transitions.
- `relabel P` preserves point type, order, zero and next of any cyclic problem,
  while replacing encoding and parameters. It noncomputably places an orbit
  scalar in the public encoding. `relabel_solved` proves one right move then
  halt suffices. This deliberately inadmissible encoding is NOT an executable
  ECDLP algorithm: its inverse computation is outside the charged program.
- Coordinator's `InputCollision.problem` modifies only the original order-two
  example's encoding: false maps to [] and true to [false]. They are different
  lists but `Tape.ofBits` produces the identical record. `no_solver` proves
  no program at any finite fuel can satisfy `SolvesWithin` for this problem.

Commands: `timeout 60 ./scripts/lake.sh env lean Research/EncodingAudit.lean`
and `timeout 60 ./scripts/lake.sh env lean Research/InputCollision.lean`.
Both passed. EncodingAudit initially emitted deprecated-lemma warnings; replaced
`dif_pos`/`dif_neg` by the suggested `dite_eq_left`/`dite_eq_right`. InputCollision's
first attempts failed on Bool type inference in a structure update and two
reflexive branches after simplification; an explicit Bool binder and reflexivity
completed the proof. No semantics changed to make either example work.

These examples involve no wallet, precomputed attack table, random sampling,
hardware timing or scaling experiment. Only the intentionally exposed secret
encoding in the negative test uses noncomputable choice. All code under test
uses the original machine semantics. The audit's standard logical dependencies
can certify such a theorem without making its input specification appropriate.

## Objections and interpretation

The original README already required reviewed conventional encodings, frozen
families and preprocessing accounting. Thus these examples refute adequacy of
the bare interface as an acceptance gate, not those explicit research rules.
Documentation claiming program size alone excludes inverse tables is corrected;
the core propositions and interpreter are unchanged.

Opus's further informal claims are NOT yet accepted: that an every-n prime-order
EC family needs an unsolved short-interval prime theorem; that the tape layout
unconditionally implies T >= parameter length; and that this bounds generic
advice benefit to q^(1/3). Those require additional hypotheses and justification.
Independent native Astra `/root/encoding_review` gave a qualified pass for
committing all three negative examples and independently compiled scratch and
integrated versions. It confirmed that `relabel` changes both encoding AND
parameters, and that the examples leave the coordinate toy unaffected.

Its objections refine the informal claims:

- No reduction from the dyadic order intervals to an unsolved prime-gap problem
  has been given. Do not adopt that assertion. Also, n=0 forces q=1, so a literal
  prime-order constraint at every existing index is impossible even before any
  asymptotic construction issue. A later family layer must handle finite exceptions.
- T >= parameter length is false unconditionally (order one can halt). For
  q>=2 the reviewer finds a credible first-output-bit locality argument, still
  unformalized. This does not establish any q^(1/3) advice tradeoff; the generic
  theorem's access model and costs would need matching hypotheses.
- Tape-record inequality is not enough either: [true] and [true,false] store
  different records but have the same blank-extended observable contents.
  Fixed-width/framed serialization should be proved to have an observable
  decoder, while admissibility against secret-revealing encodings remains a
  separate independently reviewed constraint.

Final `./scripts/check.sh` passed 53 named dependency audits (11 screened
files, 25 build jobs) after integration; all reports use only allowed standard
logical dependencies. No core definition or interpreter changed. The only
Goals.lean edits clarify comments about program-size scope and family order
bounds. These validation results cover the negative statements, not a stronger
ECDLP acceptance policy.

The seven-point coordinate example uses ordinary fixed-width coordinates,
not the negative-test encodings. Nevertheless a concrete curve alone does not
solve uniform family admissibility, parameter-generation cost or tape refinement.

## Next distinct step

Independently review these proofs, audit all supporting declarations, preserve
them as regression counterexamples, and specify a separate computable EC input
layer with fixed coordinate framing and explicit parameter generation. Do not
silently weaken or replace the frozen core goal. A later acceptance criterion
must reject the deliberately leaky encodings and address the tape collision.
