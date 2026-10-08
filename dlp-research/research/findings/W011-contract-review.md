# W011: independent review of exact fixed-word core contract

Date: 2026-10-07. Status: amended core contract accepted for implementation; query comparison
NOT APPROVED. Internal implementation is in progress, not yet accepted.
Existing Machine/Problem/Goals and accepted count scopes remain unchanged.

Design author: native Sol `/root/small_curve`, owns only
research/proposals/W011-fixed-word-contract.md. The final draft SHA-256 is
`7a730bca3238729da82b397fd40f9071f6a0e66374e51c19afd3fed08ff05864`.
Author reports formatting checks only, no Lean compilation/proofs. It responds
to the rejected W010 design and the complete recorded objections, not merely
its original headline proposal. This draft is a concrete review target.

The proposal fixes positive word/register widths, fixed heap capacity, exact
bitvector input length and disjoint output region, typed code with 13 opcodes,
explicit next PC, pre-state operand reads and deterministic aliasing, atomic
faults, metered R+M+L setup, one shared fuel budget, distinct terminal outcomes,
exact attempt events, reported capacities, and actual unary/prefix serialization.
The proposed units explicitly abstract host/bit/hardware work; no conversion
to tape cost or whole ECDLP claim is supplied. Query-program refinement would
be a later stage with its own input layout and separately visible preparation.

## Review assignments

- Native Astra `/root/encoding_review`: read-only operational consistency,
  exact state/instruction/setup/fuel/alias/fault behavior, theorem obligations
  and required boundary tests. Original W010 rejection and exact draft supplied.
- T3 Claude Opus 5.5: separate read-only adversarial cost-admissibility,
  setup/metadata/advice/uniformity, serialization and fair comparison review.
  Request `ecdloop-w5-word-contract-opus-20261007-r1`; task ID
  `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w5-word-contract-opus-20261007-r1`.
  This is a new delegated round with prior evidence and objections included,
  not a continuation sent through an earlier child thread.

Both are reviewers only; no children or shared edits. No implementation before
review disposition and an explicitly frozen accepted contract. A qualified
approval of model units cannot become a bit/hardware/tape equivalence claim.

Native Astra preliminary message: no blocking contradiction found in the
13 instruction rules, aliasing, deferred invalid-PC fetch or shared setup fuel;
final theorem/test review still pending. This is not yet final acceptance.

## Completed native operational review

Native Astra approves the exact frozen hash for operational implementation:
no blocking inconsistency. It checked all instruction cases, divmod word bounds
and shared-destination remainder semantics, atomic faults, deferred invalid-PC
fetch, setup/phase boundary and fuel conservation/terminal monotonicity. Exact
R+M+L setup and I-versus-I+1 behavior are consistent. Opcode attempts, completed
loads/stores, initialization writes, capacities and output predicates are distinct.
Serialization field counts match the instruction table; roundtrip and all other
properties are obligations, not assumed theorems. This is specification review,
not compilation or implementation evidence, and not cost-admissibility approval.

Nonblocking implementation clarifications retained with the approved contract:

1. Terminal monotonicity compares fresh runs with identical profile/code/input
   and budgets F versus F+delta. Internal continuation lemmas separately account
   for any prior ledger and must never reset setup or used units.
2. Counters are a projection of a semantic trace, not a lossless encoding of
   event order. Any trace-level claim requires actual trace semantics/refinement.
3. Add combined-precedence tests: overflowing arithmetic with an invalid
   successor faults arithmetically and retains original PC; a successful store
   to an invalid successor commits, then the next fetch faults preserving it.
4. Boundary tests require legal operands: last-address only at M>0, operand2
   only when word-representable, distinct-register cases only with enough R.

No draft edits are needed for these clarifications; the reviewed hash is
unchanged. Coordinator awaits the separate Opus cost/advice/encoding review
before adopting the whole exact contract and authorizing interpreter code.

## Completed Opus review and binding disposition

The retained T3 task completed successfully; its result was read with
`task_status`. Opus conditionally approved only the small-step core, requiring
A1 (ledger equals actual semantic event counts) and A2 (all reported program
cost/solution claims start from raw input and pay setup). Section 10 incorporates
both. Native Astra reviewed those amendments and caught one wording defect:
“fetched instruction” alone omitted invalid-PC attempts. The coordinator made
the exact requested correction to include either invalid-PC fetch or actual
fetched opcode and disposition. Astra's conditional acceptance is satisfied.
The frozen original is retained unchanged at
`research/proposals/archive/W011-fixed-word-contract-r1.md`.

Accepted core contract SHA-256 (verified with `sha256sum`):
`5534f6e80df1196dcee8651c9a657f4278077991deabd786e3eeece429f18d5e`.
The intermediate amendment digest began `520312`; it was NOT the final freeze.

Opus identified five gates before any query comparison: table/query-independent
code/profile/fuel; exact no-advice input encoding; identical sorted-duplicate
input domain with bounded keys/payloads; identical charged setup and matching
exact/worst-case conventions; and ranking on attempts rather than eq/lt counts.
These are retained as future blocking obligations in section 10. No query
comparison is authorized by accepting the core. Word-growth/bit-cost bounds,
program/advice budgets, actual source input production and a tape refinement
remain missing for later solver/family claims. The coordinator does not adopt
Opus's blanket description of every fixed-instance cost theorem as “vacuous”:
such theorems can be valid in an explicit suitable description/advice model.

## Implementation ownership and current evidence

Sol `/root/small_curve` owns only `Research/WordCore.lean`: types, executable
internal guest step, event correspondence, atomicity and boundary checks.
Coordinator owns `Research/WordCodec.lean`: prefix parsers and eventual typed
instruction/program serialization. Neither may silently introduce raw-run cost
claims. Setup, runner, ledger and full codec remain separate proof obligations.
Core API was frozen after its first successful compile; final implementation
review is still required. Coordinator's prefix-parser attempt initially failed
three proof goals (Option bind simplification, modulo one, field recursion);
a second failed attempt exposed an induction hypothesis with an unreduced
empty append. A definitional `change`, `rw` and `rfl` fixed it. Exact command
`timeout 60 ./scripts/lake.sh env lean Research/WordCodec.lean` now exits 0.
No failed algorithm hypothesis or new performance evidence is inferred from
these proof-development failures. New implementation is not integrated/audited
or part of an accepted cost theorem yet.


Subsequent implementation checkpoint: W013 records independently PASSed core
and actual codec, plus integrated `./scripts/check.sh` with 211 audits. This
supersedes the implementation-pending paragraph above, not its recorded history.
Raw setup/runner/ledger and query-comparison obligations remain unaccepted.
