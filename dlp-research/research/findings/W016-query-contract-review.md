# W016: independent review of raw-bit lookup challenge

Date: 2026-10-07. Status: amended policy accepted for data encoding and numbered-template
design only. No query code, numbered graph or comparison is accepted.

Sol `/root/small_curve` authored only
research/proposals/W016-word-query-contract.md, frozen SHA-256
`bd22c845c38d6d3c840affc217f6286fce74199865895c363176a3a413c97f4a`.
This is a separate challenge, not permission to infer costs from W008/W009 or
to change frozen Machine/Problem/Goals. The W011 N1–N5 objections are binding.

The draft fixes public sizes W,m,k; exact complete sorted duplicate-table and
query domains; little-endian header/records/query bits; identical register/heap/
input/output capacities; guest packing from raw bit cells; conventional sorted
sequential versus indexed binary search; relational found/absent payload outputs;
size-only fixed control templates and actual programBits; and rankings using
both guest attempts and total used units. Source table production/sorting/
encoding remains excluded explicitly. Common fuel is a fixed proposed budget,
not a proof of sufficiency. Numbered primitive templates, range/correctness/
termination/ledger proofs and source review remain mandatory later gates.

## Review assignments

- Native Astra `/root/encoding_review`, new read-only operational review:
  encoding/layout/ranges, decoder overflow, zero/full-width paths, fixed register
  assignments, actual template/proof obligations and admission nonvacuity.
- New T3 Claude Opus 5.5 read-only cost/advice review, with original W011
  A1/A2 and N1–N5 evidence/responses supplied. Request
  `ecdloop-w7-query-contract-opus-20261007-r1`; retained task ID:
  `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w7-query-contract-opus-20261007-r1`.
  The task was accepted and is running. It is a new delegate_task round, not
  childThreadId messaging or a top-level conversation. Live catalog refreshed:
  approved target providers/models support child work without reported constraints.

Both reviews are read-only, without descendants. Coordinator alone integrates.
Slots: coordinator, native Astra review, Opus review and existing Grok literature.
Sol's design task completed. No duplicate Grok job or scheduler was created.

## Coordinator questions for review

1. Admission depends on not-yet-frozen code lengths/operands. Ultimately prove
   explicit admitted examples and meaningful parameter ranges; a theorem over
   no admitted size is not completion. No graph length is currently known.
2. Common full guest packing gives a controlled comparison, but restricts the
   sequential baseline: a raw streaming scan could avoid packing later records.
   The draft must not be presented as optimality over all linear strategies or
   as an unavoidable preprocessing cost. Review whether its headline/scope and
   later comparison remain appropriate for the intended refinement milestone.
3. Code policy, input encoding and relational duplicate outputs must stay tied
   to actual primitive instructions and raw execution. The budget definition
   supplies no termination or cost theorem; lowering scope or changing it after
   a failure requires explicit recorded review rather than silent adaptation.

The runner prerequisite has now independently passed W014 (265 integrated audits
including 38 new runner theorems and independent compiled raw-program checks).
That acceptance does not pre-approve this challenge or its future programs.


Native Astra preliminary review found no operational contradiction in layout,
descending-pointer LE decoding, duplicate outputs, checked midpoint or common
packing. It confirms the nonvacuity requirement: after templates are frozen,
prove actual code-admission witnesses for empty/nonempty, zero/full-width and
duplicate/absence-capable examples. Numerically feasible sizes alone do not
prove this. Mandatory packing supports only the prescribed-template comparison,
not an optimized streaming linear baseline claim. Final verdict still pending;
Opus review remains live. No draft change or implementation acceptance yet.

Runner prerequisite is now committed locally as `4120ffc`.

## Completed Opus review (verbatim)

# W016 review: CONDITIONAL PASS

I reviewed the frozen draft with SHA-256 `bd22c845…4a97f4a`; `sha256sum` confirms the hash. I made no edits, staging, commits, child agents or publications. I did not compile anything. I read the source, not just its descriptions.

## Verdict by acceptance stage

| Stage | Verdict |
|---|---|
| Admissibility policy (layout, domain, no-advice rule, units, ranking) | **CONDITIONAL PASS** |
| Milestone 1: data encoder, size admission, profile, numbered templates and the two code constructors | **May proceed**, under conditions C1–C6 |
| Accepting the actual query code or any proof result | **Not authorized.** Conditions C7–C14 must be met first |
| Any comparison or speed statement | **REJECT for now.** No program, proof, sufficiency of the budget `F` or ledger exists yet |

I found no blocking loophole in the policy. The draft is honest that `F = I + 256*(L+4m+32)` is an unproved challenge budget. I infer nothing about whether `F` suffices or about speed.

## The five query gates (N1–N5) for this challenge

- **N1, size-only code/profile/fuel: PASS (policy), conditional.** The graph is fixed. Only `W,L,B,A,A+1,A+2` are substituted, and all of them come from public `(W,m,k)`. Code is never unrolled, so code length is a constant. The profile and `F` depend only on the sizes. This is enough no-advice uniformity for meaningful per-size results, which matches the coordinator's qualified view on the earlier vacuity objection. It is still only prose, though: see C1 and C2.
- **N2, exact no-advice encoding: PASS (policy).** The format is little-endian `bits W m ++ bits W k ++ records ++ bits k x`, with no rank or answer hint and a query-independent table. The header repeats public sizes, which is not advice. Still owed: proofs of length, index equality and injectivity on the domain.
- **N3, identical complete sorted-duplicate domain: PASS.** Both programs face all nondecreasing tables, duplicates with distinct payloads, every query below `2^k`, and the cases `m=0`, `k=0` and `k=W`. The success/absence specification is relational. One caveat: the set of admitted sizes depends on code lengths that aren't frozen yet (C5).
- **N4, identical raw setup and matching conventions: PASS (policy), conditional.** Both programs get the same profile, the same `I=R+M+L`, the same budget, the same identical charged prefix, and fresh `run` only. Two conditions apply: the prefix's identity must be proved, and the segment split cannot be observed from the trace as the draft assumes (C9, C10). The worst-case convention is correctly deferred.
- **N5, ranking on actual attempts: PASS.** Ranking uses `guestAttempts` and `used`, both projected from the trace. `eq`/`lt` counts are diagnostics only.

From the earlier gates, A1 (ledger equals actual trace) and A2 (fresh raw run) are satisfied in principle. WordRun's `ledgerOf` is a projection of the trace, and `Produces`/`output` exist only on `run`.

## Findings

**F1. The prefix/search boundary can't be seen in the trace (needs a fix before results).** Section 3 says parsing versus search is "observed using the fixed prefix-ending PC and the first execution of it." But `WordCore.Event.instruction` carries only the opcode and disposition, not the PC, so a trace projection cannot locate that boundary. WordRun's only split lemma is `continueRun_setup_prefix`, which covers setup only.

**F2. Mandatory full packing is a declared policy, not an artificial asymmetry, but it defines what is being compared.** Because the core input is one bit per cell, some decoding is unavoidable. Requiring all of it is a choice. That choice removes two options:
- a lazy binary search that decodes only probed keys, roughly `O(k log m)` guest work;
- a streaming sequential search that exits early before decoding the whole input.

Both programs pay the same cost, so the comparison stays fair. But it measures only the difference in the search segment on top of a common prefix that grows with `L`. Any results must be labeled "packed-table search under common full packing." No conclusion about lazy or streaming variants is allowed; those would be separate challenges.

**F3. The admitted-size domain isn't fixed yet.** `M≤U` alone forces `W≥4`. The PC targets and the requirement `N≤U` will raise the minimum `W` to about `log2 N`, likely around 8. So `k=W` tests at small `W` won't exist, and exhaustive tests at `k=W` become impossible. The draft's claim that `m<U` and `k<U` follow from the other conditions is correct: `m ≤ L < M ≤ U` and `k ≤ W < U`.

**F4. A stale hedge in milestone 2.** WordRun already has the generic setup-content theorems: `initialized_input`, `initialized_rest_zero`, `initialized_registers_zero` and `initialized_pc_zero`. What it lacks is the full-run corollary that a halted run's ledger contains exactly `R/M/L` setup units and that `used = I + guestAttempts`. W014 says this explicitly.

**F5. Binary search can match the existing lookup exactly.** The midpoint `lo+(hi-lo)/2` and the equals-then-less-than order match `IndexedLookup.search`. So a deterministic refinement is possible: the payload equals `lookup`'s payload, and the loop iterations equal its `probes`. That is stronger than the relational link and gives a check against an oracle that isn't the candidate program.

**F6. Minor ambiguities to settle in the numbered expansion:**
- whether `A+1` and `A+2` appear as inline `const` literals or are computed;
- what register 27 ("saved field start") is used for;
- whether sequential search's two absence exits share one exit block;
- that register 0 is never written;
- that the prefix-ending PC is not a loop target.

None of these blocks the policy.

## Conditions for milestone 1 (encoding and templates)

- **C1.** Each code constructor's Lean signature takes only public sizes and an admission proof, never data. The encoder is a separate function.
- **C2.** Define a single symbolic template with literal slots, plus one instantiation function covering all sizes, with no branching on sizes. Prove `code(W,m,k) = instantiate skeleton (W,L,B,A,A+1,A+2)`. This turns "fixed graph" from prose into a theorem.
- **C3.** Prove the encoder's length is `L`, that its entries equal the bit list index by index, and that it is injective on the domain.
- **C4.** Before implementing the program, freeze the numbered primitive expansion of both graphs with every successor target. This includes the shared prefix's exact PC range and entry point. It needs independent source review, which is Astra's operational scope.
- **C5.** Publish the admitted-size predicate as a decidable function. Prove that both programs admit exactly the same sizes, taking the intersection. Record the resulting minimum `W` and fix test profiles to match it (F3).
- **C6.** Record the committed WordRun SHA-256 that W016's obligations target. WordRun is integrated but not yet committed. Any later change to WordRun reopens the affected obligations.

## Conditions before accepting query code or results

- **C7.** Prove that the budget `F` suffices for every admitted input, from the frozen expansion. If it doesn't fit, record a failure; any change to `F` needs a separately reviewed amendment.
- **C8.** Prove relational correctness through `output (run …)`, using a new relational predicate rather than `Produces` with a single expected vector. Also prove absence of faults, that bits stay 0/1, and that no store lands in `[0,L)` or touches register 0.
- **C9.** Prove that the prefix instruction arrays are identical, and that the prefix traces from the shared initialized state are identical.
- **C10.** Fix F1 by defining the segment split through a proved guest-continuation split lemma. It should take the form `continueRun (a+b) s = prependTrace t_prefix (continueRun b s')`, with `t_prefix` and `s'` characterized. It cannot be defined by a PC that the trace doesn't record. Make segment reporting **required** before any comparison prose, not "if proved".
- **C11.** Prove the full-run setup corollary from F4: a halted run has setup units exactly `I` and `used = I + guestAttempts`.
- **C12.** Link binary search to `IndexedLookup.lookup` exactly (F5). Sequential search must return the first matching location.
- **C13.** Compare results per input with the sign of each difference. Sequential search wins on some inputs, for example a query below the first key, or small `m`. Report crossovers. A worst-case claim needs maxima proved under the same convention for both programs. No average-case claim is allowed without a declared distribution and an exact computation.
- **C14.** Results carry the F2 label, and no claims about growth with word width.

## Assumptions that remain

- One checked-word action is one unit, including `mul` and `divmod`, at any `W`. This is not bit, hardware or tape cost.
- `W` may be much larger than `log M`, and there is no growth bound.
- Producing, sorting and encoding the source table, generating descriptors, and loading code are all excluded.
- Sortedness and header agreement are preconditions, not executed checks.
- Literals and targets are encoded in unary, so program bits and descriptors are noncompact. They are reported but not ranked.
- Setup writes each input cell twice (clear, then copy), the same for both programs.
- There is no transfer to whole BSGS. Standalone query times must never be multiplied by the number of giant blocks.

## Where I disagree with the draft or coordinator

1. I accept the coordinator's qualification of the original vacuity objection. Here the fixed skeleton plus size-only literals supplies the explicit no-advice model. That only holds once C1 and C2 are formal theorems.
2. The draft calls itself "a fair comparison of conventional sequential and binary search." It is fair only under the declared full-packing policy (F2). It is not the only fair baseline.
3. The draft treats the prefix-ending PC as observable and the segment split as optional. I treat both as defects: see C10.
4. "Prove guest/total orderings coincide" is a one-line corollary of C11. It's harmless but no substitute for C11 itself.


## Coordinator disposition and binding amendments

Both reviews give CONDITIONAL policy/design approval, not query-code or result
acceptance. Parent preserved the original at proposals/archive/W016-word-query-contract-r1.md
and incorporated Astra's explicit code-admission nonvacuity gate and Opus C1–C14
in section 9. Current amended hash:
`3aa67dbd8e98de67878d978cb895f3d3763474546ff4ed5dc39c54ec517b92b5`.
Native Astra is independently checking these amendments before stage-1 work.
Authorized scope is only data encoding/profile/admission support and numbered
primitive graph design; constructors wait for independent graph review.

Parent confirmed F1: opcode/disposition events contain no PC. Mandatory segment
reporting must use an actual guest-continuation split. W017 now independently
verifies that generic split and the full fresh-run setup/used identities; these
supply tools, not an unproved query-prefix refinement. The runner is committed
in 4120ffc with exact hash in the amended contract, resolving the stale hedge.

The prescribed common-packing comparison is labeled explicitly, with lazy
binary decoding and streaming sequential variants excluded, not dismissed.
Reviewer predictions of winner/crossover remain hypotheses until final graphs
and counts exist. Parent qualifies the blanket statement that exhaustive
full-width testing is impossible: an admitted empty-table full-width profile
can be enumerable. No minimum W is asserted before actual graphs/admission.

Astra's completed bounded arithmetic review checked 5,392 numerical triples
W≤12 and 4,082 decoder cases W≤10. These unarchived stdin checks are reviewer
reports, not code-admission witnesses or guest-program executions. Formal
admission witnesses and the full universal proof are still mandatory.


Final native amendment check PASSed hash3aa67dbd8e98de67878d978cb895f3d3763474546ff4ed5dc39c54ec517b92b5:
original archive hash unchanged; only status and binding section 9 changed.
All required nonvacuity, graph-review, actual-continuation, packing-scope and
unproved-fuel conditions are incorporated. No operational contradiction or
further correction found. Stage-1 data support and graph design now proceed
with disjoint ownership: Astra only Research/WordQueryData.lean; Sol only
research/proposals/W018-query-instruction-graphs.md. Query constructors still
require independent review of the completed numbered graphs. Neither writer
may change shared imports/audits/checkpoints or commit. No grandchildren.
