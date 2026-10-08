# H025 unchanged-B extension: finite validation rejected

2026-10-08. Independently audited exact negative result. The frozen B layout
fails the registered 5% key-count validation at order 32771. Park this literal
validation attempt without retuning. **No complete ECDLP improvement is verified.**
This is not a proof against every smaller saving or every asymptotic use of B.

## Registered question and execution

Compare unchanged B to both the GWZ-style three-family control and the H019
signed two-family wrapper at orders 32771, 65537, 131071, requiring at least
5% fewer exact uniform-target generated keys at every order. All q scalars,
paid supplied records, useful signed/input/infinity matches, completed blocks,
main cap and full fallback were specified in extension_protocol.md. Seeds do
not apply to exact all-scalar enumeration. Source/protocol were preregistered
in da874c9; the final admission paragraph was added before execution, after
both independent static reviewers cleared their requested fixes.

Sole command, from /home/mj-kang/Documents/Dev/math/dlp-research:

```sh
timeout 60s python3 -B research/experiments/H025/extension_probe.py > research/experiments/H025/extension_results.json.gz
```

Exit 0, status rejected, no error/cap hit. One global 50M-event allowance
included the previous 426964-event debit; no reset or second run occurred.
Recorded total 5018187 = 426964 prior + 4591223 new diagnostic events. This
is bounded-word coverage-enumeration work, NOT EC solver work or throughput.
Lossless gzip retains full arrays/traces (40961 bytes). Later orders 65537
and 131071 are explicitly UNTESTED because the joint gate was already refuted.

## Exact evidence at q = 32771

| Design | Mean numerator (denominator 32771) | Status | Generated keys |
|---|---:|---|---:|
| GWZ-style control | 5667345 | complete | 483 |
| H019 two-family wrapper | 5651256 | complete | 258 |
| B | at least 5372448 | censored at gate rejection | 240 |

Both controls covered all scalars in main. B covered 24673, leaving 8098.
Its current block ended normally, with no pending block. The saved censored
identity gives each discovered scalar its first completed-block cost and each
undiscovered scalar the current 240-key cost. It equals the block survival sum.
Thus every continuation has numerator at least 5372448, and

    20 * 5372448 = 107448960
                 > 107373864 = 19 * 5651256.

This is the exact registered stopping condition. Every earlier B block was
below that strict threshold. The completed B mean is NOT measured by this run.

An additional artifact-only deduction, independently supplied by Astra and
checked by root, strengthens the finite result without running another block.
Each of the 8098 undiscovered scalars needs at least the next completed block
of three keys. Consequently the final B numerator is at least

    5372448 + 3 * 8098 = 5396742,
    20 * 5396742 = 107934840 > 107679555 = 19 * 5667345.

So B cannot achieve 5% fewer keys against the GWZ-style control either.
Its final mean is at least 5396742/32771 (about 164.6804), whereas the complete
control means are about 172.9378 and 172.4469. These inequalities still allow
a smaller positive saving; do not replace them by a claim that B is slower.

Peak recorded search entries were 486, 261 and 243 respectively; B's value
is only for the censored prefix, not its eventual peak. Support/scratch/full
frontier records remain additional. No case reached fallback, so no new
numerical fallback validation is claimed. The complete fallback specification
was not removed from the rejected candidate's hypothetical continuation.

## Review, provenance and limitations

Native Astra /root/h007_additive_relations: NEW static correctness review,
fix review, then separate artifact-only audit, all completed GO. Native Sol
/root/h010_early_dependencies: proposed the extension and separately reviewed
root's concrete instrumentation/provenance fixes, GO for one capped run without
guaranteeing completion. Root implemented and ran it once, then independently
checked hash bindings, event sums, censored identities and the stronger bound.
Artifact checks did not import or rerun the probe. Review chronology and roles
remain in hypotheses/H025-layout-review-register.md.

Source SHA256: db81631dece40655857fb59a6b6181a6a46db1b9a4fd47c76472212b3712f7ba
Protocol SHA256: 32212902ea8a2eebe0e05424a31d80d01629ae112d4cc0dcce0ba1c0ff1fd399
H018 dependency SHA256: 0865eac9be57655ec1ddde3d76f2aba79bff91ea5384110a7d2205041a764da7
All three initial artifacts retain their earlier bytes; their frozen hashes
and the prior debit are bound in the extension output. The prior_run_debit
phase also contains six subsequent setup events: the event CATEGORY debit is
exactly 426964. Do not misread the phase subtotal as the historical debit.

The early small-size B passes remain true. This larger failure invalidates
the registered all-three finite 5% gate; no unsupported independence model,
phase-torus argument or asymptotic extrapolation was needed. Initial arithmetic
screens and extra-frontier costs remain relevant but are not substituted for
full EC arithmetic, memory, setup, lookup and verification measurements. No
particular prime-field curve or cryptographic family was instantiated here.
No new Lean/Audit claim or hardware performance claim follows.

Next step: stop investing in this literal layout and continue independent
mechanism proposals in H026. A future candidate needs a distinct construction
and a credible complete-work rationale; do not tune this test's fixtures or
call known signed/many-giant methods discoveries. Current ordinary classical
reference remains square-root with known constants and memory tradeoffs.
