# H034 unexecuted source checkpoint

Status: UNVALIDATED SOURCE; execution not admitted. Verified improvement NONE.
The main square-root reference and hardness assessment remain unchanged.

Separate native Sol implementer /root/h034_c4_implementation completed only
research/experiments/H034/c4_probe.py. Root measured SHA256:
`9ea5b055446f8b4f3b4f6b393ddf5569b1d366d003123f2f93a54b6814c21ba3`.
Frozen protocol v2 SHA256:
`585fd2af0fefb448a3cb85ab2041aea1b604f30fd9aab87efa3cbca7d69d0812`.
No module import, numerical execution, PRNG sampling, warmup or selftest occurred.
Writer parsed source with ast.parse and compiled the AST without executing the
code object. Root reviewed source text and verified hashes. This is not a run.

## Draft corrections before the frozen hash

Root and writer caught persistent graph variables overwritten by leaf lookup
locals. The corrected iterator uses graph_s/t/x/y. Root also required maintained
point/line row bases instead of extra per-edge multiplication. A separate
reference_candidate_batch decodes each ordinal independently and checks buffered
endpoints before full affine comparisons. Shared wrong iterator output therefore
cannot make arithmetic-only reference checks pass. The writer corrected arm
completion so interruption before the harness scalar comparison stays incomplete.
Independent reviewers must verify these repairs, not trust the reports.

## Static estimates, not measurements

Writer supplied the following deliberately conservative stage allowances. These
are pending independent audit; they are not experimentally validated bounds on
Python time or a guarantee that the aggregate budget covers every case.

| Stage | q73 | q103 | q271 | q8053 |
| --- | ---: | ---: | ---: | ---: |
| Eager roots | 30k | 33k | 46k | 480k |
| Seed scan and recovery | 15k | 15k | 20k | 100k |
| Leaf cap including references/recovery | 40k | 50k | 80k | 750k |
| One full H019 control | 50k | 60k | 100k | 350k |

With w=bitlen(q-1), v=bitlen(p-1), writer used C=10v+28 for one
complete affine add and V=2w*C+6w+1 for scalar multiplication. Proposed eager
root envelope is n(2w*C+18w+40)+2(w-1)C+30w+100, before extra rejected
RNG words: 26530,29170,40726,433718 events. Each rejected word adds10.
An expanded inverse uses at most10v+5 events in the declared primitive model.
Blinded fallback adds a primary arm plus at most2V+200 shift/verification work.
Public/certification allowances are approximately100k/50k/70k/100k; first
includes the forced fallback component. Some rough stage allowances are not
accompanied by a complete symbolic derivation and are not accepted as theorems.
No retuning, budget increase or retry is proposed. Later cases may be untested.

## Independent source admission reviews

Native Astra /root/h007_additive_relations reviews correctness, graph order,
reference separation, recovery and H019 sequence. Factory Fable5.1 reviews costs,
capacity fairness, event limits, exceptions and evidence persistence under new
T3 task:
`node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h034-source-cost-fable-20261008-r1`.
Both are read-only, pinned to the source/protocol hashes above, with no execution,
imports, edits or child work. Previous protocol findings and root qualifications
were supplied. Any material source change invalidates this pinned review scope.

The source still implements the older C4-free graph. The thickened-incidence
paper option does not change this diagnostic. Even successful finite checks
would establish neither an improved algorithm nor full-size performance.
Only after reviews may root admit the single command frozen in protocol.md.

## Native correctness review result

Astra completed its pinned read-only audit: scoped GO for the single capped
diagnostic, subject to independent cost audit and root admission. No source
correctness blocker found. It checked graph recurrence/ordinal decoding
(lines478–486,642–649,718–745), eager-root seed invariant(655–714), paired6A
(535–565), both-sign recovery and fallback(613–649,758–779,948–974), increasing
index H019 buffers and per-index search(788–945), reference-only checks
(569–610,1071–1124), and completed harness comparison(1140–1158).

Minor reporting qualification accepted without changing pinned source:
`generated_leaf_keys` increments after reference validation(line747). A cap
during reference therefore leaves this counter at the number in fully validated
batches, not every arithmetically generated output. Completed arms are unaffected;
the raw charged ledger includes partial work. Do not infer missing work from
this counter in a censored artifact. No execution/import occurred in review.

Validation: `./scripts/check.sh > /tmp/ecdlp-h034-source-checkpoint-check.log 2>&1`
exit0,366 existing dependency audits. Existing checks do not import or execute
this diagnostic. No Lean/Audit claim changed. Cost review remains pending.
