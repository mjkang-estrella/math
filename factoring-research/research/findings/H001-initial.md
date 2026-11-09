# H001 initial diagnostic

Disposition: **diagnostic supported; favorable-family evidence rejected as a
general-complexity argument**. No new algorithm and no verified improvement.

## Reproduction

```bash
.venv/bin/python -m factoring_lab iterate --hypothesis H001 --config configs/smoke.json
.venv/bin/python -m factoring_lab verify-run research/findings/H001-initial-run
```

Recorded run: 2026-10-08T05:25:40.524550Z. The original output was
research/runs/initial-H001 and was preserved in full as
[H001-initial-run](H001-initial-run/report.md). It includes the exact source
snapshot, hypothesis, config, corpus, raw rows, report, and hash manifest.
The fixed output name was used only for the initial run; future invocations use
fresh timestamped directories. The generator and solver seeds are in config.json.

Results SHA-256:
`a6acfd42c97d3c30d3e3ea8709f3d24d331d9014d1f36b5976337efa59be4221`.
Algorithm source SHA-256:
`adb5cd26560170ed8defc18077f4d180f784eb289a2e4eb806f171463d001441`.

## Evidence

156 attempts in about 4.75 seconds on this machine: 126 composite attempts and
30 prime/0/1 controls. All 122 reported composite successes had independently
checked divisibility witnesses. The four unsuccessful composite attempts were
Fermat on the sampled 20- and 24-bit unbalanced products, each at both seeds;
they stopped at the 20,000-event budget. No worker timed out. Control outcomes
were 28 `no_factor` and two `event_budget` (rho on prime 97).

On the square and close-factor families, Fermat used respectively 8 and 9
recorded arithmetic events at every sampled size. On separated balanced inputs,
its counts were 9, 14, 19, and 164 as bit length increased through 12, 16, 20,
and 24. On unbalanced inputs, counts were 2,714, 13,364, and then two censored
sizes at the budget limit. Rho and trial division solved all sampled composites.

These contrasts support the preregistered diagnostic: choosing favorable factors
can make a known algorithm look almost constant-work across a small range. The
event counts themselves are not bit-operation bounds. In particular, Fermat's
isqrt operations still cost more as operand widths grow.

## Limits and objections

Only one distinct generated instance per family per bit size was sampled; two
algorithm seeds do not increase that count, and deterministic methods ignore the
RNG. This cannot estimate population success rates or determine an asymptotic
exponent. Budget exhaustion is censored evidence, not nontermination. These
Python baselines are neither optimized NFS nor a benchmark of cryptographic-sized
inputs. Tracemalloc and subprocess overhead affect timing. No independent
research review was performed; this is an environment calibration exercise.

The held-out-seed configuration remains unrun. The evidence archive preserves
the tested source; later setup additions to the preregistration gate and Lean
contract do not change the benchmark algorithms or these observations.

## Next action

Turn H002 into a concrete proposal for obtaining useful square relations and
identify a costed primitive that could improve total work. The ability to write
N = a² − b² is already known; a fast all-input method of finding useful a,b is
the substantive missing step. Formalize a focused candidate invariant only when
it helps test or justify that step.
