# Factoring research environment

> User-requested shutdown/handover in progress. Do not start or resume research
> without explicit user instruction. Read [HANDOVER](research/HANDOVER.md).

An executable, bounded research loop motivated by
[George Hotz's polynomial-time factoring post](https://geohot.github.io/blog/jekyll/update/2026/03/16/polynomial-time-factoring.html).
The target is a uniform classical algorithm polynomial in the **bit length** of
an arbitrary composite integer. The post supplies conjectures, not an algorithm.
Current verified algorithmic improvement: **NONE**.

This directory combines Python experiments with focused Lean specifications.
It does not claim to solve factoring, prove P = BQP, or automatically generate
ideas. Factoring and general quantum simulation have separate proof obligations.

## Start

```bash
cd /home/mj-kang/Documents/Dev/math/factoring-research
./scripts/bootstrap.sh
./scripts/check.sh
.venv/bin/python -m factoring_lab factor 10403 --algorithm rho
.venv/bin/python -m factoring_lab iterate --hypothesis H001 --config configs/smoke.json
.venv/bin/python -m factoring_lab verify-run research/runs/<returned-directory>
```

Python 3.11+; only the standard library is used, with no pip installation or
network needed for experiments. This machine's local `.venv` is created by the
bootstrap script. Lean 4.34.1 uses its bundled Std library. The wrapper first
looks for `.tools/lean-4.34.1-linux`, then reuses the existing pinned binary in
the sibling dlp-research project, then tries system `lake`/elan. No sibling files
are modified. On another machine, install [elan](https://lean-lang.org/install/)
and the toolchain pinned in lean-toolchain; no sibling project is required.

## Research interface

- **Claim:** return d with 1 < d < N and N % d = 0; time polynomial in N.bit_length().
- **Experiments:** known trial division, Fermat and Pollard rho; exact synthetic
  balanced, close-factor, unbalanced and square inputs plus edge controls.
- **Measurements:** all outcomes, arithmetic event vectors, operand widths,
  tracing-enabled elapsed time, Python peak allocations, seeds and source hashes.
- **Formal checks:** witness contract, cofactor decrease, and sound/complete
  exhaustive search; separate deterministic/randomized polynomial goal definitions.
- **Continuation:** [RESEARCH_LOOP.md](RESEARCH_LOOP.md) is the agent brief;
  [research/STATE.md](research/STATE.md) is the checkpoint.

Each `iterate` freezes the hypothesis, configuration, corpus, and exact source
files before recording JSONL outcomes, manifest, and a Markdown report in a new
run directory. Existing evidence is never overwritten. A worker gets only N, its
random seed, and limits. This is a trusted-code experiment harness, not an OS
security sandbox. Event counts and squared-width proxies are diagnostics, not
proved bit complexity. Read [the full contract](docs/SPECIFICATION.md).

The smoke suite is deliberately small and public. The alternate seed config is
also public; it cannot supply adversarially blind evaluation. Tests validate
small-input correctness and the harness, not asymptotic scaling. No NFS engine,
quantum simulator, external model API, or recurring scheduler is installed.
The user has now authorized an active T3 research loop; see RESEARCH_TEAM.md and
research/STATE.md for delegated work. Current experiments find a split, not a
full factor tree.

## Continue the loop

Ask the research agent:

> Work in factoring-research. Read RESEARCH_LOOP.md and research/STATE.md.
> Perform one bounded algorithm-research wave. Preregister a concrete hypothesis,
> test its cheapest decisive falsifier, prove a focused Lean lemma if useful,
> and record a disposition and next step. Keep general classical factoring and
> P = BQP separate; report failures and full cost assumptions.

Use [research/templates/HYPOTHESIS.md](research/templates/HYPOTHESIS.md) for new
ideas. Register candidates in factoring_lab/algorithms.py. Changes to the input
contract, benchmark distributions, or cost interpretation are explicit research
changes, not ways to make a candidate pass. Consult [sources](docs/SOURCES.md)
and refresh the primary literature before claiming novelty.
