# Preserved failures

Attempts 01–04 exceeded sampled group RSS2800MiB while loading broad probability imports, before mathematical elaboration. Attempts 05–11 contain actual failed elaborations: missing scoped numeric notation, HasSum conversion, ENNReal arithmetic and PMF singleton unfolding. Attempt12 passed. No failed declaration is imported into the final modules.

poisson01 failed because ClockMarginals had not yet compiled. poisson02, after ClockMarginals compiled, exceeded RSS with the pinned Poisson.Basic import. The attempted source is retained as failed-PoissonWords.lean.txt; it has no certified theorem status. failed-broad-import.lean.txt and failed-independence-import.lean.txt preserve earlier import versions. The combined Audit.lean attempt exceeded Lean's -M2700 allocation limit (exit -6); Audit.log, Audit.guard.json and its source remain preserved. Split audits pass within the same limits.

The central failure is mathematical/formal incompleteness: no certified sorted finite event sample, no arbitrary-partition Poisson factorization, no independent clock paths, no chronological all-word probability law, no expectation-series identification. The new product laws prove prerequisites only. No sourcePASS is claimed.
