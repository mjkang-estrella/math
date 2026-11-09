# Fresh corpus r14 — no full candidate

Reviewed all **40 literal reserved MathDB records**, preserving exact selected raw lines, original chunk/line SHA-256 hashes and source provenance. Initial reservation unchanged. **Zero new solutions, zero credit, no Lean endpoint or acceptance packet.** Root acceptance remains separate; this lane does not change campaign totals.

Two sustained routes are documented in [ATTEMPTS.md](ATTEMPTS.md):

- **333840, six-vector determinants:** exact optimization within the pentagonal-ring family gives the icosahedral value. A general Cauchy–Binet certificate is too weak; 160 seeded local optimizations found no improvement. The missing obligation is a nonsymmetric universal upper bound or an exact improving witness.
- **334220, three total dominating sets:** 300 sampled closed triangulations all had explicit three-color neighborhood certificates. The known punctured-icosahedron obstruction was reproduced by exhaustive search, but ten doubled-patch gluings and triangular glued families up to 39 vertices all color. The published two-color extension argument fails to supply the required three-color invariant.

Prior-resolution exclusions: **333968** (published Majstorović2023 Theorem4), **334218** (Francis et al2022 Corollary2), **334437** (Davila–Kalinowski–Stephen theorem passage), **334540** (known 2021 bow-tie counterexample, primary search passages only). Depth and publication-version limitations are explicit in [results.json](results.json); the last two are not presented as full proof audits.

Review depth: **34 literal-only**, **3 primary-passage**, **3 selected full-proof-body** reviews. Search-only successor leads do not increase primary-body coverage. Remaining records are parked with ID-specific mathematical obstacles, not claimed resolved or globally open.

Evidence: [literal-records.json](literal-records.json), [raw selected lines](literal-records.raw.jsonl), [source receipts](source-receipts.json), [context receipts](context-receipts.json), [registry receipt reuse](registry-reuse.json), [bounded older-note reconciliation](older-reconciliation.json), [prior-art/access limits](prior-art-limits.json).

Reproduce diagnostics from this directory with `python -m pip install --target .deps -r requirements-diagnostics.txt`, then `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 timeout 240 python diagnostics.py` and `timeout 60 python structured.py`. Versions and resource limits are recorded in [resource-log.json](resource-log.json). These Python computations are diagnostics, not kernel proofs. No Lean cache/rebuild/audit claims are made.

Recent inherited OpenAI/math head and complete preprint-tree receipts were hash-verified and path-screened; no body-level novelty clearance follows. MathDB and Palomar inherited403 gaps were respected without retries. No git, shared-ledger edits, children, external messages, uploads, publication or browser tabs.
