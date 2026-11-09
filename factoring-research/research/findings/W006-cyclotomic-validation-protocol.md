# Frozen W006 cyclotomic validation protocol

The exact user-authorized protocol is retained byte-for-byte in
`W006-cyclotomic-validation-inputs/research/hypotheses/W006-cyclotomic-prereg.md`.
That protocol governs. The following fixes implementation details before any
target certificate or folded vector is evaluated. One run only; no corpus,
replacement targets, alternative certificates, expanded menu or reruns.

- Targets in order: (1610612737,e=29), (3221225473,e=30).
- Bases for each target: 2,3,5,7,11; stop at the first valid certificate.
  Nonwitness residues stay nonwitnesses. Only proper base gcds are retained
  as composite evidence. All tested bases include gcds and explicit binary
  powering residues. No extra compositeness method will be attempted.
- Symbolic certificate proof: section 5 of the frozen `proof.md` passes.
  The all-unit proof and finite-field/norm implication also pass before run.
- Form N and start degrees 2,4,8,16 only if BOTH target certificates pass.
  Otherwise each unstarted vector and the combined instance remain UNKNOWN.
- Candidate `fold(n,length)` receives exactly those two semantic inputs.
  It is a generator of explicit `(x,y,acc)` multiply-add requests. A frozen
  driver computes `(x*y+acc)%n`, records it, and sends back that result.
  This separation is only instrumentation, not an oracle: the arithmetic
  and charge are explicit. Candidate code has no imports, file reads,
  factors, totients, family labels, enormous binomial, or coefficient call.
- Dense schoolbook convolution visits every i,j (including zero products)
  in increasing index order. Right-to-left binary exponentiation skips the
  unnecessary final square. All operands are reduced on every multiply-add.
  After each vector, the evaluator records every coefficient and its gcd
  with N in increasing index order; it does not stop logging on a split.
- Each case runs in a fresh subprocess with a 1-second cold deadline,
  including process startup/imports and serialization. The whole-run clock
  includes source-hash checking, process setup and outcomes writing; an
  outer `timeout 60s` also caps launch/setup overhead. A durable exclusive
  execution-started marker prevents retries after success or failure.
- Python starts with `-B -X tracemalloc=1`, tracing imports as well as workers.
  The 32 MiB allocation limit is soft, checked on entry, every 64 events,
  and completion. It measures traced Python allocations, not OS RSS/native
  allocations. Counts/time are diagnostics, not certified bit-machine steps.
- At most 20,000 modular multiply-adds per target or degree case. Each
  binary record is four little-endian unsigned 64-bit words x,y,acc,result
  (`struct <QQQQ`, 32 bytes), meaning `result=(x*y+acc)%case_modulus`.
  Scalar powering has acc=0. Full operands and results are retained for
  EVERY multiplication, including squares. Raw product/add width is computed
  before reduction; maximum input/modulus width and sum of squared input
  widths are recorded separately. This prevents growing unreduced integers
  from hiding in a modular event. No scalar `pow` builtin is used.
- 20,000 records use 640,000 bytes. Reserve 64 KiB metadata, enforce the
  1 MiB per-case and 16 MiB overall evidence caps, and retain SHA-256 hashes.
  Case JSON includes cold/worker time, peak traced allocations, event count,
  both width maxima, tested-base event intervals or full coefficient/gcd
  arrays, and trace identity. Gcd internals and ordinary setup arithmetic
  are timed but are not modular multiply-add events; this is disclosed.
- Censoring, errors and unstarted cases are UNKNOWN, with reasons. A hard
  timeout has unknown counters/peak memory and any partial binary trace is
  preserved. No retry or higher budget is permitted. Hypothesis/test-result
  labels are kept separate from the conditional symbolic theorem.
- No scratch imports execute the protocol before freezing. Static parsing and
  source review are allowed. There is no pre-screen numerical self-test.
  Afterwards inspect saved outcomes, hashes and record sizes; do not rerun
  a target or vector. `scripts/check.sh` is a separate required project check,
  outside this screen's budgets, and is not a second screen.

Hashes in `freeze.json` cover this protocol, exact input snapshots, symbolic
proof, sources, candidate and runner before execution. Source PDF retrieval,
proof development and code authoring are preregistration work, not a test run.
The evidence budget includes their retained files in this implementation.

Source reading notes: Granville's PDF text extraction has a broken embedded
font map; the failed extraction is preserved rather than treated as readable
evidence. Pages 1, 8 and 9 were visually inspected. The author's HTML
introduction was also read at
https://www.cecm.sfu.ca/organics/papers/granville/paper/binomial/html/node2.html .
The source scopes are bounded in `proof.md`; no novelty conclusion follows.
