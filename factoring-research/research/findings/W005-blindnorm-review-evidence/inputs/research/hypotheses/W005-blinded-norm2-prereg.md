# W005 blinded Norm2 — finite distribution check preregistration

Frozen before execution, 2026-10-08. This is a primitive distribution/correctness
check, not a factoring benchmark or asymptotic measurement.

- Cases in order: (N,R)=(49,1),(49,4),(77,1),(77,4),(91,1),(91,4),
  (121,1),(121,4). No adaptive additions or cap increases.
- Evaluator enumerates x with x^2=R mod N. For every 0<=a,b<N,
  classify gcd(a^2+b^2,N) as unit, proper factor, or full gcd.
  For unit pairs evaluate the sampler for each x and count (u,v) outputs.
- Required invariant: for each fixed case all root-conditioned output
  Counters are identical; support is exactly all u^2+v^2=5R pairs;
  every supported output has multiplicity phi(N), computed by exhaustive
  gcd counts for evaluation only. All proper-gcd returns must verify.
- Controls: passing (x,2x) unchanged must fail root-choice independence on
  the distinct-root cases; the affine-only stereographic sampler b in Z/N
  with a=1 is separately checked and must not be silently treated as the
  exact full-group sampler. Record its actual comparison, not a preset
  success/failure count.
- Budgets: <=60 seconds total computation; <=1 second per (N,R) case;
  <=20000 (a,b) pairs per case; soft Python traced allocation cap 32 MiB;
  at most 1 MiB evidence per case and 16 MiB overall. Check time/memory
  periodically and before each case. Unstarted, timed out, and exhausted
  cases are UNKNOWN, never passes. No seeds or numerical search.
- Keep source, frozen protocol and machine-readable per-case counts,
  comparison outcomes, processed/expected pairs, time, peak traced memory
  and stop reasons under the reviewer's exclusive prefix. Avoid recording
  all redundant pair outputs when exact Counters and their hashes suffice.
- Rejection: any completed case violates a required invariant, produces an
  invalid factor, or a control is incorrectly labeled. A passed finite
  screen only checks these cases and does not prove the general sampler.
- Standard-library scratch code only; no package or shared solver change.
  Run scripts/check.sh if adding code, as required by AGENTS.md; that
  baseline check is separate from the 60-second primitive screen.
