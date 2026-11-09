# W006 execution details fixed before the only screen

The byte-identical parent preregistration is `W006-coefficient-validation-protocol.md`.
These details resolve instrumentation choices without changing its cases, menu,
candidate, controls, or caps. No candidate execution or arithmetic dry run has
occurred before freezing.

- Right-to-left binary powering starts with the unit vector and (1,1,0,...).
  It multiplies the accumulator for each set bit and squares the base only when
  a next exponent bit remains. Thus convolution count is
  popcount(N-1)+bit_length(N-1)-1; each costs exactly L^2 multiply-adds.
- All L coefficient gcds are computed in increasing index order, even after a
  proper gcd appears. Return the first checked proper gcd only after completing
  the vector scan. This gives all requested gcds without additional transforms.
- Candidate is an isolated source module taking only N,L. Evaluator labels and
  factors occur only in the screen module, after candidate execution. This is
  reviewed trusted code, not an adversarial security sandbox.
- Each attempt is a fresh Python subprocess. The supervisor enforces a 1-second
  subprocess timeout including startup, arithmetic, controls and serialization.
  The worker checks its overall deadline during every row recurrence; candidate
  checks during every multiply-add and gcd. An outer 60-second `timeout` applies
  to the supervisor. A 48-record UNKNOWN ledger is saved before work and updated
  after each attempt. Terminal, timeout, failed and unstarted records are kept.
- Every completed exponent bit, the completed vector and every gcd are flushed
  to a bounded per-attempt JSONL stream; a hard-killed worker's partial stream is
  retained. Counters missing after a hard kill are unknown, not zero.
- Reduced operand width includes N; arithmetic width additionally includes the
  unreduced product and multiply-add. No modular reduction is deferred.
- Tracing starts before candidate loading in each worker. Peak is a soft Python
  traced-allocation cap, not an RSS/native-allocation guarantee. Supervisor
  tracing includes its evidence buffers. Time is checked throughout arithmetic.
- Each attempt independently calls math.comb and separately computes all exact
  row coefficients by integer recurrence. Exact controls are never candidate work.
  Retain central width/time, row time/width, folded vector, and every noncentral
  index in the central residue class together with its coefficient modulo N.
  These diagnostic aliases require no second run and are not fed to candidate.
- Output JSONL is capped at 1 MiB per attempt (any truncation is explicitly UNKNOWN)
  and outcome-plus-worker evidence at 16 MiB total. No truncation is expected:
  the largest alias list has at most 1799 entries and only bounded scalar fields.
- The started marker uses exclusive creation; an existing marker prevents rerun.
  Source and protocol hashes are verified before attempts. Static AST parsing
  and project checks execute no W006 candidate and are outside the screen cap.
- If an external whole-screen kill occurs, the saved UNKNOWN ledger and partial
  events are the evidence; no restart is permitted. No adaptive menu or fallback.
