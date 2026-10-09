# A Lean 4 specification for discrete-log research

**Research stopped by user:** existing work has been collected; explicit user
resumption is required. Start with [research/HANDOVER.md](research/HANDOVER.md)
for conclusions, evidence boundaries and the final shutdown checkpoint.

This project defines what a verified faster discrete-log algorithm would have
to establish. The Lean code does **not** discover an algorithm automatically
or demonstrate a cryptographic break. The user has authorized a separate agent
research task governed by `RESEARCH_LOOP.md` and `RESEARCH_TEAM.md`.

Lean 4.34.1 is pinned. Only Lean's bundled `Std` library is used. The downloaded
local toolchain lives under ignored `.tools/`; no global installation or shell
profile changes were made.

```bash
./scripts/check.sh
./scripts/lake.sh build
./scripts/lake.sh exe research_demo
```

On another machine, install [elan](https://lean-lang.org/install/); the wrapper
then uses `lake` and this project's pinned toolchain. The bundled local download
is Linux x86-64 only. Python 3 is needed for the audit scripts.

## What is the argument?

For an elliptic curve with generator G of order q, given Q = [d]G, recover the
unique d in [0,q). A meaningful claim needs a correct executable algorithm,
specified inputs, a cost model, and a useful bound under that model.

Two goals are intentionally separate:

1. **Concrete feasibility:** a fixed, reviewed instance admits a program of
   bounded description size that solves every scalar within a specified number
   of machine steps. This limits tables hidden in the finite program, but does
   not constrain the public encoding or parameter advice. Those must be reviewed
   separately. Limits must be chosen from an actual resource budget.
2. **An exponent improvement:** one fixed program solves every instance in a
   fixed family whose orders grow with n, with cost eventually bounded by
   O(q^(1/2 - epsilon)) for some epsilon > 0. This is stronger than a
   constant-factor improvement and stronger than merely o(sqrt(q)).

The essential concrete statement in `Research/Goals.lean` is:

```lean
def ConcreteGoal (P : CyclicProblem) (maxProgramBits maxSteps : Nat) : Prop :=
  ∃ code : Machine.Program,
    Machine.descriptionBits code ≤ maxProgramBits ∧
    SolvesWithin P code maxSteps
```

`SolvesWithin` quantifies over **every** scalar. The interpreter receives only
public parameters and an encoded public key. Successful execution must halt
within the fuel budget and return the scalar in fixed-width binary.

The exponent target uses integers only:

```
exists one program A, a budget function T, k >= 1, C >= 1, and N,
  A solves every scalar at every size within T(n) steps, and
  for every n >= N:
      T(n)^(2*k) <= C * q(n)^(k-1).
```

Taking positive roots corresponds to an exponent of 1/2 - 1/(2k). For k=2,
this asks for an O(q^(1/4)) algorithm. The code defines a proposition, with no
theorem asserting that it has a proof. Its truth is an open research question
for any suitably chosen cryptographic curve family.

The fixed `secp256k1` curve alone has no varying input-size parameter: it is a
finite problem. A complexity-class claim about it alone is meaningless without
a specified family. Also, a generic group algorithm cannot beat established
generic lower bounds; a proposed breakthrough must exploit a concrete
representation or change other assumptions. A faster EC kernel can be useful
without being an exponent improvement.

## What has actually been checked?

- A binary-tape interpreter with fuel counting executed transitions, and a
  theorem that one extra unit of fuel preserves successful runs.
- A complete toy cyclic problem of order two, with a verified trivial solver.
  It is a framework check, not an elliptic-curve result.
- A coordinate implementation of y²=x³+2x+1 over F5 with seven points:
  closure, abelian group laws, generator order seven, complete orbit, and an
  injective fixed-width coordinate encoding connected to `CyclicProblem`.
- A high-level exhaustive orbit-search baseline, proved to return every scalar
  d with exactly d+1 equality tests (at most q), instantiated on that curve.
  Equality-test counts exclude point/field arithmetic and memory costs and
  are not binary-tape step bounds. Independent review is recorded in W001.
- Fixed-width input encodings preserve observable tape distinctions: different
  scalars on the small curve differ at a head observation within its 25-bit
  input. This assumes known width and proves no parser or runtime bound (W003).
- A conventional executable baby-step/giant-step solver recovers every orbit
  scalar for every positive table width, including duplicate baby points when
  the width exceeds the order. Its add/neg refinement is proved for the small
  coordinate curve. Lookup is linear; no total-cost bound is asserted (W005/W007).
- A separate sorted solver uses reviewed coordinate keys and actual indexed
  binary lookup. Generic proofs cover every positive table width and bound
  accumulated query comparisons. Baby construction, sorting, key generation,
  group arithmetic and memory remain unpriced; this is not a total-work bound
  or a tape implementation (W008/W009).
- A reproducible signed-BSGS experiment tests all 365 scalars of five synthetic
  coordinate curves. Negation pairs reduce some counted additions while adding
  sign/key work. This known constant-factor method has no calibrated speed or
  exponent claim; the full event vectors and review disagreements are in W006.
- Independently reviewed checked-word instruction steps and actual prefix
  serialization, with fault/event correspondence and exact program bit lengths
  (W011/W013). These are internal components of a separate abstract cost model;
  a raw-input runner now charges setup and execution from one budget, with
  trace-derived counts, initialization proofs and terminal monotonicity (W014).
  Complete solver costs and tape refinement remain open. The encoding is
  deliberately unary and proves no compactness or budget feasibility.
- The standard secp256k1 generator coordinates satisfy y^2 = x^3 + 7 (mod p),
  and the standard scalar-order constant is less than 2^256.
- Arithmetic showing that the earlier illustrative workload 2^128 exceeds a
  week of one million workers at 19.3 billion operations/second, even after a
  10-quadrillion-fold speedup.
- A source screen and printed axiom audit for the named theorems.

Negative specification tests also demonstrate why an accepted research
challenge needs more than the abstract interface. Secret-revealing encodings
can satisfy its goals trivially, even while preserving an existing curve orbit.
Distinct finite-list encodings can also initialize identical tapes, making the
corresponding problem unsolvable. These are interface counterexamples, not
ECDLP algorithms; see `research/findings/W002-encoding-audit.md`. The small
coordinate example has a fixed-width ordinary encoding and is separate from
these deliberately inadmissible examples.

The GPU arithmetic checks are **conditional calculations**. They do not prove
the work estimate, the reported benchmark, linear scaling, or a reduction from
curve operations to tape steps. The tape model and the GPU model have different
units and must never be silently equated.

## What remains open?

- A general or cryptographic-size elliptic-curve refinement. The new seven-point
  example is finite specification validation only. The existing interface models
  a cyclic orbit; it does not itself enforce elliptic-curve group laws.
- A frozen family of appropriately difficult curves and reviewed, conventional
  public encodings. Do not choose an easy family and claim a secp256k1 result.
- A justified refinement of the high-level exhaustive baseline to the tape
  model, and a verified complete cost bound for the sorted baseline (or a
  separately reviewed alternative cost model). Query bounds alone do not pay
  for construction, sorting, arithmetic, memory or physical access.
- A randomized/probabilistic extension. The current all-input deterministic
  worst-case goal is stronger than the usual expected-cost Pollard-rho claim.
- Resource accounting beyond transitions: peak tape usage, realistic hardware,
  preprocessing, and any cost of producing family parameters. The program
  must perform runtime preprocessing inside its budget; fixed public inputs
  must not smuggle precomputed inverses or secret-dependent advice.
- A genuinely improved candidate, correctness proof, cost proof, and independent
  review of both the theorem and the implementation.

Because these items are open, successful compilation is **not** a certificate
of cryptocurrency security or insecurity. For a meaningful future claim, the
problem definitions and interpreter must be frozen independently of candidate
generation. Our scripts catch common mistakes, not a malicious proof author.

## Running an open-ended research process

Use `RESEARCH_LOOP.md` as the agent brief and `research/STATE.md` as its checkpoint.
Each invocation performs one bounded research iteration and records what
changed. A scheduler or agent orchestrator can repeatedly invoke that brief;
Lean checks finite artifacts rather than executing an infinite proof.

The research task may use the approved native/T3 subagent providers and commit
significant findings and process notes locally. No time-based schedule, custom
agent API integration, or live-wallet attack job is installed.

## Primary references

- [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
- [SEC 2, secp256k1 parameters](https://www.secg.org/sec2-v2.pdf)
- [Shoup's generic discrete-log lower bounds](https://www.shoup.net/papers/dlbounds1.pdf)
- [Pollard-rho work estimates](https://safecurves.cr.yp.to/rho.html)
- [Reported GPU kernel benchmark](https://github.com/RetiredC/RCKangaroo)
