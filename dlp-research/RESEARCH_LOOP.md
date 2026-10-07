# Resumable agent brief

Prepare research artifacts toward a verified improvement in algorithms for the
elliptic-curve discrete logarithm problem. The initial objective is honest
formalization, not claiming or guaranteeing a discovery. Work on mathematical
specifications and synthetic, small instances; this project has no wallet
targets or live-fund recovery tasks.

The user has now authorized a dedicated research task, parallel subagents,
independent verification, and local commits of significant findings together
with their research process. Follow `RESEARCH_TEAM.md` for the approved model
families, delegation mechanics, write ownership, and commit policy. This
authorization supersedes the original preparation-only restriction.

Work in successive bounded research waves, checkpointing between them. Continue
autonomously while useful work remains and the runtime permits. Use a persistent
agent goal where supported; do not implement a busy shell loop or claim that a
single process can run forever. No time-based recurring schedule is configured
by this brief. A paused or interrupted task must resume from its checkpoint.

## One invocation

1. Read `README.md`, `research/STATE.md`, and the current Lean definitions.
   Check the working tree for work in progress before making edits.
2. Select one tractable integration milestone and assign distinct parallel
   investigations when useful. Start with the unresolved
   concrete elliptic-curve refinement, a small checked example, or baseline
   correctness. Do not jump directly to asserting a secp256k1 breakthrough.
3. Write a short hypothesis: what might improve, why, and what observation or
   proof would falsify it. Consult primary literature when assessing novelty.
4. Implement, formalize, or experiment with explicit resource bounds. Use roughly
   15–30 minute research waves as checkpoint intervals, not a limit on the whole
   task. Initial toy experiments should fit within 60 seconds and one million
   transitions; document justified increases before running them. User-authorized
   model calls go through the native/T3 delegation tools. Do not purchase extra
   infrastructure, rent GPUs, or start live-wallet recovery jobs.
5. Run `./scripts/check.sh`. Add every new theorem supporting a claimed result
   to `Audit.lean`. Report assumptions and all unproved obligations.
6. Update `research/STATE.md` and a per-hypothesis research record with exact
   commands, outcomes, rejected hypotheses, resource use, reviewer objections,
   task IDs, and the next distinct step. Preserve useful negative results.
   Commit significant coherent milestones under the policy in `RESEARCH_TEAM.md`.
   Do not repeat a failed approach without a new reason it could succeed.
7. Continue to the next wave or yield to outstanding subagents. Record any
   necessary handoff before ending a run. Do not duplicate work already active.
   If three successive iterations hit the same external blocker, explain it
   and require a changed input rather than spinning indefinitely.

## Acceptance conditions

- Never change the target, curve family, public encoding, interpreter, or cost
  semantics merely to make a candidate pass. Legitimate specification changes
  are separate milestones requiring review before comparing new results.
- No unproved escape hatches, newly assumed attack theorems, or compiler-based
  proof shortcuts. Keep the axiom audit limited to Lean's standard logical
  axioms. An open objective stays a definition of a proposition.
- A complexity result requires a uniform executable algorithm and a proven
  bound on its execution. A bare inverse function or assigned cost is not one.
- Do not turn a secret into public input, use secret-dependent advice, narrow
  the scalar range silently, or substitute toy/easy curves for the target.
- A finite-size improvement, asymptotic improvement, and practical attack are
  different results. Report each with its actual evidence and scope.
- Benchmarks do not prove asymptotic complexity. Correctness does not prove
  speed. A theorem about an abstract group does not certify a concrete curve.
- Account for preprocessing, memory, program size, success probability,
  amortization, and hardware assumptions before making a practical claim.
- Freeze independently reviewed challenge definitions before accepting an
  extraordinary result; the included lexical and axiom screens are not a
  hardened untrusted-agent proof checker.
- When a hypothesis becomes testable, separate its proposer/implementer from
  its verifier. Obtain mathematical, executable, and cost-model checks before
  treating an improvement as established. Disagreement is part of the record.

## Suggested milestone order

1. Review/freeze the statement and cost model; refine curve arithmetic into it.
2. Prove scalar multiplication and exact-order facts on a small actual curve.
3. Formalize a baseline and demonstrate end-to-end correctness on that curve.
4. Add explicit randomized semantics for expected-cost algorithms if needed.
5. Connect an efficient implementation's operations to a reviewed cost model.
6. Investigate one specific algebraic or implementation improvement at a time.
7. Only after synthetic evidence and proofs, assess transfer to cryptographic
   parameter sizes and the size of the remaining performance gap.
