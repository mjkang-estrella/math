# Bounded factoring research loop

Read README.md, docs/SPECIFICATION.md, and research/STATE.md first. The objective
is a credible new factoring mechanism or useful falsification. Current verified
improvement is NONE. Do not count infrastructure, theorem count, or tiny-case
successes as algorithmic progress.

User steering on 2026-10-07 local / 2026-10-08 UTC explicitly authorizes ongoing
iteration and T3 subagents to discover disruptive factoring ideas and decrease
time complexity as much as possible. The research goal is active. Perform rolling
bounded waves, preserve evidence, and continue from each disposition; do not treat
completion of setup or one diagnostic as completion of the research objective.
No recurring scheduler or model API integration is needed. Purchases, publication,
unrelated projects, and a new recurring scheduler are not authorized by this loop.

Use broad independent ideation before synthesis. Initial wave W001 has six
distinct mechanism lenses plus a primary-literature baseline task. Each proposer
explores several genuinely different mechanisms. Avoid anchoring everyone on
H002 or one fashionable approach. Rank potential asymptotic gain, credibility of
the missing step, and decisiveness of the next test. A new general subexponential
exponent, better L-constant, deterministic worst-case improvement, special-family
algorithm, and implementation constant are separate achievements. Baselines and
models must match before claiming any of them. Verified improvement remains NONE.

T3 task completion wakes this parent thread. Preserve all task IDs and use each
notification to synthesize, review, test, or launch a revised wave. If only live
children remain, checkpoint and yield to their notifications instead of polling
or creating duplicate researchers. See RESEARCH_TEAM.md for ownership rules.

1. **Choose.** Read the last disposition. Select one precise question; consider
   several mechanisms before committing to one. Check primary prior art. State
   the predicted gain, unsupported assumption, and cheapest decisive falsifier.
   Keep factoring, generic quantum simulation, and practical cryptography separate.
2. **Preregister.** Write research/hypotheses/HNNN.md using the template. Choose
   representative inputs, baselines, seeds, budgets, success measure, and rejection
   threshold before running. Preserve old versions in run snapshots. Do not put
   answers, totients, hidden periods, or size-dependent advice in candidate code.
3. **Implement minimally.** Add a callable (n, rng, meter) in algorithms.py and its
   registry. Price every substantial primitive; identify anything the meter cannot
   price. No factor library or oracle fallback under the candidate's name. A better
   algorithm should not require building a whole formal machine stack first.
4. **Run a bounded screen.** Run scripts/check.sh and then:

   ```bash
   .venv/bin/python -m factoring_lab iterate --hypothesis HNNN --config configs/smoke.json
   .venv/bin/python -m factoring_lab verify-run research/runs/<returned-directory>
   ```

   A default wave allows 60 seconds for setup plus attempts, 1 second per worker,
   and 20,000 recorded arithmetic events per attempt. Failed and unstarted trials
   stay in the denominator. Do not silently increase budgets or hide losing seeds.
5. **Challenge.** Check all witnessed factors, input-family leakage, special cases,
   growing operand widths, hidden preprocessing, and conditional success claims.
   Use independent seeds after freezing the candidate. Seek independent critical
   review before promoting a significant claim; T3 delegation is authorized.
   Rejection of one candidate does not disprove the existential goal.
6. **Formalize the useful step.** For a survivor, prove a focused invariant or
   reduction in Factoring/. Add it to Audit.lean and rerun checks. All-input
   correctness and complete bit complexity are separate proof obligations. Do not
   weaken the contract, assume the desired attack, or hide an unbounded primitive.
7. **Record and stop/repeat as authorized.** Write a finding with exact run path,
   frozen source hashes, failed trials, evidence for/against, and disposition.
   Update STATE with the next decisive action. Preserve significant JSONL evidence
   under research/findings; research/runs is ignored scratch, not durable versioned
   evidence. Resume from STATE when T3 results arrive or the user steers the work.

Every wave report must state:

- Best supported complexity or full-work claim and its assumptions.
- Verified improvement against an appropriate baseline (NONE until established).
- Hypothesis tested, evidence for and against, and all material limitations.
- Disposition: rejected, revised, promising, or inconclusive.
- The next experiment/proof that could change that conclusion.

Pause infrastructure work unless a named candidate requires it. Formalize a
machine execution model only when a concrete all-input candidate reaches the
complexity-proof stage. Do not confuse goal definitions with proved existence.
