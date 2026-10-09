# Algorithm-first ECDLP research loop

**USER STOP, 2026-10-09 UTC:** finish only work already running at the stop
instruction, collect it, and hand over. Do not start new research rounds,
hypotheses, experiments, children, retries or review rounds. After handover,
the existing goal is paused until the user explicitly resumes it. This
instruction supersedes every continuation/slot-filling rule below. See
[research/HANDOVER.md](research/HANDOVER.md) and [STATE](research/STATE.md).

The main objective is discovering and testing more efficient elliptic-curve
discrete-log algorithms. The research metric is a changed credible complexity
or matched end-to-end work estimate, not theorem counts, commits, encodings,
decoder lemmas or infrastructure. Verified improvement over the accepted
baseline is currently **NONE**.

User steering on2026-10-07 local/2026-10-08 UTC supersedes the earlier milestone
ordering. The loop drifted into disproportionate generic word-machine/query
refinement. Preserve that work, but stop expanding it unless a named promising
algorithm demonstrably needs a specific lemma. Do not make a complete formal
machine stack a prerequisite for evaluating or rejecting an algorithm idea.

## Each bounded wave

Persistent user steering: maintain broad independent ideation before synthesis.
Use as much useful parallelism as actual provider/runtime capacity permits;
the user explicitly confirms T3 Code supports20 concurrent subagents, while
native delegation has four active slots. Use confirmed T3 capacity and respect
actual provider errors/limits; do not create top-level conversations. Keep free slots on distinct productive ideation in
rolling waves while preserving live investigations. Each proposer explores about
3–5 different mechanisms if worthwhile; aim for an initial pool around15–25
distinct candidates across waves, never as a quota or progress metric. Diversify
authorized models after live discovery; report failures without silent swaps.
Do not restrict the pool to two ideas plus a critic. Initial proposers receive
different lenses without other agents' proposals, reducing anchoring. Every idea
needs a mechanism, expected gain, prior-art distinction, unsupported assumption
and cheap decisive falsifier. Speculative ideas need not have complete proofs.
Then deduplicate, retain rejection reasons, rank meaningful gain/testability,
and independently review promising survivors before matched experiments. Generic
lower bounds do not prove coordinate-aware impossibility. Breadth does not waive
full-cost accounting or justify generic Lean infrastructure.

Retain acceptance discipline: independently review and freeze challenge
definitions before accepting significant claims. Changes to curve family,
encoding, interpreter or costs are separate reviewed changes, never a way to
make a candidate pass. Asymptotic claims require a uniform executable algorithm
and a proved bound; finite improvements and practical attacks are distinct.
Account for program size/advice and all assumptions. Do not purchase or rent
additional infrastructure under this loop's authorization.

1. Inspect STATE and live task handles. Keep the existing research goal; do not
   create another coordinator, duplicate active hypotheses or add a scheduler.
2. Rank concrete algorithmic hypotheses. For each state the mechanism, barrier,
   accepted baseline, predicted exponent or material complete-work saving,
   preprocessing/memory/success assumptions, primary prior art and cheap falsifier.
   Label known techniques as known. Reject secret-range narrowing, hidden inverse
   tables/oracles/advice, and irrelevant special-curve transfer immediately.
3. Use parallel distinct idea exploration and independent critical review. Give
   each experiment one precise question that could change the full-size hardness
   or complete-work assessment. Do not replace missing primitives by free oracles.
4. Test correctness and scaling on increasing representative synthetic parameter
   sizes and multiple declared seeds. Match full-work accounting: curve/field
   arithmetic, relation generation/verification, preprocessing, lookup/sorting,
   memory, restarts, failed trials and success probability. Distinguish memory
   tradeoffs and amortization across targets. No real wallets or live funds.
5. Initially bound a computation to60 seconds and roughly1M instrumented events;
   justify larger runs in advance. Stop losing candidates promptly and preserve
   negative evidence. Finite measurements cannot prove asymptotic complexity.
6. Use Lean for focused mathematical claims or invariants of a promising approach.
   Broader refinement must name the candidate and explain why the exact missing
   lemma can change acceptance. Never weaken a challenge or add assumed attack
   axioms to get a result. No proof escape hatches or compiler proof shortcuts.
7. Commit coherent evidence and process locally, with commands, sources, seeds,
   failures, costs, objections and task IDs. Run appropriate checks; when Lean
   changes, update Audit and run scripts/check.sh. The screens are honest-mistake
   checks, not adversarial proof validation. No push/publication without a request.
8. Report the five items below, choose the next decisive experiment, and continue
   or yield to confirmed-live children. Honor pause/stop/budget instructions.

## Mandatory wave report

- Current best supported complexity/full-work estimate and its assumptions.
- Verified improvement versus the accepted baseline (currently NONE).
- Concrete hypothesis under test.
- Evidence for and against it, including failed and inconclusive tests.
- Next experiment or analysis capable of changing the conclusion.

For ordinary prime-field prime-order curves, generic square-root algorithms and
known automorphism constants remain the working classical reference; this is not
a proof excluding coordinate-specific attacks. Use primary sources to scope
claims and do not treat a historical literature survey as a current novelty proof.
No GPU curve-work throughput is validated here: B200/H200 AI FLOPS do not measure
ECDLP work. Any dashboard multipliers are explicitly hypothetical, not benchmarks.

The ongoing goal remains open. No discovery is promised, and compilation is not
completion. See RESEARCH_TEAM.md for delegation/ownership and research/STATE.md
for the authoritative checkpoint and active hypotheses.
