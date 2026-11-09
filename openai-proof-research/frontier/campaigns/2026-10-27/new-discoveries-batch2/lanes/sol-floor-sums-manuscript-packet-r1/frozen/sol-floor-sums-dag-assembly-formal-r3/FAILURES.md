# Preserved failures and limitations

The final endpoint compile succeeds. Earlier failed attempts are not successful
proofs and are preserved in numbered attempt directories and `attempts`.

1. The initial structure used unparenthesized grouped fields under
autoImplicit=false. It failed binder inference. Parenthesized fields corrected
the syntax. Unused environment/query binders were renamed with underscore
prefixes; no warning option was disabled. An unnamed noncomputable section also
needed its own closing `end`. Numbered source/log snapshots retain these failures.
2. Initial generic rule generation used fallback `first` tactics. Strict linting
rejected unused branches and tactics after simp had already closed goals. Final
code selects a proof mechanism; the guarded repair script removes only exact
reported solved-goal tactics or unused simp arguments. Kernel checking, not the
repair script, establishes validity. Failed versions are retained.
3. Integer congruence required exposing both application heads and premise
equalities. Pure propositional reasoning failed at node742 and neighboring
nodes. Final proofs explicitly rewrite arguments; transitivity uses Eq/Iff.trans.
4. Intro-definition clauses required actual ite semantics rather than tauto.
Explicit condition cases prove them. The first lemma discharge at node7492
also required exposing the negation inside its clause. Large discharge clauses
later made tauto exhaust heartbeats (node17296, conclusion17295, in
parts/Dag168_031). Explicit Or injections and classical contradiction replace
remaining large-clause searches.
5. The unsplit 45-node Dag168 composition block hit the unchanged CPU210 guard
(sampled RSS about1.46GB), producing no module. Its exact source/receipt remain.
The SAME block was split into 45 serial one-node modules. All compile, and the
Dag168 wrapper imports the final part. No cap or heartbeat limit was increased.
6. A subsequent repeated old-search invocation was intentionally terminated
after its replacement had been prepared; the process and parent chain were
stopped before starting the replacement. Dag170's old tactic search was likewise
terminated to replace its remaining five resolution searches. The direct
resolution generator initially omitted a surviving whole disjunction literal;
that case is now explicitly injected. Final generated resolution proofs check.
Some failed helper correction runs were not redirected to durable console files;
their diagnostics remain in the session transcript. Exact early helper source
versions beyond the explicitly saved snapshots are not all retained. This is a
provenance limitation; final sources and scientific bindings are hashed.
7. Missing inherited arithmetic object files stopped imports. They were rebuilt
from byte-identical proof sources only when required. An initial arithmetic
rebuild chain was stopped after its current invocation to prioritize composition;
no two Lean processes overlapped. All required arithmetic modules subsequently
built. This replays solved proofs rather than introducing new arithmetic proofs.
8. A helper attempted an unbounded read of a large inherited audit log and hit
MemoryError under the unchanged512MiB AS cap. No cap was raised. The replacement
freezes/hashes/log parsers stream bounded chunks/lines. Direct source copies made
before that interrupted manifest write were rebound and rechecked by the
streaming extra freeze. The immutable scientific originals were not edited.
9. Clip transfer initially exposed a mismatch between computable and classical
Decidable instances inside ite. Explicit condition cases close the equality
without a new axiom. All64 query clip equalities compile.
10. The first source-sum bridge had an obsolete `Finset.not_mem_empty` name and
a global AC simp reached its fixed heartbeat limit. It was replaced by64 small
argument identities and outer additive normalization, with ordinary finite-set
simplification. The initial `congr 1` solved some goals before the subsequent
arithmetic tactic; congrArg now leaves the explicit argument equality uniformly.
The final source-sum identity and unconditional endpoint both compile.

All predecessor failures/early-version limitations remain preserved through
the direct frozen packets and immutable references. Resource sampling can miss
transients; guard receipts report sampled peaks, not a proof of continuous RSS.
No live novelty clearance or complete historical search is claimed. All campaign
acceptance gates beyond this formal endpoint remain the root's responsibility.
