# H031: bounded C2 carryover — remains parked

Status: paper contract, no new solver result. Native Sol
`/root/h010_early_dependencies` proposed the following bounded repair; root
checked the table count and null-cycle algebra. No numerical experiment,
source modification, Lean proof or asymptotic improvement. Starting evidence:
[sole H030 diagnostic](H030-c2-diagnostic-result.md), commit a10bf42.

## Concrete mechanism and costs

Keep r=8, tau=2, the same jump law, DP predicate and eight-state exact ring.
Replace runtime formal-vector copying/ranking with a transition array
T[v,epsilon,i]=index(v+epsilon e_i). Only norm-at-most-one pre-refresh vectors
occur:17 formal rows times2 signs times8 jumps require272 index words. Build
these from declared arithmetic; retain all145 formal point/h records, including
duplicates and infinity. Address arithmetic, transition read and point-record
read remain paid. This removes prototype overhead, not scalar-recovery work.
The origin/sign/slope/label invariant and logical successor remain unchanged.

Let S be canonical, i its selected jump and S'=can_h(S+J_i). If the orientation
relative to S+J_i was negative and S' selects i again, then
F(S')=can_h(-S-J_i+J_i)=S. Labels also return unchanged, so this relation is null.
In traced coordinates that relative orientation is delta*epsilon, not delta
alone. Process identity, ring and DP recovery at S' first; only then retire
instead of computing the known null return. Use actual canonicalization signs
at zero-h and exceptional states. Give the y-control the same early check.
Longer cycles still require the existing ring/round policy. No replacement
starts are supplied, so this is not a demonstrated repair of failed cases.

For matched batch size n, the regular candidate arithmetic core is
4.5M+0.5S+6A+(I-3M)/n, versus5M+S+6A+(I-3M)/n for the control. These expressions
exclude mandatory metadata, bootstrap, reports, reconstruction, failed work,
labels, exceptions, verification and memory. Different actual batch sizes and
stopping times cannot be replaced by equal counts. Array construction and its
272 extra words must also be charged. These are implementation techniques,
not a new exponent claim or established novelty.

## Decision and falsifier

Keep literal C2 parked. A useful reopening would require a named, defensible
cost model and complete inequality such as P_C+E[W_C] <=0.9(P_B+E[W_B]), with
startup P, all stopped work W, failures, memory and comparator optimizations
included. The10% is an explicit materiality gate, not a proved attainable gain.
H030 supplies neither the needed collision/detection efficiency premise nor
validated hardware prices. First instantiate the exact layout and both early
retirement ledgers on paper. Merely removing ranking overhead or repeating
the arithmetic ceiling does not admit another pilot, seed change or cap increase.

Root validation:17*2*8=272; negative-orientation return is the displayed group
identity; initial and later useful reports precede retirement. No probability
law or success guarantee is inferred. No focused Lean claim merits new formal
infrastructure at this stage. Existing366 audits are not evidence of improvement.
