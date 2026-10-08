# H034 concentration without a paid useful-collision gain

Status: native Astra independent initial pass completed, no surviving new
transition or numerical diagnostic. Root checked the elementary statements below.
No new algorithm, general lower bound, Lean claim or prior-art discovery.
Role `/root/h007_additive_relations`; other initial H034 proposals withheld.

## Rejection sampling of independent uniform proposals

Take independently generated uniform group points, with correct affine labels,
and accept each P with fixed public probability a(P) in [0,1]. Put
alpha=E[a(P)]>0. The accepted point distribution is pi(P)=a(P)/(q alpha), so

    sum_P pi(P)^2 = E[a(P)^2]/(q alpha^2).

Under a birthday approximation based on this second moment, charging all
proposals cancels the alpha factor: the proposed-work coefficient is proportional
to1/sqrt(E[a²]), which is never smaller than for accepting everything. This
approximation is not an exact stopping theorem for arbitrary distributions or
EC walks, and does not price memory, labels or detection.

An exact statement survives without birthday assumptions: fix the entire
proposal sequence and acceptance decisions. Every useful labelled equality
between accepted proposals already occurs among all proposals. The unfiltered
detector may use more storage/lookups, so this containment does NOT establish
matched-memory full-cost dominance. Rejection needs a specific paid detector/
storage saving; second-moment concentration alone is not a gain premise.

## Literal known-anchor reset cancels its own target coefficient

For P=aG+bQ and a known anchor A=cG, forming the jump A−P and then adding it
maps every input to A. Its affine labels combine as

    (a,b)+(c−a,−b)=(c,0).

Forced equality at A is therefore tautological, not useful scalar recovery.
All formation/transition costs are paid. This does not exclude other attraction
rules with a genuinely informative nonzero recovery coefficient.

For independently uniform affine start pairs (a,b), conditional on point
tG=(a+bk)G, b is uniform in Fq. A pair selected using only these independent
points has null signed-recovery coefficient with probability1/q. This observation
requires independent starts, point-only selection and the full initialization
distribution; it is not a claim about same-start cycles or arbitrary walks.

## Disposition

No new paid generation/detection mechanism emerged. Existing filtering/DP and
minfold/minhash screens remain prior context; these elementary deductions are
not discoveries. A next candidate needs a concrete transition and useful-label
law, or a matched-memory detector saving, before testing concentration. Generic
square-root reference unchanged; verified improvement NONE. All work paper-only,
no source novelty claim or numerical runs. Root integrates; no Lean/Audit change.
