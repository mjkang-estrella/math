# H026 native search cards and current disposition

2026-10-08. Native Sol /root/h010_early_dependencies completed three independent
initial constructions, without experiments or edits. Root reviews their literal
cost/scopes below. No supported complete-work survivor emerged. Known paired
additions/block methods remain prior art; no novelty is claimed.

## 1. Explicit failure-conditioned candidate avoidance — literal form rejected

Precompute32 labelled jumps J_u=2^uG+3^uQ with paid shared doubling/tripling
chains. Maintain inspected labels P_i=a_iG+b_iQ and excluded scalar set E.
From current label(a,b), consider all32 possible next labels(a+2^u,b+3^u).
For every stored label and both signs compute the nonzero-denominator scalar
candidate (epsilon*a_i-a-2^u)/(b+3^u-epsilon*b_i), plus infinity. Select the
proposal with the most distinct candidates outside E, breaking ties by u.
Generate and inspect that point, recover/verify useful collisions, otherwise
add its tested candidate scalars to E. A declared cap leads to paid full fallback.

Intended gain: reduce overlap among recovery equations. Literal cost: every
proposal visits every stored label at every step. Even before inverses and
deduplication, cumulative bookkeeping isTheta(t²), henceTheta(q) at t=Theta
(sqrt(q)). Constant-density recorded exclusions additionally needTheta(q)
individual records or a paid q-bit bitmap. Point generation, unused proposals,
lookup and fallback are extra. Root checked this explicit loop-count argument;
it is not a lower bound against every compressed novelty-count data structure.
No such cheaper operation was supplied.

With fixed public jump labels and deterministic tie rules, the all-failure path
is determined by q/independent randomness: E and the next label can be unrolled
without observing target coordinates. Stopping on success depends on the secret,
but failure conditioning alone does not make the selector coordinate-adaptive.
Paid preprocessing or amortization cannot be silently removed. Reject the
literal selector; no EC experiment needed to discover its quadratic loop cost.

## 2. Shared-depth signed tree — exact negative screen accepted

See H026-fixed-depth-tree-screen.md. Reusing one jump per entire tree depth
permits cheap paired generation but at mostO(3^d) useful equation patterns for
Theta(2^d) records. At d=floor(log2(q)/2), fixed-label uniform success tends to
zero, including polylogarithmic inspected setup support. Root and independent
Astra verified the exact finite bound. This is not the previous lag-three
recurrence or a blanket lower bound for adaptive addition circuits.

## 3. Table-directed two-choice walk — speculative, no run admitted

Use the same paid32-jump table. Hash the current canonical full point P with
a fixed domain separator to select J_u. Compute both x(P+J_u) and x(P-J_u),
inspect both against the entire stored-key table, recover/verify useful matches.
Among fresh abscissae choose the candidate of minimum cyclic numerical distance
to the table; break ties by abscissa then sign, and compute its ordinate. If
neither is fresh, use a paid reseed. Store full affine labels, bound restarts
and keys, then fall back completely with all costs paid.

Hoped gain: numerical coordinate attraction might persist through subsequent
translations and increase useful-hit probability. No positive persistence result
is supplied. Under independent next-candidate behaviour, this choice has no
benefit per emitted key. Coordinate proximity, concentrated endpoints and
marginal uniformity do not establish the desired effect.

Proposer ordinary paired step:3M+2S+I for two inspected abscissae and one
retained ordinate. A limiting batch average of3M+S per emitted key requires an
explicit multi-stream schedule; a single dependent walk does NOT receive free
inversion amortization. Ordered predecessor/successor queries, full labels,
seeds, jumps, dead ends, exceptional operations, verification and fallback add
cost. Evolving-table decisions do not have ordinary memoryless coalescence or
free replay. Equal-key memory is not equal-byte memory.

At hypothetical S/M=.8, even granting that optimistic batched kernel and no
other overhead, a10% arithmetic saving needs mean emitted keys below roughly
.737sqrt(q) against the H019 high-memory reference, or.703sqrt(q) against the
empirical.9sqrt(q) grumpy reference. These are conditional necessary targets,
not attained constants or hardware predictions. The proposal has no evidence
meeting either; its finite batching/table semantics also need review.

An operational detail must also be frozen: attraction must be scored against a
table snapshot that excludes the newly inserted candidate pair. If both candidates
are inserted first and then compared with that table, both have distancezero.
The current card does not yet specify every such ordering/batching detail.

Retain as a high-risk card, not an algorithm improvement. Before any experiment,
need a specific positive reason and a cheap frozen test for useful-hit persistence
that can distinguish real gain from table concentration and dependent samples.
No parameter tuning or broad simulator is authorized by this card.

## Source access and roles

Sol read the primary GWZ paper, sections2.1,4.1–4.3,5 and Appendix B:
https://pdfs.semanticscholar.org/5753/7e7d4d08b6de01aa79717c4bb849e694958f.pdf
Its BL2012 follow-up retrieval failed403; it did not claim to inspect those
sections. Root uses previously accepted baseline derivations for cost comparisons.
No experiment, import or source edit was performed by the proposer. The tree
has a separate mathematical reviewer; the two-choice premise remains unverified.
