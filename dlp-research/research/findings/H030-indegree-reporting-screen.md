# H030 indegree-filtered reporting: local enrichment is insufficient by itself

2026-10-08. Native Astra initial proposal; root independently derived the finite
counting and cost screen, checked again by Astra. No numerical experiment,
implementation or Lean claim. No novelty established. Verified improvement NONE.

## Candidate operation and attraction

For a fixed r-adding map F(P)=P+J_(s(P)) with distinct prepared jumps, enumerate
the possible predecessors R-J_j of a prospective report point R and test
s(R-J_j)=j. The number passing is exactly d(R), with 0<=d(R)<=r and sum d=q.
After a cheap independent hash gate, admit R as a distinguished point only when
d(R)>=h, e.g.h=3. Full predecessor tests, selector evaluations and jump setup are
paid. Keep endpoint/seed/replay information and verify recovered scalar labels.
Labels assigned by subtracting a known J_j from R give tautologies, not extra
discrete-log relations.

Why investigate: uniform-source arrivals weight R by d(R), whereas two distinct
sources colliding at R weight it by d(R)(d(R)-1). A point of high indegree can
carry more collision mass per stored report. This corrects the assumption that
merge targets must be uniform. It does not establish an actual walk's distribution.

Known DP/replay baseline context: [van Oorschot–Wiener, §§2–4](https://www.scs.carleton.ca/~paulv/papers/JoC97.pdf),
opened by root and previously read by Astra. Its random-walk assumptions are not
a proof of the new reporting rule. Prior H005/H027 indegree identities likewise
do not establish successive collision hazards.

## Exact finite counts and separate detection model

Let A={R:d(R)>=h}, V=(1/q)sum_R d(R)(d(R)-1)>0, and

    b=(1/q)sum_A d(R),  e=(1/(q*V))sum_A d(R)(d(R)-1).

For b>0, b is the eligible fraction of uniform-source arrivals and e is the
eligible fraction when two distinct uniform sources are conditioned to have
the same output. These statements count finite ordered sources exactly.
An independent hash gate with acceptance probability tau gives theta=tau*b
arrival reporting and eta=tau*e merge reporting in these sampling models.

ADDITIONALLY assume that after an unreported merge every fresh step has the
same geometric reporting hazard theta as the baseline. Expected extra delay
is(1-eta)/theta, compared with(1-theta)/theta for ordinary reporting. Saving is

    e/b-1 <= (r-1)/V-1.

The inequality uses d-1<=r-1 inside the d-weighted sum. Thus local enrichment
with bounded e/b removes only bounded many subsequent steps, not a constant
fraction of a growing1/theta tail. The first useful-collision work is unchanged
by this local-delay model. Actual persistent graph effects remain unproved.

## Paid-screen necessary gate, conditional only

If C literal full screens complete, each testing all r predecessors, their work
is r*C*Cpre when Cpre is actual equal per-test cost; a lower cost bound also
gives a valid lower work bound. An upper estimate cannot prove necessary cost.
In a SEPARATE fixed-P synchronous cost model with constant paid step cost,
the maximal positive local-delay credit is bounded by

    P*max(0,(r-1)/V-1)*Cstep.

Hence positive headroom in these combined models requires

    r*Cpre*E C < P*max(0,(r-1)/V-1)*Cstep.

Root tightens the reviewer's 'at most P active' phrasing to fixed P: arbitrary
state-dependent activity cannot be substituted into a difference of expected
delays merely by bounding population. For one serial continuation take P=1.
Only with justified fixed-T testing/independent gate marginals can E C=T*tau
=T*theta/b replace the actual count. Random stopping, fixed-hash revisits,
caching, variable batches or asynchronous schedules require their own ledger.

## Disposition

Concrete hypothesis retained; no supported material gain or admitted experiment.
Next decisive premise would be an explicit NONLOCAL reduction of detection work
large enough to pay for exact indegree tests, with a genuine trajectory law.
The present identities and local model do not establish that premise or exclude
all filtered reporting. No broad graph formalization is justified.

Two other initial directions were examined without new cards: memoized repeated
trajectories need comparison with already-useful collision recovery/null-cycle
retirement; window summaries need actual common labelled points or paid replay
and currently reduce to known DP/winnowing. Neither supplied a cheaper operation.
