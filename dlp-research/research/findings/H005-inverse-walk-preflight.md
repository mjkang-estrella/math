# H005 inverse walk: independent mathematical preflight

Status: transition/recovery identities checked on paper; no contraction theorem,
experiment or verified improvement. Proposer native Astra h005_information_ideas;
independent reviewer native Astra encoding_review; coordinator checked signs,
qualifies the arbitrary known-set bound below, and owns integration. No Lean
claim or Audit entry added. No numerical trials were performed by the reviewer.

For R_t=a_t Q+b_t G, branch d in{0,1} gives
R_(t+1)=[inv2](R_t-dG), a_(t+1)=inv2*a_t,
b_(t+1)=inv2*(b_t-d), so a_t=2^(-t)!=0.
Equal states at i,j yield k=(b_j-b_i)/(a_i-a_j), when denominator nonzero.
An adjacent return around a cycle of length ell is useless exactly when
ord_q(2) divides ell. If so, every repeat in that component is useless. A
constant-memory detector can compare a larger multiple of a useful ell and
produce a zero denominator: do not declare the component useless from that
alone. The first pilot instead stores every state and sees the first repeat.
Memory is charged; no constant-memory performance claim is made.

Known R=O yields k=-b/a immediately; R=-G yields k=(-1-b)/a whether or not -G
is fixed. Check these before collision/timeout and verify the recovered point.
A public known-point set must be frozen and priced, never a full inverse table.

## Structural checks and their limits

Only 2R and2R+G can map to R. The strict total score gives exactly
indegree(R)=1[s(R)<s(R-H)]+1[s(R)<s(R+H)].
Let n2 count indegree2 points. Sum indegrees=q implies n0=n2; for odd q,
n2<=(q-1)/2. Thus independent uniform starts X,Y obey
Pr(F(X)=F(Y))=(q+2*n2)/q^2 <=(2q-1)/q^2 <2/q.
This is a one-step distribution identity, NOT a successive collision hazard
bound or a coordinate-aware square-root lower bound.

O is absorbing and F(G)=O. Any other cycle has length<=q-2. Consequently if
ord_q(2)=q-1 no useless cycle exists. This does not bound the paid trajectory
length or imply work improvement. The least candidate score need not be lower
than the current state's score: no descent follows from the definition.

The root proposed, and reviewer confirmed, the reflection identity
F(G-R)=-F(R) for R!=H. The candidates have different x-coordinates unless
R=H, where they are +/-G/4 and the y tie-break breaks this identity. This
symmetry is not independence evidence and does not replace coefficient recovery.

For labelled initial point[x]G,
R_t=[(x-D_t)/2^t]G, D_t=sum_{j<t}2^j*d_j in[0,2^t).
If 2^t<q, reaching O by time t requires canonical x=D_t; absorption makes
this an at-most2^t count of initial states. It supplies a logarithmic obstruction.

**Root qualification of reviewer wording:** for an arbitrary known set A of
size s, bounded indegree alone bounds EXACT-time preimages by s*2^t, but BY-time
preimages require union_{j<=t} F^(-j)(A), bounded by s*(2^(t+1)-1), absent an
additional invariance argument. The review's blanket by-time s*2^t bound is
not adopted. For this specific A={O,-G}, the digit identity gives initial integer
representatives in [0,2^t-1] or[-2^t,-1] across all hitting times<=t, hence at
most2^(t+1) residues. This special bound needs no assumption that -G is fixed.
The independent reviewer confirmed the correction and withdrew the unrestricted
claim; neither variant proves sqrt(q) hardness or a practical advantage.

## Approved direction, not approved execution

The reviewer found one bounded full-domain pilot meaningful for this actual score.
Its outcome must be actual verified recovery with all failed-attempt costs.
For independent uniform restarts with success u>0,
E(total attempt work)=E(C_attempt)/u, plus one-time solver setup; after r attempts
failure probability=(1-u)^r. This includes initialization, timeouts, failed
collisions, scoring, detection/replay, coefficients and successful verification.
A successful-only trajectory mean is biased. An offline functional graph or
scalar labels cannot become free solver preprocessing.

Root's draft research/experiments/H005/inverse_walk_protocol.md freezes one
existing ordinary prime-order fixture, all73 offsets of one public target,
actual direct halving and exact scores, cap18 transitions, first-repeat dictionary,
and an executable signed-BSGS reference sharing the same affine arithmetic.
The finite full-attempt screen can reject this frozen implementation; it cannot
establish asymptotics, curve generality, an optimal timeout or hardware costs.
No random-score sweep, enlarged budget or broad formal infrastructure is funded.
Separate native Sol implements only inverse_walk.py, syntax checks only; the
independent reviewer checks the draft before a later independent source review.
No experimental result exists at this checkpoint.

Protocol review additionally required a Gauss half-tie STOP rule (not a
repeated nearest-integer subtraction), explicit sampler rejection/bit-packing
control charges, and an explicit fixed-Q versus uniform-secret distinction.
Root amended the draft accordingly and sent the changes to the implementer.

Final protocol review conditionally approved the core equations/coverage; also
required false verified answers and reference exhaustion to be fatal validation
failures, and peak memory to remain separate from additive work. Root incorporated
these requirements. Full source review and execution are still pending.
