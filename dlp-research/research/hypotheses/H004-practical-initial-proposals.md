# H004 independent practical cards: one coverage gate, two cost gaps

Native Sol /root/h002_tradeoff_ideas supplied these independently of other H004
initial proposals. No edits, experiments or children by proposer. Root retains
the mechanisms, not their novelty or any unsupported cost gain. Earlier apparent
paired-addition and terminal-y savings were screened as prior art, separately recorded.

P1: four affine progressions jointly chosen for scalar cover area and existing
paired x-output arithmetic. Frozen b=(0,1,2,3), s=(1,M,−M−1,2M+1),
M=floor(sqrt(q/2)), round robin. A fourth intercept/stride might fill gaps in
the signed three-list cover, but can also duplicate coverage. Correct objective
is full stopping-cost area with setup, joins, memory, overshoot, recovery and
fallback, not pair count. Exact recovery and falsifier are frozen in
H004-progression-coverage-protocol.md. [Bernstein–Lange grumpy giants](https://cr.yp.to/elliptic/grumpy-20120709.pdf)
already studies slope/coverage choices; this substantially overlaps that prior art.
No gain was predicted numerically before the test. Root subsequently ran the
approved bounded gate; see H004-coverage-initial-diagnostic.md for actual evidence.

P2: generate rows nG+bQ via normalized rank-two elliptic-net values, advancing a
Somos-4 recurrence `w_(n+2)*w_(n−2)=alpha*w_(n+1)*w_(n−1)+beta*w_n²`.
Share recurrence inverses with adjacent-net coordinate-output denominators;
maintain rolling windows and explicitly handle zero terms with point arithmetic.
Feed outputs to the unchanged signed collision solver. No exponent claim.
It needs an actual combined recurrence/output count below the stronger paired
x-output baseline; none was supplied. Initialization, constants, normalizations,
zero fallbacks and sign recovery are not free. Elliptic-net arithmetic is prior
art ([Stange](https://arxiv.org/abs/0710.1316)); recurrence alone is not a saving.
Disposition: retain as a cost-gap hypothesis, no arithmetic pilot from this card.

P3: route a Jacobian walk using projective-invariant bits
`chi(X−c_j*Z²)=chi(x−c_j)` instead of representation-dependent limb hashes.
Equal points then choose the same jump, preserving coalescence. Normalize declared
endpoints, retain scalar labels and verify collision recovery. Price projective
addition, each character, endpoint normalization, short cycles and restarts against
batched affine rho with identical resources. Direct Euler exponentiation appears
far too costly, but no universal lower bound on every character implementation is
claimed. The missing primitive is a demonstrated cheap invariant routing procedure
whose full loop wins; a saved normalization alone is insufficient. This is distinct
from an endpoint filter claiming more scalar information.

No broad implementation, hardware benchmark or Lean infrastructure is authorized
by P2/P3. A future exact loop with a favorable optimistic count could merit a
tiny synthetic falsifier; neither card currently supplies that count.
