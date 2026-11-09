# H029 — Coordinator disposition

2026-10-08. **ACCEPT the scoped mathematical core after specification repairs.**
Verified full factoring complexity improvement: **NONE**.

The coordinator consumed all 622 review lines, checked the four localized
repairs and their proof completions, and verified all 40 frozen-input hashes
and all eight review-delivery entries. The review hash is
c42bd1a2f1dcd495992e6621f5cb87932db9047247862dd4734e7b413c476d52.
The original 300-line [submission](H029-submitted-draft.md) remains unchanged,
hash dbf3036111778eb9837aba21195265765b9af576d4925eca49b45aba744d7a0e.
The corrected construction report has hash
056e83ae5c7ce5f32a5fe720b54518f6036068d880a9a6ddc0e23cf41d8ec74d.
Original parent/construction intakes and source manifests remain historical.

## Accepted scope and repairs

P1–P8 pass: a universal same-base power-difference cover obeys
theta(R)<=|B|[L²/(2log2)+3L/2], hence |B|L²=Omega(R). This is a necessary
prime-support condition, not a runtime lower bound or an obstruction to
input-dependent or cross-base covers.

Card A's real progression leaf routine and restricted explicit high-order menu
obstruction pass. Restrict 3<=m<=R, a nonempty menu, and paid finite parameter
selection so the stated n-bit costs apply. The retained screen also requires
m<R/2. The report now specifies recursive triangle order and row-major
rectangles, including the same-row interval case. Monic products/remainders
work over arbitrary composite moduli; no inverse interpolation is presumed.
The explicit prime-count constant and R>=41 are recorded. An upper leaf-cost
certificate is not a lower bound on each actual leaf execution.

Card B's known small-factor preprocessing, Lehman coverage, dyadic padding,
O(n^4) descriptor construction, Theta(M^(1/3)) rows, strict positive leaves
below M, and cheap visited-prime recovery pass. Root descent now explicitly
starts at gcd(input,full product). The invariant is divisor-of-input and
divisor-of-assigned-product; prime support alone does not supply valuations.
Strip all multiplicities from original N_0. The general traversal keeps index
costs, with its simplified envelope restricted to log(k+1)=O(n). The complete
Lehman hypotheses are displayed alongside the application.

The parent checked that root initialization, valuation partition and the
small-leaf inequality compose: after preprocessing M=pq is squarefree; a
nontrivial visited leaf divisor d|M and d|A<M is p or q. Internal gcd=M merely
shortens the interval. The expensive general Leaf fallback is not reached
under these invariants.

The current fully specified product enumerates Theta(M^(1/3)) rows, giving
N_0^(1/3)*poly(log N_0) complete time and the stated preprocessing workspace.
This is slower than the deterministic N^(1/5) benchmark. It is a mathematical
algorithm specification, not an implemented or timed improvement.

## Exact remaining algorithmic question

RootProduct returns the product of the ordered positive leaves for every
M>=4096, every 2<=d<=M and every valid interval, with empty result 1 mod d
if offered. Every preparation, query, index, modulus change, record and
operand width is charged. A uniform bound C_P+P<=M^(tau+o(1))*poly(log M)
would imply complete exponent max(1/6,tau). No such fast primitive exists
in this submission or review.

The paired identity A_minus*A_plus=4kM+e is valid, but replacing the product
by e is only valid modulo divisors of 4kM. A zero pair without a retained,
paid decomposition loses the present leaf proof. This does not prohibit
every alternate pairing algorithm; it requires its own exact interface.

Select one bounded proof-only attempt at an exact polynomial-block realization
of RootProduct. It must avoid paying for the full root list, certify floor
boundaries, work for composite nondivisor moduli and partial intervals, and
charge all polynomial degrees and coefficients. Target a fixed tau<1/5,
ideally 1/6. Failure closes that realization only. No finite experiment,
parameter sweep, solver code or Lean change is selected yet.

Harvey already posed a square-root speedup of Lehman's search; no novelty
claim is made for that aspiration or these classical identities. H030 will
carry the selected constructive attempt. H029 tasks are complete with no
pending child runs. The overall research goal remains active.
