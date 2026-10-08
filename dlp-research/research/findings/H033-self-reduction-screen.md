# H033 single-target self-reduction: scope and missing gain

Status: independent native Astra initial proposal completed; root checked the
following algebra. No new algorithm, complexity bound, numerical experiment or
Lean claim. Verified improvement NONE. Role `/root/h007_additive_relations`.

Let Q=kG in a prime-order q group. Construct Q_i=u_i Q+v_i G with known nonzero
u_i. Searching a fixed scalar set A_i for the logarithm of Q_i succeeds for
exactly the original scalars in u_i^{-1}(A_i−v_i). Thus the probability of at
least one success for uniform k is exactly

    |union_i u_i^{-1}(A_i−v_i)| / q.

The sets and coefficients here are fixed independently of the unknown scalar;
adaptive selections require their own conditioning argument. Finding z_i
recovers k=u_i^{-1}(z_i−v_i). Independent random shifts may give independent
uniform derived points conditional on fixed Q, but the algorithm knows their
affine linkage. It must pay construction, searches, repeated setup and storage.
Shared baby tables are ordinary shared collision-search schedules; merely
calling their queries independent targets establishes no complete-work gain.

For translation-only family emissions P_{i,j}=u_i Q+(v_i+c_{i,j})G, a signed
collision P_{i,j}=sigma P_{l,r} gives

    k = (sigma(v_l+c_{l,r})−v_i−c_{i,j})/(u_i−sigma u_l),

provided the denominator is nonzero. Choosing distinct non-opposite u_i removes
some null equations. This is the already screened multiple-family coverage
mechanism in H024–H025. A new test needs a new coverage-per-paid-operation
premise; another choice of coefficients alone is not one. Generation, inverse
computation, lookup and verification remain charged.

More generally, an affine emission from any derived-target solver flattens as

    aG+bQ_i = (a+bv_i)G+(bu_i)Q.

Root checked that this preserves its point and collision recovery equation.
It does not prove equal implementation costs: shared generation/preprocessing,
label updates and detection could matter and must be explicitly specified.
A competent single-target comparator can use the same flattened relations;
solve-all amortization for unrelated targets is not automatically a saving in
this first-useful-relation problem.

Disposition: three executable mechanisms, no supplied new complete-work gain
premise. No experiment admitted. The cheap falsifier for future variants is
the exact covered-set union plus a matched generation/query/recovery ledger,
not an independence assumption. No general coordinate-aware lower bound or
impossibility claim follows. The generic square-root reference is unchanged.

Source/process: proposer consulted existing coverage/storage findings and
reported a prior successful GWZ primary-paper access; its new Kuhn–Struik PDF
fetch returned502. No fresh literature theorem or novelty claim is inferred
from that failed fetch. The displayed identities are direct algebra checked
by root. All work read-only; no imports, numerical runs or children. The next
decision is whether other independent H033 proposals supply a genuinely new
paid operation or coverage argument. Validation recorded in STATE.
