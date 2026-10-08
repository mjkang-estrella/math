# H034 sparse paired sums: unverified constant-factor hypothesis

Status: UNVERIFIED. Native Sol proposed a C4-free variant after its literal
all-pairs construction failed. Independent Astra mathematics and Factory Opus5.5
cost/prior-art review RUNNING. No claimed new algorithm, verified gain, benchmark,
Poisson theorem or experimental admission. Exponent remains1/2 even if the
suggested constant survives. Root alone integrates.

## Mechanism to freeze

Let a simple C4-free graph have n vertices, m edges and bounded maximum degree
Delta. Assign independent uniform affine labels(a_i,b_i) in Fq² and compute
P_i=a_iG+b_iQ. All graph choices, labels and emission order are independent of
observed coordinates. For each edge(i,j), emit/store x(P_i+P_j) and x(P_i−P_j),
with edge and sign descriptors. A signed output match yields a linear equation
in k; recover only with nonzero coefficient, then verify against Q. Infinity,
equal-x seed pairs, zero denominators, repeated outputs and null relations need
explicit paid dispatch. All source points and helper state count in peak memory.

Paired x-only additions share an inverse. The ordinary batch subtotal for E
edges is5E M+2E S+I−3M, emitting2E keys. Its limiting regular price is2.5M+S
per key, the SAME as the H019 arithmetic baseline. There is no new kernel claim.
Seed scalar multiplications cost O(n log(q)) group operations, not free advice.

Possible graph family: finite-projective-plane incidence, n of order h²,
m of order h³, Delta of order h. h is a constructible prime power; construction,
edge indexing/order and finite caps are still being specified by the proposer.
Taking n of order q^(1/3) could make seed preparation lower order than sqrt(q).
No oracle supplies the seeds' discrete logarithms: only their affine labels are
known, and their points are computed by the usual public group operations.

## Why this differs from all pairs

The all-pair construction emits t=r(r−1) signed keys from r seeds, but its
four-distinct-seed equations number only8*C(r,4), leading t²/3 rather than t².
Different edge pairings repeat the same signed equations. The literal all-pair
prefix is independently screened separately; arbitrary DAGs are not excluded.

Two disjoint graph edges offer eight signed four-support equations modulo global
sign. A C4-free graph should prevent alternative perfect matchings of the same
four vertices. The conjectured leading distinct relation count is therefore
t² for t emitted signed keys, with lower-order adjacency/degeneracy terms.
This precise combinatorial claim is under independent review.

## Unproved probabilistic bridge

For fixed unknown k, z_i=a_i+b_i k are independent uniform Fq variables. A
nonzero signed relation on four seeds has probability1/q. Conditional on the
points, b_i remain independent uniform marks; useful recovery must be checked
with that conditioning, not assumed from geometric collisions alone.

Root conjectures a local-dependence Poisson argument for fixed t=x sqrt(q):
O(m²) events, at most O(Delta*m) potentially dependent events per event. Distinct
nonproportional forms should have joint probability1/q². At n~q^(1/3),
Delta~sqrt(n), these estimates suggest a vanishing approximation error. This is
NOT a proved application of a theorem: event multiplicities, field assumptions,
prefix degree bounds, lower-support events, null labels and dependency conditions
must all be verified. Tail control, caps and paid fallback are separately needed
to convert fixed-threshold probabilities into expected stopped work.

If all those bridges held with survival exp(−t²/q), mean leaf keys would approach
sqrt(pi)/2 sqrt(q), about.886 sqrt(q). H019's accepted interleaved key count is
(2sqrt(2)/3)sqrt(q), about.943 sqrt(q). Stronger applicable grumpy-giant constants
near.90, their evidence status and implementation costs MUST also be considered.
The suggested margin against that comparator is small and may not be material.
Neither hypothetical count is a complete bit-work or wall-clock comparison.

## Falsification and roles

First cheap tests are paper checks: distinct equations and their dependency law;
whether graph/seed preparation, descriptors, sorting/lookup, inversion batches,
exceptions and fallback preserve any full-work margin; and whether prior art
already supplies this mechanism or a better baseline. Only after those checks
would a capped synthetic correctness/scaling diagnostic be specified. No real
wallets or narrowed-secret challenge, no measured hardware rates.

- Proposer `/root/h010_early_dependencies`: freeze graph and complete contract.
- Mathematical critic `/root/h007_additive_relations`: combinatorics, probability,
  expected-work bridge and counterexamples, independently.
- Factory Opus5.5 cost/prior-art critic:
  `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h034-sparse-pair-priorart-factory-opus-20261008-r1`.

All roles read-only/no experiments, edits or children. No Lean infrastructure
is commissioned. Verified improvement remains NONE until independent results
support a concrete claim under explicit resource assumptions.
