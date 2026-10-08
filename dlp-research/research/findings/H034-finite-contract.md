# H034 sparse paired sums: finite contract and reviewed stopped costs

Status: paper contract, NOT an implementation or complete-work improvement.
Native Sol proposed; native Astra independently reviewed the finite-cap,
hash-conditioning and graph arguments; root integrated. No numerical run,
new Lean theorem or novelty claim. Earlier mathematical screen supplies the
four-support collision law. Full-cost comparison remains open.

## Frozen candidate

For an ordinary short-Weierstrass curve over odd Fp with odd prime subgroup
order q and full-range Q=kG, set Emax=ceil(3sqrt(q)/2). Choose the least prime
ell>=2 satisfying 4ell^6>=9q. The affine-plane incidence graph has 2ell²
vertices, ell³ edges, degree ell, and no C4. Vertices are points(x,y) and
lines(s,t), with incidence y=sx+t over Fell. Index points by xell+y and lines
by ell²+sell+t. Edge ordinal e=sell²+tell+x identifies its endpoints.
Enumerate only the first Emax edges in lexicographic(s,t,x) order. Within a
row use y<-y+s modulo ell; charge indexing and all small-field/integer work.
Trial-division prime search has a coarse O(ell^(3/2) polylog(ell)) bit bound
using a prime within a constant factor of the threshold. No prebuilt edge list.

Eagerly sample every vertex label(a_i,b_i) independently uniformly in Fq²,
compute full P_i=a_iG+b_iQ, and retain coordinates/labels. No resampling of
exceptional roots. The mathematical probability law assumes actual uniform
independent sampling; fixed PRNG seeds in a future diagnostic would be a
reproducibility convention, not an instantiation of that theorem. Charge random
bits, rejection sampling, scalar multiplications and all setup.

A separate seed-only exact-x index checks seeds during startup and is freed
before the leaf stage. Seed/helper keys are never compared with leaf keys.
For each edge emit x(P_i+P_j), then x(P_i-P_j), in batches of at most ell
edges. The regular arithmetic subtotal for b edges is

    (5b-3)M + 2bS + 6bA + I.

Whole-batch arithmetic is paid even on an early hit. Stop lookup at the first
exact repeated x. Derive formal labels from the two edge descriptors, try both
orientations in fixed order, and verify every nonzero-denominator candidate
against Q. One zero denominator alone does not justify abandoning the other
orientation. A null/unrecoverable equality triggers the paid fallback below;
it does not silently reuse the first-collision stopping theorem for a later hit.
Infinity is handled before x hashing. Seed-zero and equal-x edge cases get
explicit ordinary group/tangent/vertical dispatch and candidate verification;
they are not guaranteed solutions when their target coefficient is zero.

Candidate archive uses U=2Emax nodes with exact x, edge ordinal, plus/minus bit,
and next pointer. Head count H is the least power of two >=ceil(sqrt(q)). Hash
is ((eta*x+zeta mod p) mod H), independently sampled eta!=0,zeta in Fp.
Prepend after an unsuccessful exact lookup. Pay hash arithmetic, head clearing,
allocation, record reads/writes and every chain comparison. Reserve 10ell field
scratch entries and 2ell integer/exception entries. Include root array,
labels, identity flags, capacities and allocator representation in peak bytes.

On edge-cap or exceptional unrecoverable failure, free the candidate archive,
sample fresh uniform R in Fq, solve Q+RG using the complete H019 fallback,
subtract R and verify. The new independent shift makes fallback input uniform
even conditional on the candidate failure posterior. Pay shifting, fallback
setup/search, clearing, unshifting and verification. Whole lifecycle peak is
the maximum of the stages, not just the leaf table.

## Accepted conditional moment deductions

The earlier reviewed collision law gives survival exp(-x²)+o(1) at x sqrt(q)
keys. A bounded cap permits dominated convergence for both moments. Candidate
inspected prefix T has

    E[T]/sqrt(q) -> integral_0^3 exp(-x²) dx,
    E[T²]/q -> 1-exp(-9).

If candidate/fallback per-key prices are cC,cB, the leading arithmetic is

    sqrt(q) * [cC integral_0^3 exp(-x²) dx
               + cB (2sqrt(2)/3) exp(-9)].

Do not replace this fixed-cap expression by sqrt(pi)/2. Batch overshoot
O(ell), seed construction O(ell² log(q)), and suitably paid exceptional
fallback events are lower order under the stated model. That does not make
their finite costs small. Complete costs also include the leading lookup work.

The first exact-x equality depends on the points and inspection order, not
hash placement. Conditional on the entire stream and T, the independent affine
hash remains random. For distinct keys its collision probability is at most
1/H+1/(p-1). Thus

    E[unequal-key comparisons]
      <= (1/H+1/(p-1)) E[T(T-1)/2].

Before the first repeated key all stored keys are distinct, and its terminating
query adds at most one exact-key comparison. No IID leaf assumption is used.
For H comparable to sqrt(q), the false comparisons are O(sqrt(q)), a LEADING
cost. If paid batch overshoot keys are also queried, count those keys too.
Hash-dependent resource aborts break this conditioning for the censored T;
report such censoring separately in any future capped diagnostic.

## Remaining gate

H019's smaller worst-case record capacity lets it spend spare matched peak on
hash heads or other tuning. Root suggested, and Sol is independently checking,
that its leading second moment is also q, so similar same-H collision traffic
does not automatically scale down with H034's smaller mean key count. Compare
complete finite vectors and strongest applicable grumpy evidence before a run.
No numerical experiment is admitted. An eventual small synthetic loss could
test correctness/cost implementation, but would not refute a lower-order seed
term's asymptotic disappearance. No practical gain or exponent change follows.

Process: /root/h010_early_dependencies proposal; /root/h007_additive_relations
independent finite-contract/hash review; root integration. Reviews were read-only
without experiments, code imports, edits or children. No Audit change.

## Subsequent deterministic startup clarification

Root and independent Astra recovery review fixed the earlier ambiguity:
after the explicit Q=O input dispatch, construct ALL roots before processing
seed events. Then scan roots in vertex order, infinity first, and on the FIRST
seed-x repeat either verify recovery or immediately fall back. Null seed events
never permit continuing to the leaf phase. No resampling occurs.

Reaching the leaf phase therefore certifies finite roots with pairwise distinct
x. A simple graph's edges all have nonzero denominators and both signed sums
are finite. This is an exact invariant, not a probabilistic assertion. Defensive
ordinary edge checks must reject an invariant violation; tangent/vertical/zero
support can be exercised separately as public component diagnostics.

With equal x keys labelled(A,B),(A',B'), orientations sigma=+1,-1 yield
d=B-sigma*B' and proposal(sigma*A'-A)/d when d!=0. Verify both nonzero-denominator
proposals in order; a failed wrong-sign verification is expected. Example at
Q=2G: labels(-1,1),(-3,1) represent G,-G. The first denominator is zero, yet
the second recovers2. Premature fallback after only the first orientation would
lose a useful relation. Null zero label(0,0), or identical labels at nonzero
points, can require fallback; infinity/equal x is not automatically a solution.

The fixed-k Poisson law describes the undispatched mathematical leaf process.
An actual solver with Q=O dispatch has T=0 on that fixed input. For a uniform
full-range target this shortcut alters the mixture only on probability1/q;
it does not justify removing0 from the challenge or claiming equal fixed-input
stopping laws after shortcut dispatch. The pending finite protocol includes0.

Reference: proposed research/experiments/H034/protocol.md. Independent
protocol review precedes source construction/execution admission. No run yet.
