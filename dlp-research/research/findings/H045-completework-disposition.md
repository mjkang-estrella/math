# H045 translate schedules: finite counts are not stopping laws

2026-10-09 UTC. Raw Grok report/task ID retained in H045-completework-grok-raw.md.
Root and native Astra reviewed the probability claims; native Sol reviewed
arithmetic and complete costs. No complete-work improvement or unconditional
losing-schedule theorem follows. Working exponent1/2; verified improvement NONE.
No experiment, hardware measurement or new Lean claim.

## Translate sets: what is actually counted

Let S={s_j} contain n distinct scalar offsets. Block i emits C_i+s_j G,
where C_i=a_i G+b_i Q. Put Delta=|S−S| and Sigma=|S+S|. The elementary bounds

    Delta<=n(n−1)+1,  Sigma<=n(n+1)/2

and the raw positive/negative scalar-recovery equations are correct.
Recovery requires the corresponding coefficient b_i−b_m or b_i+b_m to be
nonzero, followed by exact verification. These counts do not supply a
probabilistic distribution for centres or labels.

If C_i,C_m are independent uniform points, their difference and sum are
jointly uniform in the odd-order group. The exact geometric cross-hit
probability is

    (Delta+Sigma)/q − Delta*Sigma/q².

Bijectivity of the sum/difference map alone does not establish uniformity.
For example C_m=−C_i makes a sign event certain, despite a uniform difference
when C_i is uniform. Such a geometric identity can have zero useful coefficient.

A different scoped statement remains valid without independent centres:
fix all affine labels and offsets independently of a uniformly random secret k.
Each nonzero-coefficient sign equation covers at most Delta or Sigma possible
secrets. Thus for B full blocks the useful cross-hit union bound is

    Pr[useful cross hit by B] <= binomial(B,2)*(Delta+Sigma)/q.

Exclude zero-coefficient identities; no scalar recovery follows from them.
Labels selected adaptively from the target require a new conditional argument.

Writing T=nB, the quadratic coefficient is

    c_n=(Delta+Sigma)/(2n²)
       <=3/4−1/(4n)+1/(2n²).

The raw ceiling 3/4 holds for n>=2, not n=1. More importantly, a union bound
on cumulative probability is not a conditional hazard or exponential survival
law. It gives only survival at least max(1−c_n*T²/q,0) in this cross-only
idealized continuous relaxation. Integrating yields (2/3)*sqrt(q/c_n), with
block discretization qualifications, not sqrt(pi*q)/(2sqrt(c_n)). At c_n=3/4,
the respective coefficients are approximately0.770 and1.023. The latter
requires an additional Poisson/Rayleigh premise. The weaker bound does not
establish a loss against the referenced0.943 BSGS key coefficient.

Internal negation events were also omitted. For j<h they cover the restricted
sumset {s_j+s_h}; direct infinity tests add {2s_j}. Together the tested centre
values correspond exactly to S+S. A uniform centre therefore has geometric
internal-or-infinity probability Sigma/q. Their B-block union contribution is
at most B*Sigma/q. The same useful-secret upper bound holds for fixed affine
labels under the uniform-secret contract, after excluding null coefficients.
Hence the total elementary upper bound in those stated models is

    Pr[useful recorded hit by B]
      <= min(1, (binomial(B,2)*(Delta+Sigma)+B*Sigma)/q).

For n comparable with sqrt(q), the internal contribution need not be small.
It cannot be dropped uniformly while optimizing block size. These finite
counts do not prove a new algorithm, but they invalidate the raw claimed
unconditional rejection and its proposed cardinality-only falsifier.

## Setup, storage and null labels are separate costs

Computing offsets by separate scalar multiplications and sorting all n²
sums/differences are particular strategies, not necessary costs of emitting
and hashing leaves. If a named construction needs a Sidon certificate, price
that certificate; otherwise do not invent a mandatory sort. A cheaper explicit
offset or centre generator must likewise include its actual setup/storage.
One fixed orbit of centres requires its own coverage/label analysis; it does
not inherit the independent-centre distribution or the raw universal rejection.

Null probability1/q can hold with suitably independent uniform coefficient
labels, conditional on the geometry and chosen sign. It is not guaranteed for
arbitrary labels: all b_i=1 make positive cross-hit coefficients zero.
Records may store a centre descriptor and offset index instead of full scalar
labels, with paid descriptor access and reconstruction. Compare actual bits,
peak memory, traffic, failure budget and verification. Mean stopping inventory
is neither a fixed memory cap nor a matched record schema.

## Side probes: arithmetic comparison only

For ordinary nonexceptional affine inputs and a finite inversion batch of K
nonzero denominators, H043 gives full-sum plus opposite-abscissa cost
6M+2S+(I−3M)/K. It omits additions, labels, representative selection, detection,
storage, failed trials and recovery. H019's x-only interleaved BSGS comparator
has a separately specified limiting kernel2.5M+S; its finite batch, prefix,
setup/overshoot and exception conditions remain in H019-xonly-baseline-screen.md.
Neither is an unconditional full-runtime price.

In the all-pairs model of two independent eligible samples per round, the
leading number of rounds is sqrt(pi*q)/4. Put s=S/M. The difference from the
H019 leading field invoice is

    [sqrt(pi)/4*(6+2s) − (2sqrt(2)/3)*(2.5+s)]*M*sqrt(q).

This difference is positive for the stated s in [0,1]; at s=1 the comparison
is about3.54 versus3.30. It is not positive for arbitrary symbolic s.
The separate main-key/two-probe model has mean sqrt(pi*q/8), producing the
larger conditional field invoice recorded in H044. Neither law is established
for the correlated walk in the raw proposal. An IID estimate is not inherently
optimistic: dependence can improve or worsen useful collision behavior.

The assertion that O(1) field additions per output cannot close the gap is
unsupported: their weighted counts contribute to the leading constant.
Lookup, memory and labels can also change full-work comparisons. Conversely,
no evidence supplied here shows that these omitted effects produce a gain.
Square-root-sized storage on both sides does not itself match peak byte caps.

For a stored label and a side equality W_side=epsilon*P_stored, epsilon=±1,
the coefficient is b_side−epsilon*b_stored. The raw phrase 'coefficients
differ' misses the negative-sign null condition. A repeated jump identifies
the predecessor only under the actual propagated representative invariant;
negation canonicalization can change that equality. Useful/null classification
must follow the implemented labels, not an informal sign convention.

## Progression blocks: a rigorous horizon bound

For D!=O, 2<=ell<q/2, and P_(i,j)=C_i+jD, distinct within-block negation pairs
have sums j+h=1,...,2ell−3. A uniform centre has exact geometric probability
(2ell−3)/q; usefulness requires 2b_i!=0. Positive internal equalities are
impossible under these offset assumptions. Direct infinity tests add their
own cases (together the signed/infinity sumset is 0,...,2ell−2).

For a deterministic horizon H and marginally uniform centres, regardless of
cross-block dependence,

    Pr[an internal negation hit by H] <= H*(2ell−3)/q.

At H=A*sqrt(q/ell), this is O(A*sqrt(ell/q)), tending to zero when ell=o(q).
This finite-horizon statement needs no Poisson approximation. To conclude that
internal hits do not change an EXPECTED full-work leading constant, one still
needs a valid stopping law and tail control, or an explicitly capped comparison.
Plugging a heuristic mean into the event formula does not establish that result.
A Wald/predictable-indicator argument may apply with fresh independent centres
and a specified stopping contract; it cannot be presumed for arbitrary walks.

The block invoice remains C_f+(ell−1)C_x. H044's conditional4.83 coefficient
for its illustrative prices is not a proved cost of an unimplemented generator.
A within-only mean q/(2ell−3) requires independent trials and useful labels.
Calling that set-membership implementation BSGS does not establish equivalent
complete costs. For fixed affine-label single progressions, linear many scalar
equations can explain an O(T/q) useful-secret count, but not for arbitrary
adaptive successors without their own proof.

## Remaining comparisons and decision

The sum-feature's Möbius partner still has no supplied scalar decoder; solving
its coordinate fiber does not automatically give known affine labels. H044's
automorphism-lift exclusion is narrower than all possible recovery methods.
Co-Z and Jacobian kernel statements remain scoped to their exact formulas,
representation invariants and delayed normalization. A kernel invoice does not
prove an entire family of complete solvers slower on every resource model.

Retain the finite counts, extraction equations and conditional field screens.
Withdraw unconditional Sidon loss, inferred Rayleigh lower bound, and universal
growing-block rejection. No material improvement is supported either. The next
decisive object remains a specified labelled generator and detector with a
justified useful-event law and competitive full invoice. No new synthetic test
or infrastructure is admitted merely to repair a false negative argument.
The raw demand for a step strictly cheaper than 5M+S is not necessary: a
dearer step might compensate through a better useful-hit law or matched-memory
schedule. Admission compares the whole construction, not one kernel threshold.

Root and native Astra independently checked the formulas; native Sol checked
the cost scope. Underlying primary arithmetic/baseline references are retained
in H019 and H043, not newly audited by Grok. Validation command/results in STATE
concern unchanged Lean artifacts and do not certify the paper probability model.
