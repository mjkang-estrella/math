# W002 Lens C — corrected scope and coordinator disposition

2026-10-08. **ACCEPT the finite algebra, extraction and corrected cost/probability
statements below; REJECT the two specified realizations as additive speedups.**
Verified COMPLETE classical factoring complexity improvement: **NONE**.

This addendum is authoritative for the accepted result. The original 518-line
submission remains unchanged, including its historical UNACCEPTED label.
Read it with these replacements, not as an unqualified acceptance of every
original sentence. The coordinator consumed all 612 independent-review lines.
All 46 review snapshots, 20 original snapshots, 30 original delivery entries,
10 source-artifact identities, the added primary PDF and 58 review delivery
entries verified. Review SHA-256:
d71c5255acc6f393ada99a3e94ea3ea564719d29c7e8a6f537ffe0b21be064bd.
Original report and submitted draft SHA-256:
c73d5c34bd6ba6dc1a283d94edf75fd36fcbacf53f3a539cabc3722c1f80f8df.
Intake SHA-256:
90dd593cde0be7778dec9baed3343b8ea18eeca52a3a4a501cce95b7197aa78f.

## Adopted review corrections

**R1: evaluator and driver domains.** The evaluator takes odd N>1, positive
K and s>=0 supplied residues. It is a polynomial computation over Z[1/2]
reduced modulo N, valid with duplicate parameters, zero intermediate values,
singular curves and nonsquarefree N. Only its field/group interpretation
needs a nonsingular reduction. Even N and K=0 are outside this evaluator.
The composite-input driver first returns a proper 2 or 3, then has gcd(N,6)=1.
Its total success law is therefore

    sigma_driver(N)=1                            if gcd(N,6)>1,
    sigma_driver(N)=1-(1-tau_(N,B))^r             if gcd(N,6)=1.

The rn-bit sampling tape belongs to the second branch; an optional total tape
can be unused on the first. No later setup is charged to an early return.
The exact useful-word set retains all rejection and full-gcd failures.

**R2: sequential access and original labels.** Compute the cached powers
u^0,...,u^s once, and scan that cache for each tensor output (or perform a
sorted join). This additional access fits
C(s,h,n)=O(h 16^s [M(n)+s(n+s)]). Tensor addresses refer to positions in
the retained list; preserve the original raw-slot map separately. If labelled
records are rescanned in recovery, add

    Lscan=O(s log(s+1)(n+log(r+1))).

This is absorbed by C+O(r(n+log(r+1))), not uniformly by C alone for arbitrary
r. With L=log_2(r+1), the label term fits C when L<=s; when L>s,
s log(s+1)=O(r), so it fits O(rL). The empty list has no tensor scan.
Thus the final whole-trial envelope survives, with every recomputed subquery
and its initialization charged. No free cache or label lookup is assumed.

**R3: explicit scalar fallback schedule.** Adopt the review's level-order
schedule, which preserves equation (9) as a proper-factor-or-FAIL interface.
For each parameter, stream K and keep two fixed scalar windows; append its
final z_i. Pad with units to the next power of two, build the product-tree
levels by sequential adjacent-pair scans, and retain the level records.
There are fewer than 4s total nodes. Scan all stored nodes, paying every gcd
and O(log(s+1))-bit key operation, then verify a selected proper divisor or
return FAIL. If left-first selection is desired, keep the proper node of
minimum prefix-first preorder key. This specifies the padded tree's answer;
it need not preserve the original unpadded stopping schedule.

A tree has a proper-gcd node exactly when it has a proper-gcd leaf; unit
padding does not change that event. The schedule costs
O(s(M(n)+G(n)+n+log(s+1))) beyond scalar evaluation. Hence the accepted
fallback bound remains

    S(B)+O(r h M(n)+r G(n)+r(n+log(r+1))), h=Theta(B).

Space for evaluation and tree is O(s(n+log(s+1))+h+W(n)); add the driver's
actual O(r(n+log(r+1))) raw-word/label storage. Do not replace an original
log r label by log s without keeping its map. This is an on-paper schedule,
not a newly executed implementation or a new factoring result.

**R4: conditional comparison quantifiers.** Under the separately stipulated
useful-word law, require fixed c,C>0 with c<=r*tau<=C. Equality of only the
leading logarithmic scale does not guarantee constant success. The choice
ceil(c/tau) illustrates that model; it is not an executable estimate of tau.
Take p=min(p,q)->infinity for distinct semiprimes, with r->infinity and
r=exp(O(sqrt(log p log log p)))=p^o(1). Define retained-slot indicators on
the full tape, even for executions that stop early. Their binomial count S*
has retention probability at least (1/2)(1-3/p)(1-3/q). A union bound on
early discriminant factors and a Chernoff bound give

    Pr(no early exit and s>=r/4)
      >=1-3r(1/p+1/q)-exp(-c0*r)=1-o(1).

This does not assert independence of a stopped list. The scalar and desired
additive expressions minimize respectively b+1/(2b) and max(b,1/(2b)),
giving sqrt(2) and 1/sqrt(2) only in that conditional model. Keep polynomial
input-width factors outside L_p unless their logarithms are o(sqrt(log p
log log p)). The fixed B=n^2,r=n driver inherits neither the parameter rule
nor a positive useful-success bound. No unknown factor size is provided free.

**R5: historical attribution.** The constructor's verifying STATE snapshot
c18ea42829aef215700161c2795fe6151285933c23b0a5c928f545ca1931eca8
already records H031 completion near its top, while retaining stale live
statements lower down. Its synthesis snapshot
fb148d61e5f77f591a799bb3c670872a85165889a82f1aeb99b5eb2a72abace0
records completion. An earlier synthesis read with different wording is not
separately preserved. This replaces the overbroad attribution in the original
report/provenance; the original files and manifests remain untouched. The
current shared checkpoint's stale H031 statements are corrected separately.

## Accepted result and remaining research obligation

The four base values, eight-coordinate quartic transition, full labelled
tensor invariant and final product are accepted with R1. No recurrence formula
needs replacement. Full-gcd descent succeeds exactly when some leaf has a
proper gcd, for every composite modulus, including repeated prime powers.
Its fresh queries obey sum_v 16^(s_v)<=2*16^s, with R2's traffic paid.

The distinct-semiprime CRT identity is accepted for p,q>3. Vanishing of a
division polynomial at the fixed affine point means its order divides K,
including when a characteristic divides K; separability is not required.
The coordinator checked the archived multiplication-map statements in
Sutherland's 2021 Lecture 5 alongside the review. The raw-word success formula
is exact, but contains no positive uniform lower bound on tau. Expected
restarts cost E[T_trial]/sigma only when sigma>0.

The expanded implementation stores 8^s tensor entries and expands 16^s
terms. Its mandatory transition writes are Omega((h-3)8^s n) for h>3.
The all-zero raw tape actually reaches s=r=n on every composite coprime to
6, so the fixed driver has the stated expensive branch. Keeping its known
tensor factors restores ordinary per-curve work. Neither realization is an
additive improvement. Formal cross-term examples and literal storage bounds
do not rule out other compressed states or all norm algorithms.

The coordinator checked the transition endpoint ranges, distributive invariant,
both recovery directions, label absorption, scalar streaming schedule and
full-tape probability argument before adopting these completions. No experiment
or Lean task is selected. A new attempt needs a different finite transition,
paid extraction, a useful-success theorem and an input-only parameter rule.

[Original submission](W002-ecm-norm-recurrence.md),
[independent review](W002-ecm-review.md), [intake](W002-ecm-intake.md).
