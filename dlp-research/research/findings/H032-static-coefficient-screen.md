# H032 static coefficient constructions

Status: two explicit hypotheses, no supported improvement. Native Astra
`/root/h007_additive_relations` independently proposed them without reading other
H032 initial ideas. Root adversarial review repaired the multiplicative coverage
dispatch and strengthened the literal parabola cost screen; proposer confirmed
both repairs. Native Sol `/root/h010_early_dependencies` then independently
reviewed and ACCEPTED the exact scopes, with the infinity/dispatch caveats below.
No numerical experiment, code/Lean edit or benchmark. All constructions use the full scalar
range in a prime-order subgroup, Q=[k]G; no novelty is claimed.

## 1. Additive-basis parabola

Emit P_t=tQ+t²G. For u!=v in Fq, P_u=P_v implies k=−(u+v).
Let m=ceil(sqrt(q)) and use parameter progressions0,...,m−1 and
0,m,...,(m−1)m. For any desired s in[0,q−1], write s=jm+i with0≤i,j<m.
Its chosen jm<q, so the two parameters are distinct except s=0. Dispatch Q=O
directly. Other wrapped or repeated table entries do not invalidate this chosen
cross-pair argument, but duplicates must be handled in an implementation.

For progression step d, maintain

    P_t=tQ+t²G, D_t=dQ+(2td+d²)G, F=2d²G;
    P_{t+d}=P_t+D_t, D_{t+d}=D_t+F.

Updates use old values. Literal generation uses two full additions per regular
emission plus initialization, lookup/labels and verification. Exact signed point
keys can add coverage but do not supply a cheaper generation operation. Auxiliary
D/F registers are not inspected for recovery in the screen below.

Root's exception repair: for odd q and d!=0, scalar polynomials are
P=t(k+t), D=d(k+2t+d), F=2d²!=0. P+D is exceptional only if P or D is zero,
or P=±D. Nonzero polynomial root bounds give2+1+2+2=7 occurrences over distinct
t. For D+F, D=0,±F gives at most3. Two streams therefore have at most20
exceptional addition occurrences. Counts are union bounds and can overcount.
Short Weierstrass base field characteristic is greater than3. Both steps1,m
are nonzero modulo q for q>2. Each inspected prefix uses distinct t within each
stream; initialization and omitted last updates change only O(1) work.

Give every inversion and all batching, setup, storage and recovery away. Each
regular literal affine addition still executes2M+S. With t inspected P keys,
signed pair matches and infinity tests reveal at most t² candidate scalars;
identically true equations reveal none. Extra fixed direct input tests add O(1).
The fixed schedule is independent of the unknown scalar. For uniform full-range
k, run until valid recovery or L=floor(sqrt(q)) keys; the tail-sum bound gives

    E[min(T,L)] ≥ sum_{t=0}^{L−1}(1−(t²+O(1))/q)
                 = (2/3)sqrt(q)−O(1).

The literal generation's mean leading arithmetic is consequently at least
(2/3)(4+2s)sqrt(q) M, s=S/M∈[0,1]. This exceeds the existing high-memory H019
coefficient(2sqrt(2)/3)(2.5+s): 4+2s>sqrt(2)(2.5+s) throughout that interval.
The argument even grants free inversion and ideal useful signed coverage.
If addition-dispatch flags involving D/F are exploited for recovery, they add
O(t) candidate equations, not merely O(1) input tests. The same leading bound
survives because their tail-sum contribution is O(1); the exact t² statement
above applies only to P-key signed/infinity tests.

Disposition: reject this literal recurrence as an arithmetic improvement over
that high-memory comparator. This is not a lower bound for all implementations,
all additive-basis lifts, low-memory solvers or wall-clock costs. It requires
the declared inspected keys and stopping/truncation policy; abandoned earlier
failed prefixes do not inherit it. A new cheap multi-output operation would be
a different candidate. No coverage enumeration or solver experiment is needed
to evaluate the losing stated implementation.

## 2. Multiplicative-basis hyperbola

For nonzero t, emit P_t=tG+t^{-1}Q, with inverse in the scalar field Fq.
Ordinary equality at u!=v yields k=uv. Signed equality at u+v!=0 yields k=−uv.
Other degenerate equalities cannot be treated as scalar recovery.

Given a CERTIFIED primitive element g of Fq*, set m=ceil(sqrt(q−1)) and take
parameters g^i, g^{jm} for0≤i,j<m. For any k!=0, let k=g^e with0≤e<q−1.
The existence proof uses e=jm+i; the solver does not obtain e as advice.
The selected exponents i,jm are below q−1, so equality of the two parameters
forces i=jm=0. This is k=1, which requires an explicit Q=G dispatch in addition
to Q=O. Root requested this correction; proposer confirmed it. Cross products
then prove coverage of every remaining scalar without an assumed decomposition
oracle. Exhaustive point equality/recovery, if used, remains paid work.
Intermediate infinity must not be dropped for lacking an abscissa: P_t=O gives
k=−t² and must be handled directly, including an infinity cross-match.

The missing gain is generation: no uniformly cheap operation for these parameter
sequences was supplied. Literal scalar multiples or successive multiplication
by g and g^{-1} are not unit-cost point additions. Primitive-element certification,
any requisite factorization information, scalar inverses, all initialization,
generation, square-root-size storage, lookup and exact verification remain paid.
Coverage alone proves neither favorable work nor an exponent improvement.

Disposition: no surviving executable cost hypothesis, no experiment admitted.
A specified cheap emission operation and matched complete ledger would be needed
to reopen it; this is not a proof that every hyperbola-based mechanism fails.

## Comparison and review boundaries

H019 x-only signed interleaving and the existing H025 addition-chain screen are
the comparison findings. Known BSGS, grumpy-giant and coefficient-geometry methods
are antecedents, not discoveries. The proposer read the primary Galbraith–Wang–
Zhang paper through a public PDF mirror; a Bernstein–Lange fetch502 is recorded
as an access failure, not a novelty result. No new literature-wide novelty claim.

Best supported complexity remains the classical square-root reference with
existing memory/automorphism qualifications. Verified improvement NONE. Next:
synthesis/review of the separate memory-recovery and autonomous-walk proposals.
Root alone integrates and commits. Validation: ./scripts/check.sh >
/tmp/ecdlp-h032-static-check.log 2>&1 exit0,366 existing audits. Paper-only
claims, no Lean/Audit changes or experiment admission.
