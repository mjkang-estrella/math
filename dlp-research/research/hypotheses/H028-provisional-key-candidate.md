# H028 provisional Miller-coefficient collision keys

2026-10-08. Native Astra independent initial delivery, with root normalization
clarification. Candidate: replacement Claude Opus r2 gave conditional GO for a correctness
diagnostic; the uniform moment lemma was independently proved subsequently.
Factory initial delivery was empty (see task register). No experiment, formal theorem, novelty or complete-work gain.

## Mechanism and finite ledger

Use h(P)=a_P/q from H027-compact-trace-construction.md, q!=p. Keep H019 full
centers/offsets and propagate their h alongside ordinary group operations.
For regular C±J use one inverse of xJ-xC and slopes
lambda±=(±yJ-yC)/(xJ-xC), then h(C±J)=hC±hJ-lambda±.
This costs2M+I rather than2M+2S+I for the two x-only keys.
Full center advances remain paid. With k centers and ell side pairs:

    Kx=(ell+1)[I+(5k-3)M]+k(2ell+1)S
    Kh=(ell+1)[I+(5k-3)M]+kS.

Claimed regular-block saving2kell S. Limiting generation arithmetic2.5M/key
rather than2.5M+S; no exponent change. At S/M=.8 generation-only ratio2.5/3.3,
not a measured total saving. Added field additions, sign canonicalization,
bucket accesses, descriptors/archives, setup and refinements must all be paid.

Bootstrap h(G'),h(Q') by O(logq) normalized Miller chains. Propagate all support
values from already charged slopes; no independent Miller per emitted key.
Use H019 contiguous signed interleaved prefixes and full deterministic caps,
same overshoot/exception accounting and randomization as comparator.

## Recovery and memory contract

Key=min(rep(h),rep(-h)); keep orientation plus index/generation descriptor.
RETAIN EVERY bucket record. On each cross-list raw match reconstruct exact
x for both records from archived full center and offset. A regular reconstruction
costs at most I+M+S plus additions/accesses; two uncached records at most2I+2M+2S.
Center outputs already have coordinates. Dispatch denominator exceptions.
Unequal x rejects cheaply; equal x yields ordinary signed-index recovery and
final scalar verification. Nonzero h orientations determine relative point
sign. At h0, reconstruct y or verify both scalar candidates; zero h is NOT O.

Archive old centers after active advancement: O(N/ell) full points for N keys,
plus per-key descriptors and O(k+ell) active/support data. Compare at equal
actual memory allowance; archives are not free future point outputs.
Worst-case bucket scanning remains quadratic; no failed/capped run is success.

Subsequent Sol protocol refinement (separate Astra review COMPLETED): regular lazy
reconstruction can avoid inversions and multiplications. Archive immutable
(xC,hC), retain offset (xJ,hJ) and the actual signed hSide (recovered from key
and orientation). Then lambda=hC±hJ-hSide and xSide=lambda²-xC-xJ. This costs
one S plus additions/accesses per newly reconstructed record. The earlier
I+M+S bound remains a valid but unnecessarily expensive recovery choice. Active
centers still need full coordinates; old archive lifetime, exceptional outputs,
zero buckets and caching must be explicit. This improves the proposed recovery
ledger, not measured complete work. Factory's initial review began before this
refinement and cannot yet be represented as approving it.

Astra independently confirmed the sign/zero/tangent/identity cases. If canonical
key kappa=epsilon*hSide, actual hSide=epsilon*kappa; descriptor sign sigma is
separate from epsilon. Historical hC belongs to the actual labeled center.
Center outputs return archived x without a square. Infinity is dispatched on
generation; finite tangency uses the same reconstruction after paid exceptional
generation. Identity operands use the other point directly. At h0 recover x
normally, then verify both scalar signs if needed. Archives are immutable
snapshots BEFORE center advancement and survive until all dependent records
expire. Historical (x,h) occupies two field elements, like former (x,y);
active centers/offsets still retain full coordinates and h. Optional x caches
have separately charged space. No extra raw-h field is required per record.

Bounded prior-art check by Astra: reopened Galbraith–Wang–Zhang §4 and retained
Liao–Zhang §3.1 (https://tches.iacr.org/index.php/TCHES/article/download/13106/12653).
The latter's normalized EDS provisional keys are a close antecedent, with a
different key and recurrence. No exact matching construction was confirmed;
this is NOT a novelty determination. eprint2019/385 returned403 and no claims
were adopted from its snippet. First nonconstant normalized coefficient must
not be confused with the leading Laurent coefficient.

## All-input randomization and exact false scans

Pay uniform s in Fq*, uniform independent r in Fq, G'=sG,Q'=Q+rG.
Recover original k=s*k'-r modq. Two scalar multiplications, target addition and
exact rejection sampling charged. Handle Q'=O by direct verified recovery.

Production contract DISPATCHES ACTUAL INFINITY BEFORE RAW BUCKET SCANNING.
For nonidentity P define c(a)=#{P!=O:hP=a}. Oddness gives c(a)=c(-a).
Let d be nonidentity canonical signed bucket sizes, M2=sum c²,
S2=sum d²=2M2-c(0)², rho=S2/[2(q-1)]>=1.
For fixed I nonzero baby indices and J giant indices under fixed full caps,
expected false record comparisons (skipping actual giant infinity) are

    IJ*(S2-2(q-1))/(q(q-1)) = 2IJ/q*(rho-1).

For each baby point, shifted giant is uniform; averaging the nonzero baby via
s gives the fibre sum. Only linearity is needed, not independent pairs.
Actual stopped scans bounded by full-cap scans; not an exact stopping-time law.

Root separately derived the all-point alternative in H028-provisional-key-preflight.md.
Writing c0=c(0), b0=c0+1, B2=S2+2c0+1, its numerator is
S2+c0-2(q-1). Extra c0 counts exactly the comparisons with giant O.
Astra explicitly confirmed this reconciliation and the predispatch contract.
Factory review was launched before this exact clarification; do not imply it
has approved the final normalized contract yet.

## Main unsupported premise and next falsifier

SUPERSEDED premise: rho<=3 now has an independently checked exact paper proof
in H028-uniform-fibre-bound.md, from a residual quadratic for every point
difference. No random-map hypothesis or finite measurement is required. Thus
I,J=O(sqrtq) gives O(1) expected false refinements under paid randomization.
Complete finite costs must still fit within saved squarings; no full-work win.

Astra recommends existing four fixed H024 synthetic fixtures, recertification,
one full-group h enumeration, exact fibres, and independent Miller checks at
fixed indices. Paid enumeration is a diagnostic, not production advice.
A tentative1M-event/60-second cap awaits static accounting. Cap exhaustion
inconclusive, no retuning. Native Sol now designs the exact diagnostic contract;
replacement Claude Opus separately audits the mathematics and complete costs. No run yet.

Prior art actually reopened by proposer: Galbraith–Wang–Zhang shared-inverse
paired generation, https://pdfs.semanticscholar.org/5753/7e7d4d08b6de01aa79717c4bb849e694958f.pdf .
Provisional matching/refinement overlaps H023 EDS matcher; proposed distinction
is this slope-linear key. Targeted prior-art review still needed; no novelty claim.
Other initial relation attempts repeated existing residual-divisor/SP3/oracle
gaps and were not padded into cards. Supported complete work remains square-root.


Root froze experiments/H028/protocol.md before implementation/execution,
incorporating independent polynomial-Miller checks and discriminant consistency.
No run occurred. Review changes and the single10M-event reservation are explicit.
Native Sol reviews the archive-free scalar-verification variant; it is not a
hidden change to this first diagnostic.
