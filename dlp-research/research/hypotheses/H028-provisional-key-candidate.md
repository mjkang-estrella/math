# H028 provisional Miller-coefficient collision keys

2026-10-08. Native Astra independent initial delivery, with root normalization
clarification. Candidate only: separate Factory Opus cost/mathematics review is
RUNNING. No experiment, formal theorem, novelty or complete-work gain.

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

rho=O(1) on the intended family is UNPROVED and UNMEASURED. Under it and
I,J=O(sqrtq), false refinements have O(1) expectation, but complete finite costs
still must fit within saved squarings. No arithmetic constant alone is a result.

Astra recommends existing four fixed H024 synthetic fixtures, recertification,
one full-group h enumeration, exact fibres, and independent Miller checks at
fixed indices. Paid enumeration is a diagnostic, not production advice.
A tentative1M-event/60-second cap awaits static accounting. Cap exhaustion
inconclusive, no retuning. Native Sol now designs the exact diagnostic contract;
Factory Opus separately audits the mathematics and complete costs. No run yet.

Prior art actually reopened by proposer: Galbraith–Wang–Zhang shared-inverse
paired generation, https://pdfs.semanticscholar.org/5753/7e7d4d08b6de01aa79717c4bb849e694958f.pdf .
Provisional matching/refinement overlaps H023 EDS matcher; proposed distinction
is this slope-linear key. Targeted prior-art review still needed; no novelty claim.
Other initial relation attempts repeated existing residual-divisor/SP3/oracle
gaps and were not padded into cards. Supported complete work remains square-root.
