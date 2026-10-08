# H016 labelled restart bursts: explicit operation, no favorable cost ledger

2026-10-08. Native Sol independent proposer, root cost/distribution qualifications.
No implementation, experiment, hardware measurement or new formal claim.

Choose independent uniform a0,b0,u,v in Fq and pay to construct
A=a0*G+b0*Q and S=u*G+v*Q. Resample S if it is O. Generate h<q starts

    P_j=A+j*S=(a0+j*u)*G+(b0+j*v)*Q, 0<=j<h.

Use explicitly handled mixed Jacobian additions then paid batch normalization.
Feed starts to the unchanged negation/endomorphism-aware walk while preserving
logical restart/report order. Retain burst scalars and j for exact label replay.
This could replace h individual start constructions by two constructions,
h-1 projective additions and normalization. It changes only seed production.

A,S are independent uniform points with S conditioned nonzero. Thus raw starts
are individually uniform and pairs uniform-distinct, but the whole burst is NOT
iid. Point/label operations, exceptional cases, unused tail at termination,
descriptor retention, scratch storage and reduced batching capacity all count.
Negation canonicalization may identify distinct raw starts. No iid rho constant
or H015 iid-start theorem transfers without a fresh analysis.

## Complete-work gate

The competent reference may already reuse labelled public points/walks or paid
fixed-base tables. It must not be artificially priced as fresh binary scalar
multiplication per restart. Let baseline total T0 have N starts, mean start cost
Cs and candidate mean Cb. A necessary material-gain condition is

    N*(Cs-Cb) - extra setup/storage/failed-walk/recovery work >= 0.1*T0.

Even eliminating seed construction entirely cannot save10% if its baseline
fraction is below10%. No supplied bottleneck/cost ledger meets this gate. The
proposer therefore parks the operation without a numerical engine; novelty is
unresolved. A defined measured or analytically justified seed bottleneck is the
next prerequisite, followed by full distribution/cost comparison.

## Existing arithmetic capabilities cannot be claimed as new

Sol read actual [BLS §5, printed pp.12–14](https://cryptojedi.org/papers/negation-20110102.pdf).
Deferred subtraction reductions, fused multiply/subtract reduction, a shared
y-derived canonical coordinate for indexing/reporting, and compact preselected
jump points are already baseline techniques. The proposer declined to pad H016
with renamed versions. These source kernel optimizations do not themselves
calibrate the present burst's complete work or any modern GPU throughput.

## Exact initial-negation collision warning

Root derived the following count; Sol independently confirmed it in a separate
paper followup. Conceptually write A=aG,S=sG, s!=0; no algorithm computes these
scalar ratios. For distinct indices P_i=-P_j iff t=-2a/s equals i+j modulo q.
Conditional on any s, t is uniform. For h>=2, integer sums i+j with0<=i<j<h
are exactly1,...,2h-3. When2h-3<q,

    P(any distinct-pair initial negation collision)=(2h-3)/q,
    E(number of such pairs)=binom(h,2)/q.

Pairs of the same sum collide together and yield the IDENTICAL label equation
(2a0+(i+j)u)*G+(2b0+(i+j)v)*Q=O. Their multiplicity is not independent rank.
For h on sqrt(q) scale, expected pair count can stay constant while chance of
any collision vanishes. This is an exact warning against importing iid birthday
success from pairwise facts. It concerns only initial negation collisions, not
subsequent walks, every recovery event or small fixed bursts. The actual baseline
may also use dependent seeds and must be accounted for on its own terms. No run.
