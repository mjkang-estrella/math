# H018 BM probe v1: frozen for one diagnostic

2026-10-08. Independent native review requested by root. No diagnostic, curve
search, arithmetic experiment, or implementation has been run. Root approval
was required before numerical execution and is recorded below. Verified complete ECDLP improvement:
NONE.

## Decision and purpose

Propose ONE finite-instance exact sparsity falsifier, with four frozen features,
one successfully certified synthetic curve, and no automatic follow-up. Amend
the preliminary threshold 128 / 256 samples to threshold 64 / 128 samples.
This gives more budget margin and tests a sparsity bound below sqrt(q) at the
proposed q near 8192. Even sparsity below 64 would not make quadratic BM cheaper
than a competent square-root solver; this is an information diagnostic only.

The useful negative event is finite-prefix linear complexity at least 64. It
proves that the corresponding GLOBAL geometric-orbit sequence has no recurrence
of degree below 64, equivalently no scalar polynomial with fewer than 64
nonzero powers on Fq*. This is distinct from H014's character-correlation
screen and H016's unproved mixed-modulus proposal. There is still no positive
mechanism predicting sparse powers. A positive finite-prefix result proves
neither global sparsity nor useful ECDLP recovery.

## Frozen, paid fixture selection

Use p=8191, with trial-division primality certification performed and charged.
No previously discovered curve parameters or scalar-to-point table are used.
Try the four curves y^2=x^3+x+b, b=1,2,3,4, in that order. Reject singular
curves by checking 4+27b^2 modulo p. No changing the order after observations.

Before point search, evaluate x^3+x+b at x=-1 with charged arithmetic. If zero,
reject the curve: (-1,0) is nontrivial rational2-torsion, incompatible with full
odd prime order. Among these four curves this rejects b=2. Independent Sol
identified this symbolic obstruction; root accepted the filter BEFORE any
fixture search. No additional curve or fallback is added.

For each curve, try x=0,...,15 in order. Compute h=x^3+x+b and y=h^2048 mod p
using eleven squarings, since (p+1)/4=2048. Accept the first y with y^2=h and
y nonzero, and choose min(y,p-y). This defines the nonzero point G. If none
exists in this bounded search, move to the next curve. No square-root table.

The Hasse interval for the full order is [8011,8373]. Enumerate its odd primes
in increasing order using paid trial division; retain at most the first 64
such primes. Certify each retained prime by trial division through its square
root. EXCLUDE q=p=8191 (charge the comparison): the known anomalous family is
not a representative full-range ECDLP probe. This correction was required by
the independent Sol review and accepted by root BEFORE any numerical run.
For a curve with its selected G, test the remaining q in increasing order by
computing [q]G. Impose a GLOBAL maximum of 96 such scalar tests across all
curves. If [q]G=O, accept the first resulting fixture and stop selection.

This really certifies FULL prime order: G is nonzero, q is prime, and q divides
#E(Fp), while 2q>8373. Hasse therefore forces #E(Fp)=q. No point count, claimed
order, or uncharged fixture discovery is needed. If the lists or 96 tests are
exhausted without certification, the result is FIXTURE NOT FOUND / INCONCLUSIVE.
Do not infer a probability of success from this small deterministic family.

Factor q-1 completely by paid trial division. Try w=2,...,33 in order and
accept the first with w^((q-1)/ell) != 1 mod q for every distinct prime factor
ell of q-1. This certifies primitive order q-1. If none succeeds, terminate
inconclusively; do not extend the search. There are at most five distinct prime
factors, since the product of the first six primes exceeds 8372.

All fixture selection depends only on public parameters, never a secret range
or favorable feature output. This probe uses no unknown target Q.

## Four exact features and shared samples

For the accepted curve let X,Y be centered integer representatives of x(P),
y(P), and take centered a=1 and the selected b. All outputs below are in Fq:

1. f_x(P)=X mod q.
2. f_y(P)=Y mod q.
3. f_kappa(P)=((Y^2-X^3-aX-b)/p) mod q.
4. f_t(P)=center_p(-x(P)/y(P)) mod q.

The quotient in feature 3 is exact integer division. It is the H016 kappa
itself, without multiplying by Y or applying a character. Its intermediate
integers fit a signed 64-bit word for this p. Feature 4 is a coordinate-field
inversion, followed by centering and reduction into a DIFFERENT field.
Define all four at O to be zero, although O never appears in this orbit.
Prime odd full order also excludes affine y=0, so feature 4 has no sampled
pole. Check every affine sample lies on the curve and has nonzero y.

Generate P_0=G and P_(i+1)=[w]P_i for i=0,...,126. Use the fixed scalar
binary method with projective internal coordinates and explicit exceptional
case handling. Normalize each sample with one paid inversion; compute its
four features once and share the sample. Do not enumerate all q points or
precompute an inverse table. The scalar w<=33 is small if certification
succeeds, but the conservative ledger below allows a 14-bit multiplier.

Run standard Berlekamp-Massey over Fq independently for the four streams.
Maintain the usual discrepancy, connection polynomial, previous polynomial,
shift, and current complexity L. At each update stop that stream immediately
if L>=64. No further feature evaluation for stopped streams is necessary.
Stop sampling when all four have stopped or 128 samples have been processed.
Connection polynomials must use actual finite-prefix BM, not a fitted
recurrence chosen after holding out inconvenient terms. Store prefix values
and the BM update trace for audit; all trace writes are paid.

Finite-prefix complexity means minimum recurrence LENGTH L; it must not be
replaced by the actual degree of the current connection polynomial C, which
can be smaller for finite prefixes. A terminal update can write a coefficient
as high as index128 even when old L<=63. Reserve129 coefficients or stop at
the mathematically justified discrepancy/length update before constructing
that terminal polynomial; retain enough trace to audit the stopping event.

The stopping event is sound because the minimal recurrence degree for a
prefix cannot exceed the minimal recurrence degree for the entire sequence.
Globally, the sequence has period q-1, and X^(q-1)-1 is separable and split
over Fq. Its minimal recurrence degree equals the nonzero-power count in its
unique expansion sum_(e=0)^(q-2) c_e n^e. A connection-root convention may use
reciprocal roots; that does not affect the degree statement.

No root factoring, exponent discrete logarithm, target recovery, or claim
about an unobserved suffix is part of this diagnostic. Failure to reach 64
is UNRESOLVED, not a sparse-power discovery. Reaching 64 excludes t<64, not
t<=64 and not a sparsity bound at other curve sizes.

## Streamed controls; no full tables

Run one planted control of length 16: s_i=1+2*w^i+3*w^(2i) in Fq. Generate
the powers by recurrence and require BM complexity exactly 3 at completion.
The roots 1,w,w^2 are distinct and the coefficients nonzero. Require its
reported recurrence to reproduce its supplied terms, with all checks paid.

Run one deterministic pseudorandom control of at most 64 terms, stopping at
complexity 32. Freeze the 32-bit LCG state to 18018 and update
state=(1664525*state+1013904223) mod 2^32. Output state mod q. This is an
implementation comparison, NOT an iid-uniform null model, and its result is
not an admission or statistical-significance threshold. No retries or seed
search. Store only the generated prefix. A random-looking result is not a
proof that coordinate features obey a random-sequence law.

Controls and feature streams share the same global resource budget. A failed
planted control invalidates the run. There is no inverse, log, random-function,
or complete orbit table. No multiple-testing p-value is claimed: report each
of the four exact stopping events separately.

## Instrumentation and conservative paper ledger

ONE cap: 1,000,000 instrumented events AND 60 seconds wall time, whichever
comes first, including setup, selection, controls, trace storage, and checks.
No per-curve or per-feature reset. Start the wall clock before selection.

An event is one word integer or modular addition/subtraction/multiplication,
division/remainder, comparison, bit operation, dynamically indexed array
read/write, or recorded trace item. Modular field arithmetic on these bounded
word operands is a unit arithmetic primitive; exponentiation, inversion,
point operations, scalar multiplication, BM iterations, and primality tests
are NEVER unit primitives. Expand them into the counted operations. Fixed
scalar-register assignments and fixed-field record access are ordinary local
implementation bookkeeping, not charged as a second memory operation on top
of each arithmetic instruction; dynamic coefficient-array access IS charged.
Report this RAM-event convention, not a bit-operation or runtime equivalence.

Use binary modular powering for inversions and exponent tests. Before a run,
the implementation must expose a formula-level audit meeting the following
ceilings; these are preflight ceilings, not measured performance. In
particular use a short-Weierstrass projective scalar implementation whose
ordinary doubling/addition/exception dispatch takes at most 64 events per
group step, plus at most 112 events per 14-bit scalar loop. A 14-bit scalar
test then has at most 27 group steps and costs at most 1840 events. Do not
silently use inversion-heavy affine steps under that allowance.

| Work | Reserved events |
| --- | ---: |
| Certify p, enumerate/certify q candidates, factor q-1, discriminants and bounded point search | 35,000 |
| At most 96 order-certification scalar tests, 1840 each | 176,640 |
| Primitive-w certification, including all powering and control overhead | 25,000 |
| At most 127 sample scalar multiplications, conservatively 1840 each | 233,680 |
| Sample normalization, feature calculations, curve checks, sample storage | 35,000 |
| Four stopped BM streams: coefficient work and all overhead/inversions/trace | 400,000 |
| Both streamed controls and their validation | 35,000 |
| Remaining global bookkeeping/report data | 20,000 |
| Total paper reservation | 960,320 |

For the BM reservation, before a stopping update L<=63; the discrepancy
sum and stored previous polynomial can involve at most64 coefficients each,
but the shifted destination can extend to index128 as noted above.
Per iteration, allow 10 events per coefficient for discrepancy and polynomial
update together, giving 4*128*64*10=327,680 events. The remaining 72,320 cover
modular inverse powering, discrepancy/degree branches, copying at most 64
coefficients when the previous polynomial changes, and trace overhead. This
allowance must be checked against the actual BM implementation, including
its copy policy, before execution; the global cap overrides every estimate.

Independent STATIC implementation review found bounds33665 for features and
34394 for controls, exceeding the original30000/25000 reservations. Root
explicitly amended these to35000 each BEFORE any run, using15000 of the prior
reserve. The global1M cap and event model are unchanged. BM phase bound399426
includes the initial outer-loop comparison in addition to the399425 core bound;
it fits400000. These are paper bounds, not observed counts or runtimes.

The remaining39680 reserve is limited. If the implementation audit cannot
meet any major allowance, do not move work off-ledger, reinterpret the event
unit, increase the cap, or run anyway: return a failed preflight to root.
The 60-second condition is plausible for fewer than one million small-word
events but is unmeasured and may fail under instrumentation. Any cap hit is
inconclusive, including a hit during fixture selection or controls. Partial
prefix certificates can be preserved explicitly as partial results if their
planted-control validation has completed, without claiming the run completed.

## Admission and interpretation

This is a proposed narrow diagnostic with credible paper-level cap fit,
conditional on implementation audit; it is not authorization to implement or
execute. Its value is one exact counterexample to the strongest sparse-power
premise for each stopped feature at a non-microfixture size. It is not a
theorem about asymptotic sparsity, a demonstration of general randomness, or
a negative result for all coordinate-aware algorithms. Even a passing finite
prefix needs fresh mathematical justification, paid global validation or a
stated probabilistic model, and full factoring/exponent/recovery costs before
it can motivate a solver.

There is no automatic escalation. A larger prime field, another curve family,
another generator, threshold 128, more samples, or new features requires a
new explicit decision after reviewing this result and its costs. No growing
size sequence is preauthorized. No data becomes hidden solver advice.

## Final pre-execution authorization

Independent native Sol static review returned GO after the explicit reservation
amendments, confirming formulas, BM lengths/arrays, certificate, controls and
cap handling. Root also inspected the full implementation and accepted ONE
execution. This supersedes earlier proposed-only wording; it authorizes no
rerun or parameter change. The script's --approved-execution flag records this
coordinator decision, not user interaction or an independent approval mechanism.

Internal timing checks do not interrupt final stdout transport or a second
timeout-report encoding. Therefore root will also use an external process limit:

    timeout --signal=KILL 60s python3 research/experiments/H018/bm_probe.py --approved-execution > research/experiments/H018/initial_results.json

An external timeout or malformed/partial report is INCONCLUSIVE, never a
completed exclusion. All numerical work and controls share the one event cap;
no warmup or off-ledger experiment preceded this authorization.
