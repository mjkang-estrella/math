# H019 — One frozen exact root-certificate screen

Date: 2026-10-08. **Disposition: INCONCLUSIVE under the registered finite continuation criterion. Verified factoring complexity improvement: NONE.**

The single trial produced **one independently arithmetic-verified primitive-irreducible upper-count certificate and three unknowns**. All five controls behaved correctly. Every research input passed its base identities, modular square-free certificate, global coefficient dominance, all inside-root disks, and positive rational geometry checks. Only the 262,144-bit input passed H017 equation (11). The 65,536-bit input failed that sufficient inequality, so the requirement for certificates on **both** largest inputs was not met. It has not been weakened.

There were zero verification failures, errors, timeouts or unstarted research inputs. These are four fixed public odd integers, not a semiprime/composite or hard-factor sample. No factors were supplied or found. The new implementation and its significant finite claim still require independent critical review; the independently written arithmetic reference within this implementation is not a separate review by another researcher.

The controlling [complete preregistration](../hypotheses/H019.md), [accepted H017 theorem](H017-resultant-tail-supply.md), and [H017 independent review](H017-independent-review.md) were read in full, along with AGENTS.md, README.md, SPECIFICATION.md, RESEARCH_LOOP.md, RESEARCH_TEAM.md and STATE.md. Only this finding and adjacent H019-certificate artifacts were written. Shared solver, Lean, STATE, registries, parent hypotheses and prior evidence were untouched.

## The fixed implementation and proof obligations

The [candidate](H019-certificate-candidate.py), [independent arithmetic reference](H019-certificate-reference.py), [outer runner](H019-certificate-runner.py), and [expanded protocol](H019-certificate-protocol.json) preserve the preregistered input rule and constants. Exact inputs and control centers are in [inputs.json](H019-certificate-evidence/inputs.json) and [controls.json](H019-certificate-evidence/controls.json). Each research worker received only an N_hex input object; the public degree comes from its bit length. The frozen input list uses one Random(1919), exactly four getrandbits(n-1) calls in order, and N=(1<<(n-1)) | getrandbits(n-1) | 1.

For each input the candidate used exact integer Newton roots and ordinary base-m digits. The independent reference checked m^d<=N<(m+1)^d, every digit, actual degree d, monicity, f(m)=N, H=2^ceil(67473*n/(20000*d^2)), and (h_*-1)^5<H^4<=h_*^5. The fixed prime 65537 was trial-divided once by every integer 2 through 256 during charged setup; [its certificate](H019-certificate-evidence/prime-certificate.json) records all nonzero remainders. Each square-free witness contains modular Bezout polynomials, independently convolved with f and f' to produce exactly 1 modulo that verified prime. No extra modulus, square-free-part replacement or irreducibility assumption was used.

Strict coefficient-(d-2) dominance at R=2H+2 is H017 equation (19), proving exactly d-2 roots inside the circle, two outside, and no root on it. Exactly d-2 disjoint rational disks were then certified inside the circle. H017 equation (18) gives exactly one root of the **full integer f** in each disk. Together these two counts account for all d roots. The omitted two roots were not classified using approximate locations.

Approximate proposals used precisely one simultaneous Aberth iteration on the degree-(d-2) truncation, coefficients divided by their maximum before floating conversion, the Cauchy circle at half-phase angles, at most 500 sweeps, and correction cutoff 2^-42. Centers were rounded to the 2^-40 grid, with fixed disk radius 2^-24. There was no alternative start, precision, radius or retry.

For z=(x+iy)/Q, Q=2^40, the candidate obtains A_j=Q^d*f^(j)(z)/j! by integer Gaussian Horner shifting. The reference imports no candidate helpers: it reconstructs A_j from the direct binomial sum with precomputed Gaussian powers. Both check, exactly,

    max(|Re A_1|,|Im A_1|) 2^[24(d-1)]
      > sum_(j != 1) (|Re A_j|+|Im A_j|) 2^[24(d-j)].

Squared integer comparisons establish disk disjointness and containment. Each witness records the centers, Taylor-array hash, exact cleared disk-comparison integers, their hashes and bit lengths. All 115 research disks passed both arithmetic implementations.

The candidate evaluates the reviewed rational U_i, L_ij and triple minimum by integer cross-products; the reference reconstructs the same quantities with Fraction. All pair bounds, a minimizing triple and the reduced positive kappa=x/y are retained. Finally both implementations multiply the cleared equation (11), with the reference using separately expanded factors. Equality would be accepted for (11); every Rouché inequality remains strict.

## All four research dispositions and exact target counts

For each case below, C_trial is the exactly evaluated expression (h_*-1)(2h_*-1)^2+(d-2). **It is a certified upper bound only in the passing case.** In the three unknown cases, its arithmetic value is retained for reproducibility but is not asserted to bound the population. A failed sufficient inequality gives no lower population or positive-supply evidence.

### 4,096 bits, degree 15: UNKNOWN

H=2^62; k=13, r=2. Aberth converged after 50 simultaneous sweeps. All 13 inside disks passed. Worker wall time, including startup and evidence, was 0.314837 seconds; its internal time was 0.252224 seconds.

The independently checked equation-(11) comparison failed: left product 262,653 bits, right product 294,544 bits. Disposition: unknown at the count inequality; there is no certified upper count from this chosen h_*.

```text
h_* = 0x3080c007655cc
C_trial (not a certified bound) = 0x6f6e336b6f846858fe6c7d65b9c9896712c388
```

[Full exact witness, kappa, comparison factors and product hashes](H019-certificate-evidence/n4096-d15-witness.json); [worker result, counters and stage times](H019-certificate-evidence/n4096-d15-result.json).

### 16,384 bits, degree 22: UNKNOWN

H=2^115; k=20, r=2. Aberth converged after 22 simultaneous sweeps. All 20 inside disks passed. Worker wall time, including startup and evidence, was 0.466275 seconds; its internal time was 0.383316 seconds.

The independently checked equation-(11) comparison failed: left product 782,415 bits, right product 839,088 bits. Disposition: unknown at the count inequality; there is no certified upper count from this chosen h_*.

```text
h_* = 0x100000000000000000000000
C_trial (not a certified bound) = 0x3ffffffffffffffffffffff80000000000000000000000500000000000000000000013
```

[Full exact witness, kappa, comparison factors and product hashes](H019-certificate-evidence/n16384-d22-witness.json); [worker result, counters and stage times](H019-certificate-evidence/n16384-d22-result.json).

### 65,536 bits, degree 34: UNKNOWN

H=2^192; k=32, r=2. Aberth converged after 18 simultaneous sweeps. All 32 inside disks passed. Worker wall time, including startup and evidence, was 0.966190 seconds; its internal time was 0.908751 seconds.

The independently checked equation-(11) comparison failed: left product 2,515,137 bits, right product 2,538,571 bits. Disposition: unknown at the count inequality; there is no certified upper count from this chosen h_*.

```text
h_* = 0x3080c007655cb8d73268e641d5c266eb4c494ff
C_trial (not a certified bound) = 0x6f6e336b6f8480853d874c2c9fea59ff43f038c87b34c6459e195cb9e1164f9ff5f3111004100fe97ccb9806b08d4bb8870113e198221ae3350e
```

[Full exact witness, kappa, comparison factors and product hashes](H019-certificate-evidence/n65536-d34-witness.json); [worker result, counters and stage times](H019-certificate-evidence/n65536-d34-result.json).

### 262,144 bits, degree 52: PASS

H=2^328; k=50, r=2. Aberth converged after 51 simultaneous sweeps. All 50 inside disks passed. Worker wall time, including startup and evidence, was 3.621777 seconds; its internal time was 3.546363 seconds.

The independently checked equation-(11) comparison passed: left product 8,425,749 bits, right product 7,972,362 bits. The following C is the certified finite upper bound.

```text
h_* = 0x5472d14ee54db115a4ea11db2e5ade00b464328b6706d4b0455447ad0de103ad96
C = 0x24c2230d75cce92d4a43c840ec1c3eb99817b92b236d471a569f595302dd051c78ff0d2f9b972e0d41c6189a1719d78708f6cfac7ae65df0a7834a10adf3ae2f102fa85182ce6bdeba2ea43b1c4485e6aa2d5886c51ba90e973f6c3fe3467deb34b35f
```

[Full exact witness, kappa, comparison factors and product hashes](H019-certificate-evidence/n262144-d52-witness.json); [worker result, counters and stage times](H019-certificate-evidence/n262144-d52-result.json).

## Scope of the passing finite certificate

For the archived 262,144-bit N, its exact degree-52 ordinary-base polynomial f, A=max_i f_i and H=2^328, the 790-bit integer C above bounds the number of genuine **primitive irreducible** quadratics

    g=aX^2+bX+c, 1<=a<=H, |b|,|c|<=H,

satisfying

    |Res(f,g)|^(5d) N^9 <= [(3H)^d(d+1)A^2]^(5d).

Here irreducibility refers to g over Q. The count theorem permits square-free reducible f; no number field or irreducibility of f was certified. Its exact geometric witness is

```text
kappa_cert numerator   = 0xcf18c3e20cc4183a7d759f4282800000000000000000000000000000
kappa_cert denominator = 0x463d75406ab7838b2061a3f6354919c065e3b0730b7606e1fcf926aaf061
minimizing triple      = [3, 4, 5] (zero-based disk indices)
E = 5*d*(k-2)          = 12480
left product SHA-256  = b9dbac1d9a7b0d7176a5c9215b9ca8a31d6c56a2fa8b1ed0a5016d973dcc38b4
right product SHA-256 = c68fbd0cf1f6bfd844da1e797aec1e05fbce070b1b19f5f83b27ffac0c81ccac
```

The exact factored operands are archived, rather than decimal-rendering the 8,425,749-bit left product and 7,972,362-bit right product. Product hashes use minimal unsigned big-endian bytes. The source theorem is H017 equation (11) implying equation (10); no quadratic cube was enumerated, and the certificate is an upper count, not an exact population cardinality.

Reducibles and contents retain H017's separate asymptotic qualifications. No unspecified O constant is presented as a finite all-output bound. Reducibles may introduce distinct linear factors; square-class parity R=V+c*1^T, even-cardinality conditions and odd dependency cosets are not discarded. Zero resultants are not smooth nonzero norms. H016 processing and H018's corrected degree model remain separate. The heuristic selected-tail smoothness comparison proves neither useful supply nor rank, square roots or proper splitting.

A finite certificate does not establish asymptotic geometry, an all-input bound, a frequency for random N, or a randomized field-selection escape probability. Unknowns do not refute the theorem or establish supply. A timeout would have been a censored implementation measurement; none occurred here. No matched factoring baseline was run, and verified factoring complexity improvement remains **NONE**.

## Controls, budgets and immutable evidence

Both arithmetic implementations accepted the correct disks for X^2-2 and X^2+1. Both rejected the disk centered at zero for X^2-2 at the disk-Rouché gate, the duplicated valid disk list at disjointness, and (X-1)^2 at square-freeness. The full control batch took 0.265088 seconds under its 3-second killable cap. Controls remain separate from the fixed denominator of four research inputs.

Only syntax parsing of the three Python files and JSON parsing of the expanded protocol preceded execution. No candidate import, control, root proposal, smoke attempt or exploratory run preceded freeze. During the one run, input generation and source/input snapshotting were charged to setup. Input generation through preparing the freeze manifest took 0.038494 seconds; setup including prime verification took 0.060650 seconds. The freeze was written before either arithmetic implementation was imported.

The exact invocation was:

```bash
timeout --signal=KILL 60s .venv/bin/python -B research/findings/H019-certificate-runner.py
```

The runner clock reported 5.834619 seconds through its final output; the recorded completion covers 5.830190 seconds through evidence sealing, within the 55-second internal allowance. All four workers received 12-second caps, additionally limited by remaining wave time with a one-second evidence reserve. No cap was reached or enlarged. Stage times include incremental evidence flushing; counters describe observed operations, not a certified bit-machine cost model.

[Outcomes](H019-certificate-evidence/outcomes.json) retain all six status categories: **1 pass, 3 unknown, 0 verification failures, 0 errors, 0 timeouts, 0 unstarted**. Every control was correct. The runner exclusively creates its evidence directory and refuses a second run/overwrite. Per-worker results, append-only stage logs, exact witnesses and stdout/stderr logs survive worker termination. Last-flushed counters would be explicitly partial if a worker died. The original frozen source has not been changed or rerun.

The [freeze manifest](H019-certificate-evidence/freeze.json) contains the exact input list, source/document snapshots, platform, Python version and all pre-execution hashes. Its SHA-256 is `c60a9c190308e9ab20c642496ea43ca8f12db2b46de186b907e27b4d504a87af`. The [seal](H019-certificate-evidence/seal.json) lists 57 files totaling 1,633,679 bytes; its SHA-256 is `4f71fce92f6412014d6b154e7d1a2344c75420c32bf3c1bbd95443588b6b164f`. [Completion](H019-certificate-evidence/completion.json) links the seal. Hashes establish byte correspondence, not independent historical attestation. All 13 snapshotted original sources/documents matched their hashes at completion.

Frozen implementation SHA-256 values:

- `H019-certificate-candidate.py`: `79bd5b42a1595f196f3c5b5f4dcb95616496eb3d48ead59fcb57a9b6926bba10`.
- `H019-certificate-reference.py`: `72d8ff5f3b23706c3561b40aa10d993686d843cd2246de1e008fb9d748e7a22f`.
- `H019-certificate-runner.py`: `9972db6ab61463be7b7b5ded09b7714118a9d59498ada9ef70b6bbdc198b5064`.
- `H019-certificate-protocol.json`: `f50f4965f34127a2834e10663e505d280c38121cb9daae786a84bd6821b1ac5d`.

The original artifacts and snapshots allow a separately authorized reviewer to reconstruct every certificate from the archived N. This task performed no replay after the single trial. Post-run work was limited to reading recorded evidence, reporting stored values/hashes and authoring this finding.

## Handoff

The screen is **inconclusive**, since only one of the two required largest cases passed. The valid individual certificate retains its exact finite upper-count claim, subject to independent implementation review. The next authorized parent action is shared project checks and independent review of the frozen proof-linked implementation and evidence, including the strict predicates, all-root coverage and count operands. No automatic new experiment is started. Changing this conclusion would require a separately preregistered mathematical or implementation round; the current source, criterion and evidence stay fixed.

No packages, recursive delegation, commits, publication, scheduler, hidden factors, instance-selection advice or shared solver/Lean changes were used. The parent will run shared checks after handoff, as instructed.
