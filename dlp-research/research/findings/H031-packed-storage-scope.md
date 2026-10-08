# H031 packed collision storage: source scope

Status: primary artifact inspection and independent paper scope review COMPLETED.
This revisits the existing comparator in H002 T2, not a new algorithm.
No solver was built, run, imported or benchmarked. Verified improvement NONE.

Root pinned the author's public PCS repository through
`https://api.github.com/repos/mtrimoska/PCS/commits/master`, resolving to
`211e174a04fa74c3c2cf4019b92f40961216a4a7`, then read raw source over HTTPS with
Python `urllib.request.urlopen(..., timeout=20).read().decode()`. Reads used
`src/pcs.c`, `src/pcs_struct_PRTL.c` and `src/pcs_vect_bin.h`; no checkout,
third-party code execution or source mutation. A web PDF fetch403 was an access
failure, not evidence against the paper. Native Sol independently reviews its
one-collision versus many-collision model and assumptions.

The public [README](https://github.com/mtrimoska/PCS/blob/211e174a04fa74c3c2cf4019b92f40961216a4a7/README.md)
documents a packed radix-tree/list representation and a conventional hash-table
comparator. It separates synthetic insertion benchmarks from complete ECDLP runs.
Its Table7 fixed-memory experiments used modified code; the current version is
not configured to reproduce that restriction. Published platform measurements
are not local measurements and cannot supply GPU rates or a universal price.

Pinned code confirms the scope:

- [pcs.c, is_collision](https://github.com/mtrimoska/PCS/blob/211e174a04fa74c3c2cf4019b92f40961216a4a7/src/pcs.c#L98)
  starts from stored scalar seeds and replays two trails, reconstructing labels
  before recovery. It also reconstructs a point for sign handling. This is a
  concrete example of paid label recovery, not a compulsory two-label endpoint
  record and not free replay.
- [pcs_struct_PRTL.c](https://github.com/mtrimoska/PCS/blob/211e174a04fa74c3c2cf4019b92f40961216a4a7/src/pcs_struct_PRTL.c#L40)
  stores coordinate suffix and seed, while bucket location and distinguished-bit
  predicate supply omitted coordinate bits. It allocates the bucket array and
  locks; insertion traverses a sorted linked list. Memory-limit checks at lines56
  and126 are explicitly commented out in this pinned revision.
- [pcs_vect_bin.h](https://github.com/mtrimoska/PCS/blob/211e174a04fa74c3c2cf4019b92f40961216a4a7/src/pcs_vect_bin.h#L15)
  has a fixed byte payload and next pointer per packed node. Payload bit count
  alone is not total storage: buckets, pointers, locks, empty entries, allocator
  overhead and other solver state must be counted under the chosen metric.

These reads do not certify correctness, concurrent behavior or complete resource
accounting of the external implementation. They establish a known concrete
comparison capability and a limitation of reproducing a published fixed-capacity
experiment from the current artifact without changes.

Any H002 T2/H031 storage crossover must grant such packing and paid recovery to
the baseline, match peak stored bits and retained-work policy, and charge lookup,
insertion, replay, initialization and verification. A storage-only result does not
establish a stopped-solver advantage. No new experiment is admitted here.

## Conditional one-collision price model

Root and native Sol both read the
[published TCHES paper](https://tches.iacr.org/index.php/TCHES/article/download/8794/8394/5595).
Section3.1 Eq4 gives, with A=sqrt(pi n/2), L workers and distinguished fraction θ,

    T(θ) = A tc/L + tc/θ + A θ ts/L.

tc and ts price computation and storage. Its stationary optimum is
θ0=sqrt(L tc/(A ts)), clipped to the permitted interval. This is a random-map
approximation with birthday/geometric-tail and linear-scheduling assumptions,
not an exact finite EC runtime theorem. AppendixA uses approximations; no
deterministic worst-case claim is transferred. Table5 reports similar one-DLP
runtimes and reduced memory; the reported limited-memory many-collision gain
is a different scope. Root read the primary passages, not just the abstract.

Root's conditional budget observation, independently confirmed by Sol: expected
occupancy about Aθ suggests θ≤w/A when w is record capacity, but this is NOT a
hard peak-memory guarantee. If a valid implementation imposes θmax<θ0, and
compression permits a larger θmax without increasing other costs, the model
predicts reduced one-target delay. Thus it would be wrong to infer that storage
can NEVER matter for a single target. Once unconstrained θ0 is available, merely
raising capacity cannot improve this fixed-price model's optimum. Changed ts,
replay, allocation, communication, setup and overflow policy can change the
comparison and all need payment. Applying Eq4 unchanged after freezing memory
or evicting entries is not justified by an expected-occupancy inequality.

This supplies a scoped price condition, not a credible new gain: packed storage
is already a baseline capability, and no measured candidate crossover or peak-
capacity proof is provided. No numerical work follows. Root owns this finding
and STATE; native reviewer read-only/no edits/experiments/children. Grok's original
H031 independent proposal remains live and was not duplicated.

Native Sol final review COMPLETED: §3.2's many-collision formula assumes a
fill-then-search policy and a sufficiently-large-collision-count approximation;
substituting one collision does not justify a one-ECDLP cost formula. The paper's
specific byte layouts do not lower-bound competent packed hash tables. For H002
T2, antecedent packing/replay does not establish any benefit from internal
checkpoint emission. Root accepts these scopes. No candidate run authorized.

Validation: `./scripts/check.sh > /tmp/ecdlp-h031-packed-check.log 2>&1` exit0,
366 existing audits. Source records only, no Lean/Audit changes. Next change to
the conclusion would require an explicit complete-cost crossover at matched peak
capacity and success, not a transfer of published storage-only timing.
