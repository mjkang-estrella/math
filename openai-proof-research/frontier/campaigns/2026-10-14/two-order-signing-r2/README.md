# Two-order signing, round r2

Status: the full target T2 is UNRESOLVED. Nothing is nominated as a
substantial result, and nothing is counted. See `candidate.md`, §§1 and 7.

Main finding: the d=1 case of T2 is, up to a factor 2 in the constant, the
weighted one-block discrepancy question that Cherniavskii, Kupavskii, Moiseev
and Shekhovtsov posed as open in October 2026. It is also Bansal–Rohwedder–
Svensson's weighted two permutation discrepancy. Reis's Conjecture 16 and
Bérczi–Liu–Reis–Tarnawski's Conjecture 5 each imply it. The round also proves
an O(d log N) baseline over the full scope and records eight attempted
mechanisms with the exact point where each fails. No independent review or
formalization is claimed.

Author: Myeongjin Kang; no affiliation. Original prose CC BY 4.0, original code
MIT; see `RIGHTS.md` for the third-party boundary. All writes for this task
are inside this directory, apart from exploratory scratch files under `/tmp`.
No nested agents, shared-file edits, commits, counting changes, external
messages, uploads or submissions were made.

Files:

* `original-scope.md`: T2 restated unchanged; what counts as success.
* `candidate.md`: full report with proofs, failed mechanisms and the unpaid step.
* `source-contracts.md`, `literature-screen.md`: URLs, hashes, reading extents,
  queries, and exactly what each source is used for.
* `retrieval-literature.json`, `provenance.json`: retrieval and run records.
* `checks.py`, `checks-receipt.txt`: exact finite checks (standard library,
  rational arithmetic, fixed seed) and their stored stdout.
* `verify.py`: read-only verifier. It authenticates before it replays.
* `mutation_tests.py`: optional rejection tests on disposable copies.
* `exploration/`: unverified numerical scripts and logs (see its README).
* `inputs/private/`: third-party reading copies and copied r4 context. Not
  release artifacts. Keeping a file does not mean every byte of it was read.
* `input-manifest.json`, `output-manifest.json`, `seal.json`: inventories and
  the detached seal.

Use Python 3, standard library only. Take the `seal.json` SHA256 from the
handoff, then run:

    python3 -B verify.py --seal-sha256 HANDOFF_SHA256

The verifier first checks the seal's SHA256 against the handoff value. It
then checks both inventories against the seal, exact file membership (no
missing, extra or symlinked files), and every file's SHA256 and size. It also
checks the r4 chain: the copied r4 seal has the r4 handoff hash, the copied r4
manifests match that seal, and the copied r4 report, scope and thesis
extraction match their r4 manifest entries. Only after all of this passes does
it run `checks.py` and compare its stdout byte-for-byte with the stored
receipt. It then authenticates everything again. It writes nothing, uses no
network, and never regenerates a receipt or inventory. A pass shows integrity
and finite support only. It is not a proof of T2.

Optional rejection tests:

    python3 -B mutation_tests.py --seal-sha256 HANDOFF_SHA256

This first verifies the original package. It then makes disposable copies in
a fresh temporary directory outside this package, changes only the copies,
and deletes them on exit. It checks that the verifier rejects receipt
tampering, input tampering, missing and extra files, a wrong handoff hash, a
checker that would write a sentinel file if run (rejected without running
it), a consistently resealed copy with a wrong receipt (rejected at replay),
and a resealed copy with a broken r4 chain.
