# Fresh structural discovery r4

Status: original full two-order Euclidean signing target UNRESOLVED.
No substantial-result nomination. See `candidate.md`, §§1 and 7.

The report proves three technical method obstructions, including a quantitative
crossed-prefix Dirichlet-energy lower bound. They do not refute the target.
No independent proof/contribution review or formalization has been claimed.

Author: Myeongjin Kang; no affiliation. Original prose CC BY 4.0, original code
MIT; see RIGHTS.md for the third-party boundary. All task writes are inside
this directory. No nested agents, shared-file edits, commits, counting changes,
external messages, uploads or submissions were made.

Files:

* `original-scope.md`: scope fixed at target selection.
* `candidate.md`: exact quantifiers, full supporting proofs and remaining step.
* `source-contracts.md`, `literature-screen.md`: operation-level source contracts,
  exact pinned URLs, primary antecedents and honest reading limits.
* `checks.py`, `checks-receipt.json`: exact finite algebra and bounded minimax
  checks, with fixed seed and no third-party Python dependencies.
* `verify.py`: zero-write, zero-network verifier, authenticating before replay.
* `mutation_tests.py`: optional tests on disposable copies only.
* `inputs/private/`: private context and third-party reading copies; not release
  artifacts. Retention does not imply every retained byte was read.

Use Python 3. Standard library only. Obtain the detached `seal.json` SHA256 from
the handoff, then run:

    python3 -B verify.py --seal-sha256 HANDOFF_SHA256

The verifier first authenticates the seal, both immutable inventories, exact
membership, every file's SHA256/size and pinned Git blobs, including the stored
receipt. Only then does it run checks.py and compare stdout byte-for-byte.
It reauthenticates after replay, writes nothing, and never regenerates a
receipt or inventory. A successful replay is evidence integrity and finite
support, not a proof of T2, priority or independent review.

Optional verifier rejection controls:

    python3 -B mutation_tests.py --seal-sha256 HANDOFF_SHA256

This first verifies the original package, creates disposable copies under this
owned directory, mutates only the copies, and deletes them on exit. It tests
receipt tampering, source-input tampering, missing/extra files, and a changed
checker that would write a sentinel if executed. Authentication must reject
that checker without executing it. The original inventory is never resealed.
Do not run two verifier/mutation processes concurrently: disposable copies
temporarily appear under this directory during those explicit tests.

The source retrieval records also explain the gzip decoding of Knuth's TeX.
Local PDF extraction used `pdftotext -layout`; selected pages were rendered with
`pdftoppm -scale-to 1500 -png` and visually inspected. Those reading tools are
not needed for replay. No mathematical inference depends on numerical
floating-point calculations.
