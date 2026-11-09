# Floor-sum manuscript and source packet

This packet certifies the exact four-variable lower bound stated in paper.md.
No acceptance, credit, priority or publication decision is included. Counts stay
9 additional / 39 total / next 40. Root owns those decisions.

## Strict replay

The distribution puts every mathematical source under formal/. No owned object
files are included. Use a fresh extracted directory. Do not run run.sh or the
historical verify_audit.py: they are preserved provenance/generation artifacts,
not the complete endpoint replay/audit interface.

From formal/, with the pinned external libraries present:

```sh
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
export HELPER_GUARD=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
bash replay.sh
python3 "$HELPER_GUARD" python3 full_audit.py .
```

replay.sh runs 437 mathematical modules and 22 audit partitions in its explicit
dependency order, serially; it never skips an existing object to claim freshness.
Use a fresh extraction, so imported owned objects can only come from this run.
For this assigned execution HELPER_GUARD MUST have exactly the value above.
The packet also contains its byte-identical helper as a documented configurable
default for later users; this does not change its limits. Lean launches only
through lean_guard.py, itself through the helper. lean_guard.py deliberately
starts the authorized Lean child in a separate process group and clears the
helper AS limit only for that child via prlimit. Lean's fixed -j1 -M2700,
2800 MiB sampled group RSS, CPU210/wall230 remain enforced. Helpers retain
512 MiB AS/group RSS and CPU210/wall230. No parallel invocations or cap raises.

For an archive rebuild from the extracted distribution root, run
`python3 "$HELPER_GUARD" python3 build_packet.py`. Its standalone mode reads
SOURCE-MANIFEST.json and needs no lane history. It writes two matching copies
of each archive and reports their hashes. The included verify_final.py is the
lane-delivery integrity verifier, requiring the lane's replay logs and bindings;
it is not the standalone formal replay interface.

## External environment and dependency scope

pins.json specifies the fixed Lean path/hash and all nine actual package heads.
lean_guard.py retains these absolute external dependencies:

* /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean
* /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages

The latter supplies already built .lake/build/lib/lean libraries. Lean's own
installation, Python3 standard library, bash, Linux /proc and prlimit are also
required. No network, solver, generation helper, historical archive or Python
mathematical library is needed for compilation and full_audit.py. Package heads
are read from existing metadata without git commands. Checking head metadata
does not independently rebuild or certify the entire external library cache.

The historical generation scripts in formal/ retain absolute references to
immutable predecessor evidence. They document generation; this packet does not
promise self-contained regeneration of every historical experiment. The exact
query, original solver proof and DAG are included under certificate/. They are
provenance inputs, not additional axioms required by the Lean endpoint. Primary
PDF/text evidence is under sources/. Inspected scopes are stated in paper.md;
other source-body claims are attributed to the preserved independent reviews.

## Integrity and deterministic archives

source-packet.tar.gz and source-packet.zip contain the same source member set,
including their internal SOURCE-MANIFEST.json. Archive metadata is canonical:
tar uid/gid/mtime zero, mode0644, empty names; gzip empty filename/mtime0;
ZIP fixed 1980 timestamp, mode0644, stored members. build_packet.py rebuilds each
twice and requires exact byte equality, then extracts and compares every member.
The mathematical .lean members are also compared against the frozen original
499-member input archive. No owned .olean/.ilean/.ir or compiled cache is
distributed. Final lane manifest excludes itself and verification-receipt.json;
verify_final.py is run separately after substantive writes. Its receipt verifies
the originals/copies and lane manifest and is not an acceptance verdict.

PDF NOTAUTHORED / QA_NOTPERFORMED: the mandatory unmodified marker failed under
the fixed helper cap. Both Node failure logs are preserved. No PDF was created.
