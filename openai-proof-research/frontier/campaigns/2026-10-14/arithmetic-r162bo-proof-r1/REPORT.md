# Detached artifact report: R162BO proof review round 1

Entire unchanged frozen-statement correctness verdict: PASS.
No necessary mathematical repair or essential unverified dependency remains.
This assigns no contribution, acceptance or campaign count.

FINAL.md: SHA256 2c493c2511d4887b13ea3eac2703402bbb949c2f116282c81e60b019cd247700; bytes 3418; full mode 33188.
MANIFEST.json: SHA256 06afbe9b6a3ccd7f126174f8b1604938ea57c9caf6bc92054a0cb064b5679532; bytes 3718; full mode 33188.
REPORT.md is inside the exclusive review root and outside the manifest payload.
Its SHA256, byte length and full mode are detached in the final handoff, avoiding
any self-hash cycle. All three anchors must be supplied explicitly to the verifier.

The payload contains 19 sorted unique file records and 3 directory
records, including the root. Whole-root membership is exactly that payload plus
MANIFEST.json and REPORT.md. Every payload file has a SHA256, length and full
stat mode; every directory has its full stat mode. The detached files' own modes
and lengths are checked against the explicit external anchors.

The sealer preflights the SAME verification function using the final in-memory
MANIFEST/REPORT bytes and modes before exclusively creating either file. It then
runs the identical function on the actual files. No sealed payload is mutated to
fit verification. Tiny own copied controls check bad detached anchors, changed
bytes, changed file/directory modes and an extra file; the restored baseline passes.
Artifact checks are not mathematical gates.

The 60 exact author files were hash/length/full-mode checked before and after the
review; exact authorized directory modes also match. False semantic-read flags
were respected. No author verifier/binding traversal, old-original read, peer-review
inspection, author change or shared-index edit occurred.

Actual proof reasoning and primary/source provenance remain private/local under
private/. All nine canonical texts and four complete relevant primary/companion
extractions (65 pages) were actually read. The other acquired primary bodies,
transitive ancestry and exhaustive classical-priority literature were not read;
none is an essential dependency of the self-contained proof.

Read-only verifier, run from the required project workdir:
python frontier/campaigns/2026-10-14/arithmetic-r162bo-proof-r1/private/verify_packet.py \
  frontier/campaigns/2026-10-14/arithmetic-r162bo-proof-r1 \
  --final SHA256:BYTES:FULL_MODE --manifest SHA256:BYTES:FULL_MODE \
  --report SHA256:BYTES:FULL_MODE
Use the detached actual anchors supplied in the final handoff, not values learned
from an unauthenticated manifest. The verifier traverses only this review root and
follows no source/original bindings.
