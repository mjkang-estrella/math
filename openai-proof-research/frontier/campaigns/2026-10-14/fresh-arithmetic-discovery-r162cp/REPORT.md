# Detached seal report — R162CP

Author-proof packet, sealed once at 2026-10-25T21:29:11.207948+00:00.
The report is outside the manifest payload but inside the exclusive authorized root.
No independent mathematical review, contribution grade, acceptance or count is asserted.

Same-logic preflight MATCH: 66 payload files, 9372207 payload bytes,
13 directories including root. The complete root has
68 files after adding MANIFEST.json and this REPORT.md.

FINAL.md SHA256: 2f791c7cd05535ae785f24de83854dcd3e6a453f6548ba1610dc52ba77f6cffb
MANIFEST.json SHA256: 940a69a40a640e675e676a4decca6f3b8f4d6c07019dce49c4e8036c55342d5b
STATEMENT.md SHA256: ebbecfde0342e866f1401764980ccaf1f3f0c08bc1aea5269e217021774594c9
PROOF.md SHA256: 7331535f72a9c9dbab2da0396af34c78eb0a1065afb5e96d4cfc618a22a052b6
REPORT.md SHA256 is supplied externally; a self-referential report hash is not embedded here.

MANIFEST.json records sorted unique safe exact payload paths, byte lengths, SHA256 and FULL
st_mode values; directories, including root, also have FULL modes. It omits only the two
root anchor files MANIFEST.json and REPORT.md; FINAL.md is a payload and also detached-anchored.
The expected FULL modes of the two anchor files are33188 and are checked explicitly.

The read-only verifier checks exact whole-root membership, lengths, hashes and modes; the
unchanged frozen statement; the seven literal direct original/copy bindings (including exactly
the five completed exceptions); ONLY the authorized acceptance/catalogue byte windows; the
complete authorized preprints-tree metadata anchor and exact15-entry source selection; all10
source Git blobs and all5 Git trees at the stipulated pin; and retained primary PDF bindings.
It never hashes or decodes the whole acceptance journal or catalogue, traverses foreign roots,
or executes a source mathematical construction. All originals/copies and their recorded FULL
modes matched the preflight. Those initial bindings are observations at copy time, not an earlier
liveness or isolation certificate.

Tiny copied controls used the SAME verify/check_material functions: exact positive packet,
three wrong detached anchors, copied-payload tampering, a copied FULL-mode change, and restored
positive packet. Results are in private/controls/RESULTS.json. They are artifact checks only.
The author rational controls on two finite complexes are also not mathematical gates.

Run from /home/mj-kang/Documents/Dev/math/openai-proof-research:

python -B frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cp/verify_packet.py --root frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cp --project . --final-sha256 2f791c7cd05535ae785f24de83854dcd3e6a453f6548ba1610dc52ba77f6cffb --manifest-sha256 940a69a40a640e675e676a4decca6f3b8f4d6c07019dce49c4e8036c55342d5b --report-sha256 THE_EXTERNALLY_SUPPLIED_REPORT_SHA256

All three explicit anchors are mandatory. The verifier itself performs no writes. The -B option
prevents Python cache creation. No file in this packet is edited after this one seal; read-only
by workflow, with no chmod that would change sealed modes. The final postseal verification result
and all three detached hashes are returned through the tool output and final handoff, not by
rewriting a sealed log. Parent alone adopts any later reviews, gates or count.
