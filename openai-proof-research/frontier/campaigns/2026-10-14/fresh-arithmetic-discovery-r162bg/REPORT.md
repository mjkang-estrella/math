# r162bg outside-envelope artifact report

Disposition: PREFREEZE/no nominee. No mathematical gates, review grades, acceptance or campaign increment. All previous scopes/dispositions remain unchanged.

The packet was sealed once after preflighting the SAME read-only payload verifier logic. File and directory records were sorted and uniqueness checked before the manifest was written. No sealed file is to be edited to satisfy a verifier.

Payload: 65 exact files, 11780464 bytes, 11 directories including root. Whole root: 68 files, including this detached REPORT, private/MANIFEST.json and ANCHORS.json. All files are regular; symlinks and unsafe paths are rejected. Full file/directory modes are bound. The three detached control files have explicit full mode 33188.

The preflight matched 15 canonical Git/SHA256 bindings against the 19-entry family metadata; eleven primary PDF length/hash bindings; and all FIVE authorized completed originals/copies at their original bytes, lengths, SHA256 and full modes. The source PDF and downloaded/extracted primary files are not thereby proved semantically read; private/READING-LIMITS.md states actual extents.

Tiny copied controls: original fixture MATCH; wrong FINAL, MANIFEST and REPORT anchors each REJECT; changed copied payload bytes REJECT; changed copied payload mode REJECT; restored fixture MATCH. Controls modified only copied fixture material before the main seal. The final verifier is read-only and takes all three hashes as explicit command-line arguments. It does not derive trust from the in-packet anchor receipt.

FINAL SHA256: 1d3f7367820e6b47ca0e25e0af91c57c2fd692757f5c5b97e1300189bd456882
MANIFEST SHA256: 8360a137751cbbf81790cc9b860483ca618d937aa126ba6d63c9730d4fe58ee5
The REPORT's own detached SHA256 is supplied in ANCHORS.json and the external handoff; no self-hash is embedded here.

Read-only invocation from /home/mj-kang/Documents/Dev/math/openai-proof-research:
python frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bg/private/verify_packet.py --root frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bg --final-sha <external FINAL SHA256> --manifest-sha <external MANIFEST SHA256> --report-sha <external REPORT SHA256>

All mathematical work and all artifact material remain within the exclusive root. No optional history traversal or foreign live-task inspection was used. This report certifies artifact consistency only, not proof correctness, substantial contribution, source truth, exhaustive clearance or priority.
