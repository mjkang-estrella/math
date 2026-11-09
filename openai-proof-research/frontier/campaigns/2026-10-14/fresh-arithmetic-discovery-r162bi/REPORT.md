# r162bi detached artifact report

Disposition: PREFREEZE/no nominee. No theorem or diagnostic selected/frozen; no independent correctness/contribution review, self-grade, acceptance or count change. Campaign19/20 latestR041 remains parent-owned.

This report is OUTSIDE the manifest payload envelope but INSIDE the exclusive r162bi root. MANIFEST.json and REPORT.md are the only detached files; exact whole-root membership still checks both. Protected bodies and named metadata remain private/local under original rights. This packet is not a publication or release.

FINAL.md SHA256: d888edd006c1b27e2c23ea512f7788da5f7a1ee860371cd18d6a5d5dc9d1fa5b
MANIFEST.json SHA256: 89a1a5257b3522653575b27f20541da3e92b2f79864f7283f627977a4c3c653b
REPORT.md SHA256 is detached in the final handoff; it cannot be self-embedded.

Immediately before sealing, the SAME verify_payload logic used by the final verifier checked a sorted unique manifest in memory: 48 payload records, 6035154 payload bytes, 10 directories including root. The sealed whole root contains 50 regular files. The manifest binds full st_mode, exact names, byte lengths and SHA256 for every payload and exact directory modes; symlinks and nonregular entries are rejected. No sealed file is changed to fit verification.

Source checks reconstruct all selected Git blob and directory-tree hashes from the exact16 entries/12 blobs, check every pinned raw URL and selected byte length/SHA256, and preserve the source stipulated-truth boundary. The verifier does not reread/hash the shared journal, whole catalogue, or complete shared tree. Those initial bounded-access/full-tree-authentication facts are documented separately.

Five EXACT authorized completed originals and all five local copies match their initial full modes, hashes and lengths. Only those original file paths are reread; their containing namespaces are not traversed. Primary PDF identities/extraction sizes are bound, while actual semantic page extents and limits remain distinct in private/READING-LIMITS.md and private/primary/read-extents.json.

Tiny copied controls were exercised BEFORE this packet seal: all three incorrect detached anchors rejected; one changed copied payload rejected; restoring that copied payload gave MATCH under the same verifier. See private/CONTROL-RESULTS.json. There was no verifier failure on the main preflight and no mathematical gate follows from these controls. One separate finite multiplicity calculation is only a mathematical sanity example, not source algorithm execution.

To verify, run from /home/mj-kang/Documents/Dev/math/openai-proof-research and supply the explicit detached REPORT hash from the handoff:

    python -B frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bi/VERIFY.py frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bi --final d888edd006c1b27e2c23ea512f7788da5f7a1ee860371cd18d6a5d5dc9d1fa5b --manifest 89a1a5257b3522653575b27f20541da3e92b2f79864f7283f627977a4c3c653b --report <DETACHED_REPORT_SHA256>

The verifier is read-only. Its own bytes are part of the anchored manifest. A successful run reports MATCH with exact counts; failure raises an error rather than relaxing membership, ordering, mode or anchor checks. The final handoff reports the actual post-seal read-only run. No post-seal log file is added to the packet.

The complete retained derivation and strongest paid comparisons are in private/DERIVATIONS.md and private/SOURCE-INTERFACES.md. All canonical texts were read; primary/transitive reading was partial, with88 distinct pages across five papers, inaccessible BPR, late reads and recovered clipping disclosed. ZERO optional original-history traversal; no exhaustive-history, perfect-isolation, necessity, impossibility or worldwide-priority claim.
