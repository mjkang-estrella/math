# R162BX detached local report

Disposition: PREFREEZE/no nominee. No theorem or diagnostic frozen; no mathematical gates or campaign increment. Parent alone adopts gates/count.

FINAL_SHA256 8f23d8865072880454909f2a1705eeb72d9c9c6a6335efe8700436ed758fdda3
MANIFEST_SHA256 83fef0b9c9dbbc9b0d37f73dfe6dcba947143046c91281e8ea0a9048268d0fe7

The REPORT SHA256 is detached in the final handoff; it cannot contain its own digest. REPORT.md and MANIFEST.json are the two files outside the payload manifest, inside the exclusive root. All other files and all directories are enumerated with sorted unique safe paths and full st_mode. The root full mode is included. The report and manifest must themselves be regular mode100644 files. Exact whole-root membership equals the payload membership plus these two names.

Payload files: 235; whole-root files: 237; directories including root: 21; payload bytes: 8403967.

The SAME verify_packet / verify_inventory logic was run on these exact final byte strings before their one-time creation. Tiny copied controls rejected a same-length byte change, extra membership and altered full mode; the fixture was restored and matched before sealing. Pinned60-blob bindings,8 primary PDF bindings and the5 exact completed originals/copies are checked. Initial completed-file bindings recorded permission bits; full modes were bound at a disclosed later comparison and are checked from that comparison onward. No initial full-mode claim is backdated.

Read-only verification from the mandated project workdir:

python frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bx/verify.py --final 8f23d8865072880454909f2a1705eeb72d9c9c6a6335efe8700436ed758fdda3 --manifest 83fef0b9c9dbbc9b0d37f73dfe6dcba947143046c91281e8ea0a9048268d0fe7 --report REPORT_DETACHED_SHA256

Replace REPORT_DETACHED_SHA256 with the exact detached anchor from the handoff. The verifier does not fetch, write, amend or repair any sealed file. Artifact checks do not establish mathematical correctness, novelty, contribution, acceptance, priority or exhaustive isolation.

Protected source/primary/completed bodies and their named metadata remain local/private. See private/READING-LIMITS.md for exact semantic extents, versions, late reads, access/extraction/truncation limits and history0. No sealed payload is to be changed to satisfy a verifier.
