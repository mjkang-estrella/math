# Outside REPORT — S236 correctness review, round 1

The independent review recommends PASS for the entire unchanged frozen S236 statement and submitted proof, relative to the stipulated Source A/B truth. Parent adoption remains separate. No contribution verdict, acceptance, or count is assigned.

The complete reasoning and objections/resolutions are in REVIEW.md. Supporting calculations are in derivations.md; actual read extents, omissions, accidental exposures, late-reading timing, and formal/artifact limits are in READING-LIMITS.md. No essential mathematical obligation remains identified. Neither a weaker theorem nor a repaired scope has been certified.

The review packet was sealed once with its own explicit 26-file selection, selected bytes and modes. Root MANIFEST, this outside REPORT, ANCHORS, and SEAL-VERIFICATION are detached from the selection. The nested tiny-control manifest binds only its separate three-file fixture; it is not an inherited main-packet manifest. The inspected verifier is copied unchanged, SHA256 5787dedceac55f5b66b247bec0fb552497f2f4ff9ec8dd9c7426a4d4d0eacad8. Tiny controls accepted the intact/restored fixture and rejected byte changes, mode changes, and reduced selection. These are artifact checks, not mathematical gates.

After all semantic and visual reads and again after the selected review seal, all 106 exact admitted author files matched the baseline in byte length, SHA256, and mode. No author original was edited, chmodded, renamed, repaired, or resealed. No author directory traversal, peer/contribution review, parent assessment, public action, git/shared edit, nested agent, or downstream work occurred.

Detached anchors computed directly from bytes:

- FINAL.md: `3fe1e9d928ae563eda7c79920ccf12553e83b181e709df8f95fdf222e521bbce`
- MANIFEST.json: `1aa6fbbb962630d541f30c7fa58c695f847afb26a632d06d4082dd8ae6edab27`
- SELECTION.json: `50835dcc89068232a3deb8046d317c4121bd929ed87b3d5d5be7312c5c57f258`

This REPORT's own hash is in detached ANCHORS.json. SEAL-VERIFICATION.json records the read-only explicit-anchor verification and final original-file recheck. The verifier checks exactly the selected files, not directories or extra files.

From the actual project root, the read-only verification command is:

```sh
python -I -B frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/structural-r236-proof-r1/verify_packet.py --root frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/structural-r236-proof-r1 --manifest-sha256 1aa6fbbb962630d541f30c7fa58c695f847afb26a632d06d4082dd8ae6edab27 --final-sha256 3fe1e9d928ae563eda7c79920ccf12553e83b181e709df8f95fdf222e521bbce --selection SELECTION.json --selection-sha256 50835dcc89068232a3deb8046d317c4121bd929ed87b3d5d5be7312c5c57f258 --report-sha256 REPORT_SHA256_FROM_ANCHORS_JSON
```
