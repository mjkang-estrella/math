# r162cj detached artifact report

PREFREEZE/no nominee. No mathematical gate or campaign increment.

This report is outside the manifest payload, but inside the exclusive r162cj root. Its SHA256 must be supplied independently together with the two anchors below. The verifier accepts explicit anchors, reads only, rejects unsafe or nonexact membership and unsorted/duplicate records, checks lengths/SHA256/FULL modes, and checks pinned Git blobs/trees and the five exact completed originals against their copies. The two tiny control copies are also compared with their source.

FINAL SHA256: f0379c11772de55c6447e823317c689b0736cffb40d71f8658e7fcd59b468a97
MANIFEST SHA256: 6fa4e4e130a939016f802da9e68a750d5111738e03e8ada0127a7c0d2b9d3ba2

57 payload files, 5076663 payload bytes; 9 directories including root. With MANIFEST.json and this REPORT.md: 59 files.

Preflight used the SAME final verify_packet logic, with the exact future MANIFEST and REPORT bytes supplied as virtual reserved files and their intended full regular-file modes. It matched before either reserved file was written. Records were sorted and unique. The packet was then written once; no sealed payload was changed to fit verification. The subsequent real-file read-only verification is reported in the task handoff/tool output rather than by mutating this sealed report.

Source authentication:27 blobs and4 trees. Protected source/primary/copy bodies and named metadata are private. Original/copy full modes were compared after initial reading, as disclosed; no initial timing claim is backdated. Tiny controls are not a mathematical correctness/contribution review. No optional original-history traversal occurred. The full mathematical and reading limitations remain in the payload.

Example invocation (substitute the three detached hashes provided at handoff):
python3 frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cj/verify.py --root frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cj --project /home/mj-kang/Documents/Dev/math/openai-proof-research --final-sha256 FINAL_HASH --manifest-sha256 MANIFEST_HASH --report-sha256 REPORT_HASH
