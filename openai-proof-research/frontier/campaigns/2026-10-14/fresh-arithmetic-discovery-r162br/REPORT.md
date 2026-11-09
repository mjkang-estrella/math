# R162BR detached artifact report

Author disposition: PREFREEZE/no nominee. No mathematical gate or campaign increment is assigned.

The read-only verifier's SAME final logic passed preflight with the final manifest/report bytes supplied in memory. Payload records were sorted and unique before sealing. The manifest covers 61 payload files, including FINAL.md, with 7857185 payload bytes. Exact final membership is 63 files and 8 directories including the root. The two detached files are this REPORT.md and private/MANIFEST.json, both inside the exclusive root and outside the manifest payload. Full file and directory modes are checked.

The preflight checks safe exact membership, byte lengths/SHA256, full modes, complete-tree/source Git bindings, ten acquired primary PDF/text bindings, and the five exact unchanged completed originals and copies. Tiny copied controls rejected wrong length/hash/mode, unsafe/duplicate/unsorted records and a changed byte; restoring that copy matched. These are artifact checks only.

The seal is created once after successful preflight. Post-seal verification and three wrong-anchor rejection controls are read-only; their actual terminal output and detached anchors accompany the handoff. No sealed payload, manifest or report is edited afterward.

FINAL SHA256: ae148cd50857d771d1ba83860bb61d86d18d2901fec85c735b206933e2b06e94
MANIFEST SHA256: d0196e136570518a5d5475f1a142f0fda83ebdf8700f6727ae0af412980be726

REPORT SHA256 is deliberately detached, not self-embedded. Invoke from the required project workdir with Python -B:

    python -B frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162br/private/verify.py --root /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162br --final-sha256 ae148cd50857d771d1ba83860bb61d86d18d2901fec85c735b206933e2b06e94 --manifest-sha256 d0196e136570518a5d5475f1a142f0fda83ebdf8700f6727ae0af412980be726 --report-sha256 <EXPLICIT_DETACHED_REPORT_SHA256>

No publication, release, formalization or independent mathematical review is implied. Detailed mathematical scope and reading limitations remain in the sealed packet.
