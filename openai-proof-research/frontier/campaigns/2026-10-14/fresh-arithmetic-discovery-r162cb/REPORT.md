# R162CB detached sealing report

The payload consists of 59 sorted unique file records and 21 directories including the root. MANIFEST.json and this REPORT.md are detached from that payload, giving 61 whole-root files. The final read-only verifier logic is used unchanged for preflight and post-seal verification. The packet becomes sealed in place only when that preflight returns MATCH; no subsequent file mutation is authorized by this report.

FINAL.md SHA256: 3749989702acf47470f1d7baeb1a85549aed8887cff161d6180546a3884ae820

MANIFEST.json SHA256: 4e698a7e61eff0727f38936c1ece44d08e0aea277b12017fcd308e264698844a

The REPORT.md SHA256 is detached again in the author handoff, avoiding a circular self-hash. All three anchors are mandatory arguments to verify.py. The frozen statement SHA256 is b69dd8585357682a27bb327cfcd789ebab99c828c00f928ec79322e1b525f53a.

The verifier checks exact safe membership, sorted uniqueness, byte lengths, SHA256, FULL filesystem modes, all five completed original/copy pairs, bounded direct-input copies, complete-tree metadata, 20 pinned source blobs and six trees, and six primary PDF acquisition bindings. It is read-only and performs no network call. Run it from /home/mj-kang/Documents/Dev/math/openai-proof-research, with --root frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cb and the explicit --final-sha256, --manifest-sha256, --report-sha256 arguments.

Before sealing, the tiny own-statement copied fixture matched, rejected byte/length mutation, full-mode mutation, extra membership, duplicate records and an unsafe path, and matched after restoration. These controls are recorded in private/controls/results.json. They are artifact checks, not mathematical gates. No correctness or contribution grade, acceptance or count is assigned. The theorem and complete author proof require the parent's independent reviews.
