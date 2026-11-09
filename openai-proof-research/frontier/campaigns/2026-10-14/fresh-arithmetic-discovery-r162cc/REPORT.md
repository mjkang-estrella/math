# r162cc detached artifact report

Disposition: PREFREEZE / no nominee. No mathematical gate or campaign increment.

The payload contains 56 regular files, 10 directories including the root, and 5949967 bytes. The complete root additionally contains this report and private/MANIFEST.json. The manifest records exact safe sorted unique paths, lengths, SHA256 and FULL lstat modes. Detached files have full mode 33188 (regular 0644). This REPORT is outside the manifest payload but remains inside the exclusive authorized root.

FINAL.md SHA256: `44598511ee764d523ba1d8bdc3c487113b0766e5d5986245513d417865466b66`

private/MANIFEST.json SHA256: `15f4938087c6879a8904447798261c2bb13b2d0c0d6451ecac0f18db0acacf51`

The REPORT.md SHA256 is detached and supplied by the final tool/chat handoff; it cannot be included in this file without a self-reference.

Verification uses private/verify.py with THREE explicitly supplied SHA256 anchors. It is read-only, rejects unsafe or unsorted/duplicate records, checks exact file/directory membership and full modes, reconstructs twelve pinned Git blobs and three trees, compares the five exact completed originals/copies, checks direct inputs using only the authorized bounded journal/catalogue windows, and checks the recorded primary acquisition/extract bindings. It does not inspect other task namespaces. The initial completed mode record stored permission bits only; the later full-mode binding and that timing limitation are preserved.

The candidate is sealed only after the SAME verify() logic used by the final CLI succeeds on these final files. No file is written by the sealer after that call. A subsequent explicit-anchor CLI invocation is a read-only confirmation. The tiny copied controls matched clean/restored bytes and rejected byte tampering, mode tampering, unsorted records and an unsafe path; their results are in private/controls/results.json. Artifact matching is not semantic proof reading, an independent mathematical review, or a contribution verdict.

Run from /home/mj-kang/Documents/Dev/math/openai-proof-research:

    PYTHONDONTWRITEBYTECODE=1 python frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cc/private/verify.py --root frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cc --project /home/mj-kang/Documents/Dev/math/openai-proof-research --final-sha256 44598511ee764d523ba1d8bdc3c487113b0766e5d5986245513d417865466b66 --manifest-sha256 15f4938087c6879a8904447798261c2bb13b2d0c0d6451ecac0f18db0acacf51 --report-sha256 REPORT_SHA256_FROM_DETACHED_HANDOFF

No downstream formal/manuscript/release work was performed. All research limitations and the precise unclosed operation are preserved in the private derivation and reading records.
