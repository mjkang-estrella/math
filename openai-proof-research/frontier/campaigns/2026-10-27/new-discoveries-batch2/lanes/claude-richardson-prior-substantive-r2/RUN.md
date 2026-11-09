# Execution record

Every helper, Python, retrieval, edit-by-script, hash and pdftotext command ran as:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -I /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py <command>

The guard enforces AS/RSS 512 MiB, CPU 210 s and wall 230 s; the caps were not raised. Native bounded reads (cat/sed/grep/ls) and native file writes, the apply_patch equivalent, were used under the explicit exception.

Order of work:
1. bind.py bind/verify
2. reads
3. fetch.py retrievals (single attempt each)
4. abstracts.py decoding
5. bind_supplement.py
6. checker.py 16 24 (guard_exit 0, peak RSS ~11.4 MB, wall ~1.0 s; check-guard.txt)
7. bind_r216.py
8. review/provenance writes
9. make_manifest.py
10. verify_final.py, in a separate guarded invocation

No children, git, shared edits, browser, MathDB edits, external messages, posts, uploads, Lean or manuscript.
