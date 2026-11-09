# Reproduction and trust boundaries

Run from this dossier directory. No network, Lean, lake, leanchecker, SAT or ILP
solver is needed. Python uses real script paths and isolated mode. Do not run
historical scripts in evidence/. Every heavy command runs sequentially.

Verify original payload before modifying any generated files:
    MALLOC_ARENA_MAX=2 python3 -I scripts/capped.py verify-new python3 -I scripts/verify_payload.py

Recompute both obstructions and all four rational witnesses:
    MALLOC_ARENA_MAX=2 python3 -I scripts/capped.py recompute-new python3 -I scripts/recompute.py

Rebuild and render the PDF, using installed groff/eqn/tbl, Ghostscript and Poppler:
    MALLOC_ARENA_MAX=2 python3 -I scripts/capped.py pdf-new python3 -I scripts/build_pdf.py

Source: paper.ms, scripts/layout.tmac and scripts/build_pdf.py. Reportlab was
unavailable, so existing local typesetting tools were used without installation.
The failed first build and subsequent corrections remain in logs/. The final
CW-font alias deprecation warning is harmless. Reruns change receipts and PDF
timestamps; mathematical outputs are deterministic, but byte-identical PDF
generation across environments is not promised. Use fresh cap-log names.

Portable packet safety/integrity recheck, without Lean:
    MALLOC_ARENA_MAX=2 python3 -I scripts/capped.py packet-new python3 -I scripts/verify_packet.py

Do not rerun prepare.py on a moved dossier: it acquires original sibling lanes
and resets the initial integrity snapshot. All its resulting evidence is included.

The wrapper waits for each group with at most two CPUs, CPU 120 s, wall 140 s,
sampled process-group RSS 6 GiB and MALLOC_ARENA_MAX=2. It also bounds address
space to 12 GiB and sets thread limits and lane-local temporary/cache paths.
No shell background job is used.

Historical formal checks use Lean 4.34.1 and read-only mathlib cache revision
d13f23b723b8a846827a245b89c10fc7d3f11612. The packet has six source/readme
members, not a complete vendored compiler or mathlib distribution. Historical
replay scripts depend on the original environment. A portable offline upstream
rebuild is not claimed. No formal checker was executed during manuscript work.

Complete frozen discovery/review/retention lanes are under evidence/, including
historical non-target computations that were not executed here. Original absolute
paths in receipts are preserved as provenance. Parent-final JSON receipts are
copied separately if present. Exact raw MathDB line: 341850.jsonl. Its file hash
includes its terminal newline and agrees with the recorded provenance.

MANIFEST.sha256 binds the payload, excluding itself, ZIPs, DELIVERABLES.sha256,
archive-verification receipt and the live packaging log/receipt. full-dossier.zip
contains that payload plus its manifest. paper-source.zip contains source, layout,
builder and this guide. lean-packet.zip is the byte-identical original.
DELIVERABLES.sha256 binds all ZIPs, the payload manifest and archive receipt,
avoiding circular self-hashes. Packaging execution logs remain outside their own
archive; all frozen evidence logs remain inside.
