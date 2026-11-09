# Exact runnable checks

From /home/mj-kang/Documents/Dev/math, every Python invocation uses:

OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python <script>

Scripts in this lane: checks.py (110 finite prefixes and all265 full-projection extension graphs), periodic.py (16 exact stationary closures through length14), structural.py (252 two-by-two graph/regime cases, exact-cover dimensions,210 threshold residuals), report.py (reports/provenance/finalmanifest), verify.py (separate final verification).

work.py freeze snapshots the selected administrative/r220 sources; work.py history verifies immutable aliases without recopying history; work.py bodies retrieves nine versioned primary PDFs and extracts with pdftotext under the same guard. work.py fetch URL NAME retains bounded HTTP body/failure and pre-read hash. Do not rerun failed/denied endpoints just to reproduce a report. Replaying mathematical checks needs no network.

Fixed helper limits: address space512MiB, sampled aggregate process-group RSS512MiB, aggregate CPU210s, wall230s; no cap increases. Scripts terminate well below those limits in this run. No additional dependencies beyond Python standard library and pdftotext. Environment disables bytecode writes and caps BLAS/OpenMP threads at1. Manifest excludes finalmanifest.json and verification-receipt.json; verification runs AFTER final writes.
