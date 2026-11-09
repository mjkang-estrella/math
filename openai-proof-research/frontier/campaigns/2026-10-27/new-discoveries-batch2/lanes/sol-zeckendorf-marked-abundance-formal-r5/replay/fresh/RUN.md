# Reproduction

Work only in this lane. Export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
PYTHONDONTWRITEBYTECODE=1. Every Python invocation (including certify.py) runs
through the absolute helper_guard.py in sibling sol-edge-irregulator-manuscript-
packet-r1/packet. No unguarded helper invocation is authorized.

bash run.sh -o MODULE.olean MODULE.lean, serially in this order:
Literal Terminal Law Cells Product Prefix Marks Boards Injection Abundance.
Then bash run.sh Inventory.lean and bash run.sh Audit.lean.
Compiler: /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean
SHA256 e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550.
Packages: campaign 2026-10-14/formal/.lake/packages; nine revisions in pins.json,
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. All pins must stay unchanged.

Fixed helper caps AS/groupRSS512MiB CPU210 wall230. Explicitly authorized separate
Lean compiler caps j1 M2700 groupRSS2800MiB CPU210 wall230; warningAsError=true,
autoImplicit=false. No retry raises any cap. runner.py retains each attempted
source, log, exit status and measurements. Audit tools are metaprogram inspection
instrumentation; the ten mathematical source modules are checked exhaustively.

Through the guard, run python certify.py pack, then python certify.py replay.
The deterministic source-only ZIP is freshly extracted; all ten modules compile
serially and both name-aware origin/transitive audits run. Owned compiled objects
are removed. Then run guarded python certify.py manifest and, as a SEPARATE
invocation, guarded python certify.py verify. No writes after final verification.
The manifest excludes only the root MANIFEST.json and final verification receipt.
Receipts distinguish a passing replay from the PARTIAL scientific theorem status.
