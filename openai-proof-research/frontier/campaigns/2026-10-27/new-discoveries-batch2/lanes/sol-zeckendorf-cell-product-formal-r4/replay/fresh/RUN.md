# Bounded strict replay

Run from this lane with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
PYTHONDONTWRITEBYTECODE=1. Every Python invocation must be under the absolute
helper_guard.py in sol-edge-irregulator-manuscript-packet-r1/packet.

`bash run.sh -o Literal.olean Literal.lean` compiles the first module. Repeat
serially for Terminal, Law, Cells, Product, then `bash run.sh Inventory.lean`
and `bash run.sh Audit.lean`. run.sh uses that guard and runner.py.

Lean is pinned at
/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean,
SHA256 e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550.
Packages are the nine immutable revisions in pins.json under the 2026-10-14
formal/.lake/packages directory; mathlib is d13f23b723b8a846827a245b89c10fc7d3f11612.

Helpers have fixed 512 MiB AS/group RSS, CPU210 and wall230. Lean is the
explicitly authorized separate compiler process, serial j1, M2700, group RSS
2800 MiB, CPU210, wall230, warningAsError=true and autoImplicit=false. The
runner preserves every attempt's source, stdout/stderr, exit, and measurements.
No limit is adaptively raised after failure.

For packaging, invoke guarded `python certify.py pack`, then separately guarded
`python certify.py replay`. Replay extracts source-only.zip into replay/fresh,
checks its bindings, recompiles all modules from source, reruns both exhaustive
audits and removes owned compiled objects throughout this lane. The helper
itself does not need to compile or execute any archived predecessor sources.

Finally invoke guarded `python certify.py manifest`, followed by a SEPARATE
guarded `python certify.py verify`. MANIFEST.json excludes itself and the final
verification-receipt.json. No writes should follow final verification.
