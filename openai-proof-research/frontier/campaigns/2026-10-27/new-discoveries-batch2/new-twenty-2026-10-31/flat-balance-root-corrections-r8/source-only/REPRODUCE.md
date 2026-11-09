# MathDB 352972 - source-only certificate

Production source bytes are exactly the independently reviewed FlatBalance and FlatBalanceBridges modules. R1Link is a review-only source-formulation supplement; EnvAudit and controls are tooling, not production imports.

Pins: Lean 4.34.1 / commit 5045d0056413266e57c625dcd7c365b10e377c52; mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. See evidence/PINNED-TOOLCHAIN.json. Upstream prebuilt dependency libraries are trusted at those pins; this archive does not distribute or rebuild upstream. env.sh records the host's exact dependency paths. Adapt only those installation paths when using another host.

Extract into a new empty directory. The archive contains no oleans or legacy project build path. After verifying SOURCE-HASHES.json, run sequentially:

    bash check.sh FlatBalance
    bash check.sh FlatBalanceBridges
    bash checker.sh FlatBalance
    bash checker.sh FlatBalanceBridges
    bash audit.sh EnvAudit
    bash audit.sh R1Link
    bash audit.sh CtrlAuthorPos
    bash audit.sh ControlsIndPos

Each wrapper uses the supplied capped runner and strict -j1 -M3500 -DwarningAsError=true. The runner writes true-exit receipts and logs. ControlsIndNeg intentionally fails with six recorded false goals; its failure is a negative control, not a theorem certificate. This root reporting revision did not rerun Lean; the final Sol r7 execution and its unchanged manifest/receipts are the accepted independent evidence.

The editable manuscript is troff; build with groff -Tps -P-pa4 and ps2pdf -sPAPERSIZE=a4, then render every page with pdftoppm for visual QA. The corrected PDF is delivered separately. Historical process deviations, bounded prior-art limits and the distinction between endpoint dependencies and semantic translation lemmas remain explicit in the final review and root acceptance record. No publication or worldwide priority guarantee is claimed.
