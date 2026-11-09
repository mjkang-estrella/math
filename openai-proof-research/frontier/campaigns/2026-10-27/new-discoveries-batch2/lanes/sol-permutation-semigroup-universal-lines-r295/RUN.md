# Guarded replay

Run in this lane, always prefixing the following commands with environment settings OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1:

    python ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python ap_classifier.py
    python ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python check_math.py
    python ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python verify.py

The last command is the separate final verifier; it checks the immutable manifest, originals/copies and witness regressions. It does not prove the universal theorem by finite testing or rerun the arrangement. The universal proof is in discovery.md and explicitly depends on the frozen r294 exact ratio-order certificate. No cap raises, third-party children, Lean or manuscript tools are used.

freeze.py and finalize.py record the initial custody/final manifest operations; do not rerun them over an immutable handoff. finalize excludes manifest.json and verification-receipt.json from the manifest; verify writes only the receipt. scout.py records live HTTP access and text hashes; no retry path exists. Source hashes are checked before inspection and after work.
