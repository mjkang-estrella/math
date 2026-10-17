# Reproduction

Authenticate the release with the externally delivered BUNDLE-MANIFEST and FINAL-GATE SHA256 values:

    python3 -B verify_bundle.py /path/to/release --manifest-sha256 HASH --gate-sha256 HASH

The command also accepts the ZIP directly. Exact payload identity is not a mathematical proof.

From frontier/campaigns/2026-10-14/seymour-s2-manuscript-r1/ in a clean extraction:

    python3 -B support/verify_package.py --manifest-sha256 61b1616c12d79c2512f2e572b4184ea5e70d3c9f3c5f6ee345a9cbab43c2d2cf
    python3 -B support/run_checks.py

Those commands need Python only and no private source/PDF files. Historical candidate/review scripts can include original-workspace authentication; the explicitly attributed manuscript adapter is the portable diagnostic entry point. The proof remains universal prose, not finite enumeration.

For Lean, copy the preserved seymour-s2-formal-r1/ to a writable working directory, follow its README.txt, and use its pinned lean-toolchain/lake-manifest.json. First provision the dependencies with lake exe cache get, then lake build. Alternatively pass explicit compiler and existing pinned dependency-cache paths to rebuild.py and mutations.py. These commands write fresh build logs in the working copy; do not run them inside an extraction that you want to keep byte-identical. Compiler pin is Lean4.34.1 commit5045d0056413266e57c625dcd7c365b10e377c52; mathlibd13f23b723b8a846827a245b89c10fc7d3f11612. The cache is an external dependency, not bundled.

The original PDF/source and its build instructions are preserved. Independent review logs document additional validation; see FINAL-GATE.json. No network publication action is part of any command above.
