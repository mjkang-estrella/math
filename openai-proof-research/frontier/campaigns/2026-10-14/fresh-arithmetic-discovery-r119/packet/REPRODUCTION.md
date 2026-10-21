# Read-only integrity replay

Use Python3, with no installation. All commands must use the actual project root as workdir. The root's three detached anchors are supplied in the final handoff; do not replace them with hashes guessed from an unauthenticated manifest.

    python -B frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r119/packet/code/verify.py \
      --root frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r119 \
      --final-sha256 FINAL_SHA256_FROM_HANDOFF \
      --manifest-sha256 MANIFEST_SHA256_FROM_HANDOFF \
      --report-sha256 REPORT_SHA256_FROM_HANDOFF

The verifier reads only. It checks all payload bytes, exact files and directories, and all three outside envelopes against independent supplied anchors. It rejects symlinks,nonregular files and hardlinks; it does not authenticate file modes. It does not establish a theorem, contribution rating or peer-isolation certificate.

packet/control-results.json describes a separate THREE-PAYLOAD copied selection with its own manifest and its own three anchors. That selection never claims to be a full copy of the research root. Do not use its manifest or anchors for the actual root. Private upstream/primary/history/navigation/extract/render and copied fixtures remain local under their original rights. Nothing is uploaded or published.
