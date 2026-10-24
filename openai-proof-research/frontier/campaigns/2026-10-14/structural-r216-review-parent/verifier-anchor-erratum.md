# Structural216 review-brief verifier anchor erratum

The parent transcribed one standalone SHA256 incorrectly in both original round-one review briefs and their composing script. The dispatched briefs remain unchanged as historical inputs.

- Supplied verifier SHA256: `feadd08d338035715987e81fdd1b142f82fe0a5db541b5b00e9afe4ec7d2fbc20`.
- Actual author `verify_packet.py` SHA256: `feadd08d338035715987e81fdd1b142f82fe0a5db541b95d28385aed7d2fbc20`.

The actual hash agrees with the original parent replay script, the original observed-root baseline and the committed author script at intake commit `77bca12f8ef0cd79d516a9eacd0a0375c86f5a5e`. The mistake arose when composing the review prompt, after that successful replay. The correctness reviewer identified it independently, inspected the actual script, and separately verified the selected author packet.

The four detached author FINAL/MANIFEST/SELECTION/REPORT anchors, the exact statement and proof hashes, and all author-root bytes and modes still match the original parent intake. No author input, review brief, sealed manifest or review result has been edited or resealed. The mistaken standalone hash is not represented as matching, and this correction is not a mathematical premise or grade.
