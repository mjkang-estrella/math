# B8C contribution round3

Read review.md for the independent SUBSTANTIAL assessment and its limits. Full scope and candidate are unchanged; the existing proof PASS is retained. No count or publication action is authorized by this packet.

non-sic-comparison.md proves why both explicit Hughston–Salamon non-SIC examples fail the sufficient covering condition. example_10_2_bounds.py independently checks the rational bounds using only Python's standard library; its output is retained. The exploratory optimization script is provenance only, not proof.

reading-and-provenance.md records actual reading extents and the distinction between directly reread bodies and retained prior comparisons. context-snapshot.json preserves mutable parent context without binding future edits. No external payload is copied here except those explicitly labeled context snapshots.

Integrity command, using the SHA256 of seal.json supplied in the reviewer's external final receipt:

    python -I -B verify.py --seal-sha256 EXTERNAL_SHA256

The verifier authenticates before parsing manifests, checks exact file/directory membership and hashes for this packet plus all three frozen dependencies, rejects unsafe paths/duplicates/symlinks/bytecode, and performs no writes or mathematical-code execution. Wrong anchors fail. Integrity is not mathematical truth or novelty.

Original prose: Myeongjin Kang, no affiliation, CC BY 4.0. Original code: MIT. Third-party source bodies stay private under their own rights.
