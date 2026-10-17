# TS132 independent contribution gate

The disposition is **SUBSTANTIAL** for the unchanged complete TS132 target, with bounded primary and historical coverage. This is not a full-proof verdict or a campaign acceptance. Read review.md and reading-and-limits.md together.

The complete author packet is copied byte-for-byte in inputs/author. It retains its manifest, source receipts, and private third-party inputs. Additional primary comparisons are in private/primary. These private bodies are evidence inputs, not files authorized for public redistribution.

Verify identity using the manifest SHA256 supplied separately by the reviewer:

```
python3 verify.py --anchor EXTERNALLY_SUPPLIED_SHA256
```

The verifier is self-contained, read-only, and offline. It checks exact file and directory membership, every payload hash, the externally anchored author packet and full target, all seven source Git blobs against the complete pinned catalogue, and five primary PDF receipts. It does not execute mathematical diagnostics or treat hashes as a proof of novelty. A wrong anchor must fail with nonzero exit. The verifier contains no assertions whose enforcement would disappear under Python optimization.

Original prose CC BY4.0; original code MIT. Candidate author Myeongjin Kang, no affiliation. Third-party rights unchanged. No publication, shared edit, staging, commit, or count change.
