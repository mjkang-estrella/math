# W5 contribution and eligibility review, round 1

Independent operation-level contribution and eligibility review of the W5 packet (`fresh-analytic-discovery-r25`, manifest sha256 `10665dc8…c606`, scope `bda045b9…9f03`, candidate `2fd9649a…147d`). Myeongjin Kang, no affiliation. Original prose CC BY 4.0; code MIT.

**Verdict: TECHNICAL.** See `review.md`. Read extents and rights are in `read-limits-and-provenance.md`; exact input hashes are in `input-hashes.json`.

This is not a proof verdict and not a worldwide priority claim. There is no count change, staging, commit or publication. `private/` holds third-party reading copies: do not commit or redistribute them.

Verify with the manifest SHA-256 supplied outside this directory:

    python3 -I verify.py --anchor EXTERNAL_SHA256 [--repo /path/to/openai-proof-research]

The verifier is read-only. It checks exact membership, every payload hash, pinned source Git blobs, primary bytes and the exact coefficient check. With `--repo` it also checks blobs against the complete preprint tree and confirms the author packet bytes are unchanged.
