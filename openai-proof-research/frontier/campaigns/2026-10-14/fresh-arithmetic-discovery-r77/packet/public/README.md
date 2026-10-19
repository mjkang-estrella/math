# r77 research packet

Read research.md and reading-limits.md together. No target was frozen; no nominee or gate/count decision is supplied. Public/ contains original research prose/code. Private/ contains the limited pinned source and primary evidence, under original rights.

From the r77 directory, run:

    python -B packet/public/verify.py --root . --finalhash DETACHED_FINAL_SHA256

Use the final hash reported outside the packet. The verifier never accepts a digest read from its own FINAL.json as the trust anchor. It authenticates the detached report and manifest, the exact packet membership, selected canonical Git blobs and primary-body hashes. It does not read live shared project files, execute third-party code, or test mathematics. Copied controls are recorded separately under integrity/; their hash is reported outside the packet to avoid a circular seal.
