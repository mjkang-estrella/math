# r75 handoff

Read research.md and reading-limits.md together. No target was frozen and no nominee is submitted. The parent owns all mathematical and contribution gates.

The exact packet is bound by manifest.json. Its SHA256 must be supplied from the separate handoff, never trusted from within this packet:

    python -B public/verify.py --packet /absolute/path/to/packet --finalhash EXTERNALLY_SUPPLIED_MANIFEST_SHA256

The verifier is read-only. It checks exact inventory, hashes, the pin, source Git blobs and primary receipts. It requires a detached finalhash, rejects symlinks/hardlinks and does not consult an internal trust anchor. Context receipts identify external project files; their bodies are not bundled and are not reread by this verifier. Copied negative controls and their report live outside the sealed packet. Integrity success is not a mathematical gate.

Rights: public/ contains newly authored research notes and code only; no third-party license is changed or inferred. private/ contains pinned upstream/third-party bodies and bounded search excerpts retained for local evidence under their original rights. This packet is not a publication or release artifact. Any later distribution requires preserving this separation and the applicable rights.
