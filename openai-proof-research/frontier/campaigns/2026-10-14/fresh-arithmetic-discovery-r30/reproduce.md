# Reproduction and seal contract

Run from any copied packet directory, using the exact two SHA256 anchors supplied in the parent's external record:

    python verify.py --expected-manifest MANIFEST_SHA256 --expected-verifier VERIFIER_SHA256
    python diagnostics.py
    python controls.py --expected-manifest MANIFEST_SHA256 --expected-verifier VERIFIER_SHA256

To authenticate the49 retrieved non-PDF source blobs, additionally pass `--source-tree /absolute/path/to/sources/preprints-tree.json` to verify.py. It rejects a truncated tree and requires complete non-PDF coverage of the four manuscript directories in the two receipt files. This checks identities, not theorem truth or full-body reading.

A public-only copy must remove the entire private directory and pass `--public-only`; no other missing/extra files or directories are allowed. Private primary/PDF/text/PNG bodies and pinned source bodies are not authorized for Git or public release. The original packet contains them solely for local provenance and author reading. There is no manuscript PDF or release authorization in this discovery packet.

Controls make disposable sequential copies under a temporary directory inside this owned packet, avoiding the system temporary-directory quota. The scratch directory is excluded only from copy creation, never from the verifier's inventory rules, and is removed on exit. Run the original verifier after controls finish. The manifest does not bless changes made by controls: the self-reseal adversary changes both a copied candidate and its manifest and must still fail the external hash. No function reseals the original packet. Verification assumes the filesystem is not concurrently mutated during a scan; no race-resistant hostile-filesystem security claim is made.

The code is adapted from the already-developed r29 strict verifier/control pattern. This infrastructure has no mathematical novelty claim. Scope/candidate changes after sealing require a new packet/version and new independent review as directed by the parent.
