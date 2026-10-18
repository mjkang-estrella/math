# T250P author candidate packet

Full frozen target: scope250p.md. Completed author proof: candidate250p.md. Operation-level contribution comparison: source-and-credit.md. Reading and finite-check limits: reading-limits.md. No acceptance or independent gate is asserted.

Run from this directory, supplying the manifest SHA256 received externally from the author/parent:

    python3 verify.py EXTERNAL_MANIFEST_SHA256
    python3 diagnostics.py
    python3 control-tests.py EXTERNAL_MANIFEST_SHA256

The verifier never reseals. It rejects extra files and empty directories, symlink ancestry, nonregular entries, hardlinks, nested manifest.json and internally resealed changes with the old external anchor. It also authenticates the 30 pinned non-PDF bodies, five primary HTML/text pairs and exact parent receipt copies. It does not fetch external sources; the parent must compare source-family identities against the canonical complete tree, not a truncated listing.

controls.json records an earlier baseline control run, whose exact manifest is preserved as provenance/baseline-inventory.json. The final manifest additionally covers that receipt and the control report. Re-running controls writes only disposable scratch, removes it, and prints results; redirect output outside the packet if retaining a replay. Do not redirect into the sealed directory. diagnostics.py prints deterministic finite support checks and does not implement the entire group algorithm.

private/ contains third-party bodies for local checking only and is ignored. Do not publish or commit those bodies. Original prose is by Myeongjin Kang, no affiliation, CC BY4.0; original scripts MIT. Formal interfaces are plans, not implemented verification. Earlier work notes preserve intermediate uncertainty; the final candidate states the complete author proof claim.
