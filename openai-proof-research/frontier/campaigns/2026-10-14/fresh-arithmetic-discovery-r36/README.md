# T027O author candidate packet

Read candidate027o.md and frozen scope027o.md first, then source-and-credit.md and reading-limits.md. This is an author-side complete proof awaiting independent proof and contribution gates. No theorem is accepted or counted by this packet. Original prose: Myeongjin Kang, no affiliation, CC BY4; original scripts MIT. Third-party bodies and source-page renders are ignored under private/ and are not approved for Git or public release.

The final external manifest SHA256 is supplied to the parent outside this directory. From a complete unchanged private copy, verify with:

    python3 verify.py EXTERNAL_MANIFEST_SHA256

The verifier requires that external anchor; it never computes a replacement seal. It checks exact file and directory inventories, rejects all symlinks including root/ancestor aliases before resolving paths, rejects hardlinks and nonregular entries, rejects nested manifest.json, and authenticates source completeness and source/primary body identities.

Replay finite mathematical checks independently:

    python3 simple-band-diagnostic.py
    python3 ribbon-diagnostic.py

Their JSON outputs match the included reports. The old tangent-diagnostic.py/json concern the superseded word family and are historical algebra diagnostics, not the candidate's topology evidence.

The adversarial copied controls are reproducible with:

    python3 control-tests.py EXTERNAL_MANIFEST_SHA256

This creates disposable copies inside a temporary uniquely named subdirectory and removes them after completion. Do not redirect its output into the packet while verification runs, since exact inventory verification would rightly reject the extra file. controls.json records the pre-final baseline controls; provenance/baseline-inventory.json records the superseded baseline bytes under a non-manifest name. The final inventory includes both. The external final anchor is required for the final verifier.

No formal implementation, manuscript, release package, staging, commit or publication is part of this task. Parent author assistance is credited in source-and-credit.md and does not replace independent gates.
