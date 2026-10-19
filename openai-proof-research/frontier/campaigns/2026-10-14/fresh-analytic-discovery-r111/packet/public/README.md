# T085E111 research archive

Start with research-report.md, then frozen-target.md, proof-attempt.md and operation-comparison.md. The target is unresolved and has no nominee. pre-freeze-screen.md and the original frozen target are preserved unchanged. reading-ledger.md limits every evidence claim.

This packet is a local research record, not a publication or a completed manuscript. Original prose/code is under public/. Private upstream and third-party reading copies are under private/, retain original rights and are not licensed or designated for redistribution by this packet.

From the campaign-owned directory:

    python -B packet/public/code/verify_packet.py --packet packet --expected-finalhash <externally trusted SHA256 of packet/manifest.json>
    python -B packet/public/code/check_algebra.py

The verifier writes nothing and requires the detached expected hash. Supply that value from the parent's handoff or an independently retained FINALHASH; a file inside packet is not a trust anchor. The verifier checks exact file and directory membership, ordinary file types, SHA256/size identities, frozen target/screen identities, raw Git blobs against selected complete-tree entries, and primary PDF/text receipts. It does not prove the mathematics, conduct contribution review or validate third-party truth.

To rerun deliberate corruptions on temporary copies only, use public/code/test_integrity_controls.py with --packet, --expected-finalhash and --scratch-parent set to this campaign-owned directory. It prints its receipt and removes its temporary copies. The original sealed packet is checked read-only before/after. The original run's controls receipt and report hash live outside packet to avoid a circular seal.
