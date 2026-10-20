# Reproduction

From the project root `openai-proof-research/`:

    R=frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r99
    python3 -B $R/packet/code/verify.py --root $R --tree sources/preprints-tree.json \
        --final-sha256 <detached FINAL anchor> --report-sha256 <detached REPORT anchor>
    python3 -B $R/packet/code/identity_check.py

`verify.py` is read-only (audit hook denies writes, renames, process spawns
and sockets) and checks file identity, registers, the pinned tree and the
frozen-scope bytes. `controls.py` replays the verifier on transient mutated
copies inside the root and writes `integrity-results.json` at the root.
`identity_check.py` evaluates the Lemma 4 identities at random points over
several fields and checks the Step 5 index conditions; it is evidence, not a
proof. None of these is a mathematical gate.

`fetch_pinned.py` re-fetches a pinned file from raw GitHub, checks its Git
blob and size against `sources/preprints-tree.json`, and logs a receipt; as
packaged it writes under the root `private/upstream/` and `work/`.
