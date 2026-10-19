# r109: full author proof, independent gates unset

Start with [status](public/status.md), the unchanged [scope](public/scope.md), [complete proof](public/proof.md), and [operation comparison](public/comparison.md). The [screening inventory](public/inventory.md) and [reading limits](public/reading.md) document the bounded search. No campaign credit is claimed.

`public/` contains original prose and finite control code. `private/` contains upstream/third-party evidence and is not a public manuscript or redistribution bundle. The top-level receipts and manifest record provenance and exact membership. No publication operation is authorized or performed.

Read-only replay, from this directory:

```sh
python -B verify.py --expected-sha256 HASH_FROM_DETACHED_HANDOFF
python -B public/checks.py
```

Supply the detached final manifest SHA256 from the parent handoff; never derive the trusted value from the same manifest being checked. `--repo-root /absolute/path/to/openai-proof-research` selects a relocated context. External context anchors are strict: subsequent edits to a shared ledger legitimately cause a context mismatch. The complete source tree and upstream pin are checked directly, not reconstructed from the truncated root-tree cache.

The verifier has no network access or file-writing operation. The checks print to stdout and use exact Python rational arithmetic. Neither program proves the theorem or supplies an independent review. The original scope hash is retained in `scope-freeze.json`; its historical status remains FROZEN_UNPROVED, whereas the final manifest records the later author-proof status.
