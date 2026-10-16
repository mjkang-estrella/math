# Consequential commands and replay

All mutations were under the assigned r5 directory. Read-only searches of the
repository used rg, Python Path reads and scoped shell reads. No git mutation,
subagent, Lean build, manuscript build or external message/publication occurred.

Pinned retrieval: for each entry of retrieval-pinned.json, use its exact raw
GitHub URL, not a moving main branch. Primary retrievals and failures are in
retrieval-literature.json. Private PDF extraction used pdftotext -layout.

Original supporting calculation:

    python3 -B checks.py

The author initially captured its stdout in check-receipt.json, then froze it.
Normal verification authenticates that existing receipt BEFORE running code:

    python3 -B verify.py

The verifier uses only standard-library Python. It authenticates the seal's
inventories, all input/output bytes and sizes, complete file membership, then
replays checks.py and compares stdout byte-for-byte. It has no regeneration,
network, fix, update, acceptance or reseal mode. Use python -B to avoid bytecode
writes. Run in the original directory or an exact extracted copy.

Mutation tests used disposable copies INSIDE the owned directory, with the same
verifier/checker bytes. A baseline succeeded. Separate copies had candidate,
primary-source input, receipt or checker bytes altered, or an unlisted file
added; authentication rejected each before replay. Temporary copies were removed.
mutation-tests.json reports the outcomes and the provisional test-seal hash;
that seal describes the test fixture before the test report itself was added.
The final real inventories were created only after all original outputs existed.

A successful check authenticates/replays evidence only. It does not prove B,
certify A independently, assess worldwide priority or alter the campaign count.
