# Review artifact reproduction and boundaries

Run from the repository root with Python 3:

```sh
python -B frontier/campaigns/2026-10-14/t195d93-proof-r1/public/code/verify.py --root frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r93 --tree sources/preprints-tree.json --final-sha256 362dfe44e0db3abcddf9ce56f2a86f496e1e9c47297bf85c6e922847e760c479
```

This is independent reviewer code, not a call to the author verifier. It only reads inputs and emits JSON. Source bodies and primary/history bodies are authenticated as retained evidence, not thereby certified true or fully read. All pinned OpenAI operative proofs are stipulated by the task; external facts are separate.

The controls runner is `public/code/controls.py`. Inspect it before execution. It derives the repository and author paths from its own exclusive directory, creates disposable copies in `private/disposable/`, removes them, checks full original snapshots, and writes `private/integrity.json`. It requires the existing baseline `private/original-before.json`. Re-running it overwrites that review receipt; it never modifies the author tree. The delivered receipt records the actual first completed run.

Controls test integrity, not mathematics. They do not test every Python audit denial, hostile runtime, concurrency race, exact author root inventory policy, or manifest-mode policy. No numerical mathematical test supports the correctness verdict.

The review seal's `MANIFEST.json` lists all payload files except itself and `FINAL.json`, including the outside `REPORT.md`, with byte hashes, modes and link counts, and all directories including root with modes. `FINAL.json` binds that manifest and the outside report. Its detached SHA256 is returned to the parent in the final response. The seal verifies bytes and membership; its own two seal-file modes are outside that payload policy. No later unlisted handoff file is needed.

Original review prose and metadata in `public/` and `REPORT.md` may be integrated by the parent under the repository workflow; original reviewer code is MIT. `private/` contains evidence receipts and preservation metadata, not publication material. Author/upstream/third-party works remain under their original rights. Temporary copied third-party bodies have been removed. No rights over those works are asserted.
