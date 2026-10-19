# Integrity and finite diagnostic

Use a separately trusted verifier and detached anchors. A copied packet cannot authenticate its own verifier merely by including it in a manifest. `../FINAL-ANCHORS.json` relative to the packet root is outside the packet; the final handoff also reports its two hashes. Obtain the expected hashes from that external handoff, not by recomputing and trusting a possibly changed manifest.

From the assigned directory, substitute the externally supplied final values:

```sh
python -B packet/public/verify.py --packet packet --expected-manifest MANIFEST_SHA256 --expected-report REPORT_SHA256
python -B packet/public/run_controls.py --packet packet --work work --expected-manifest MANIFEST_SHA256 --expected-report REPORT_SHA256
python -B packet/public/finite_checks.py
```

The verifier requires both hash arguments. It rejects altered/missing/extra files, extra directories, symlinks, hardlinks, altered manifests, and resealed payloads against the original detached anchor. It checks all selected source blobs and successful primary PDF/text identities. It does not fetch the repository, replay parsing of the entire tree, or verify mathematical statements. The full-tree identity is a sealed receipt of the creation-time parse, while selected tree entries are retained for per-file checks.

The controls use one temporary copy at a time under `work/`, delete each copy afterwards, invoke the original verifier with the original detached anchor, and compare original packet digests before and after. They do not mutate the original. The missing-anchor case must fail argument parsing; a fresh locally recomputed anchor must not be substituted for the final one.

The finite diagnostic enumerates 1,001 four-item multisets of the eleven collapsed subclass types and checks exactly four zero-primary patterns. It checks no geometric labels, arbitrary graph, asymptotic bound, or proof-completeness condition. Its output is not a mathematical gate.

`FINAL-ANCHORS.json`, `final-verification.json`, and `final-controls.json` live outside `packet/`, avoiding self-referential manifest construction. There is no frozen-target file because this round never froze a target. The public notes retain all feasibility scope and missing-step disclosures.
