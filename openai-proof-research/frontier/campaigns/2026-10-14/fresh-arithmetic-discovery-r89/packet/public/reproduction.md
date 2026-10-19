# Read-only integrity reproduction

From the repository root, use Python3 with bytecode writes disabled:

```
python -B frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r89/verify.py \
  --root frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r89 \
  --tree sources/preprints-tree.json \
  --finalhash DETACHED_FINAL_SHA256 \
  --reporthash DETACHED_REPORT_SHA256
```

Obtain the two detached hashes from the handoff/final response outside packet/. The verifier will not choose its own trust anchor from an in-packet hash. It authenticates FINAL, the outside REPORT, the exact manifest, its own code and control runner, every payload/directory, all canonical acquisition records against the complete external tree, retained source Git blobs, primary pairs and historical copies. It performs no network requests and its audit hook forbids writes, subprocesses and networking. Python/runtime and the supplied trusted hash are part of the verification environment.

The original control runner creates and deletes only disposable copies under the owned directory. `control-results.json` records its final-seal cases and before/after hashes of the original inputs. New-anchor controls deliberately authenticate altered copied metadata before testing deeper canonical/URL checks; they do not change original anchors. The direct audit-denial cases test the same verifier's hook. No finite mathematical tests are part of this archive.

An integrity success proves neither the mathematics nor reading completeness, originality, eligibility or contribution. The packet is an unfrozen research archive with no nominee. Third-party and author-private evidence remains in private/ and is not licensed for public redistribution by this note.
