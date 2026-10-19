# Reproduction and scope

Read report.md, hard-count-feasibility.md, other-screens.md and reading-limits.md. This is a prefreeze research record with no nominee. The public code checks evidence identity only; it does not test universal mathematics.

From the repository root, run the following using the DETACHED hashes delivered by the research worker (not a hash read from inside the packet):

```bash
python -B frontier/campaigns/2026-10-14/fresh-analytic-discovery-r124/packet/public/verify.py \
  --root frontier/campaigns/2026-10-14/fresh-analytic-discovery-r124 \
  --finalhash <DETACHED_FINAL_SHA256> --reporthash <DETACHED_OUTSIDE_REPORT_SHA256> \
  --tree sources/preprints-tree.json
```

The full private evidence must be present. An originals-only public integration is not a portable full evidence bundle. The verifier performs no writes, repairs, downloads or subprocesses. It verifies the entire exact packet inventory before semantic metadata bindings. The seal authenticates the verifier code but is not a sandbox against executing malicious replacement code; inspect code before execution.

Copied controls:

```bash
python -B frontier/campaigns/2026-10-14/fresh-analytic-discovery-r124/packet/public/controls.py \
  --root frontier/campaigns/2026-10-14/fresh-analytic-discovery-r124 \
  --tree sources/preprints-tree.json \
  --output frontier/campaigns/2026-10-14/fresh-analytic-discovery-r124/new-controls-receipt.json
```

Use a new output filename. The runner creates and removes only its own disposable copies under the supplied root's scratch directory, compares the entire original root before writing the receipt, and never modifies the sealed originals. Most negative controls fail the enclosing identity check; they do not claim isolated branch coverage. No mathematical test is included. Parent may replay on a disposable copy of the whole author root and keep the actual author root read-only.
