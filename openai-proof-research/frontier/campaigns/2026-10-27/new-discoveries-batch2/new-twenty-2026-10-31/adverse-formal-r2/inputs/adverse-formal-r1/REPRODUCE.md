# Reproducing the incomplete packet

This packet cannot certify a mathematical refutation. Do not interpret a
successful rational check as a formal replay. The expected replay exit is 3
(HOLD). Full formal verification has not been implemented.

Extract adverse-381433-incomplete-source.zip into a NEW empty directory
inside the assigned lane. The zip has no oleans or Lean proof files. Then run:

```
LEAN_BIN=/path/to/lean LEAN_PACKAGES=/path/to/packages python3 -I replay.py
python3 -I scripts/check_certificate.py inputs/outputs/latin36-certificate.json
```

For the fresh replay receipt, the driver was invoked from a fresh extraction
with an environment containing only PATH, LANG, LEAN_BIN, LEAN_PACKAGES,
MALLOC_ARENA_MAX=2 and TMPDIR inside the lane. It refuses an existing olean
before doing anything else. It verifies the listed source hashes, then exits
3 because formal/ has no .lean files. No Lean or leanchecker runs occur.
The variables are interface placeholders, not evidence of toolchain use.

Intended future pins from TASK.txt: Lean 4.34.1, commit
5045d0056413266e57c625dcd7c365b10e377c52; mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612. A completed future driver must add
resource-monitored strict -j1 -DwarningAsError=true builds, independent
leanchecker execution, all-declaration body/type/axiom/unsafe/partial audit,
and formal negative controls before it can report PASS. None is present here.

Receipts: receipts/input-hashes.json, receipts/input-hashes-after.json,
receipts/packet.json and receipts/fresh-replay.json. Logs:
logs/exact-certificate-check.json, logs/negative-controls.json,
logs/fresh-replay.log and logs/audit.json. Binary source bodies excluded from
the zip remain in sources/ and are bound by download receipts.
