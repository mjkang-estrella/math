# Source-only replay

Use the already installed pinned dependencies in `pins.json`. From the workspace root, invoke the unchanged required helper guard, passing Python, this lane's `replay.py`, `source-only.zip`, and a new destination within this assigned lane:

```sh
python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-factorial-product-source-formal-r1/replay.py openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-factorial-product-source-formal-r1/source-only.zip openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-factorial-product-source-formal-r1/replay-new
```

Do not reuse an existing destination. Replay itself serially invokes the authorized Lean guard. Expected: empty `logs/FactorialProduct.log`, exhaustive `FullAudit.log`, and `replay-receipt.json` status `LITERAL_GAMMA_SOURCE_REFUTATION_PASS`. The packet contains no own compiled artifacts. Its archived failed compilelogs are explicitly named and are not the fresh successful mathematical compilelog.

Packaging is local and deterministic; under the same unchanged helper guard run `python package.py` from any cwd. It needs the completed local audit's `formal/dependencies.txt` and produces the source ZIP, manifest and archive receipt. It never modifies frozen originals.
