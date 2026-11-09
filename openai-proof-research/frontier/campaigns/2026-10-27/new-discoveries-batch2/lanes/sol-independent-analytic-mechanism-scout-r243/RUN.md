# Bounded replay

From repository cwd, prefix every command with:

`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py`

Then `python <this-lane>/calculate.py`, `python <this-lane>/refine.py`. Both are exploratory, not proof checkers. Network re-fetch is unnecessary: frozen bytes suffice. work.py documents bounded retrieval/extraction/history procedures. Do not rerun build.py after manifest generation. Run `python <this-lane>/verify.py` as a separate final process; it verifies every manifest entry, primary/text hash pair, selected copied reports and immutable history references, then writes only receipt.json. No cap raises.
