# Progress / reproducibility

29October2026, solo GPT-6.1 Sol high. Read campaign handoff and original rejection notes. Screened four sources, corrected two local re-screen leads and the exact public AllSplits duplicate before any nomination. All four excluded; no fresh full target survives.

Run each Python helper serially under the unchanged absolute guard:

    python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-fresh-source-discovery-r117/checks.py

checks.py is deterministic, stdlib-only, exact arithmetic, no network, with permutation-expansion versus subset-DP and a non-TNN negative control. The source URL fetch helper is bounded8MB/25s each, stops403/429, records bytes and exact UTC. target_audit.py has a stricter185s internal bound than the guard and records partial coverage honestly. No cap was increased after an incomplete run. Audit metadata is not a mathematical source.

No independent-clearance request is justified for any screened item. No Lean/paper. Potential future inverse-Z work would still need an all-matroid mechanism and fresh source/current-literature clearance, but is expressly not fresh r117 work. End state and hash verification are in final-receipt.json and finalmanifest.jsonl.
