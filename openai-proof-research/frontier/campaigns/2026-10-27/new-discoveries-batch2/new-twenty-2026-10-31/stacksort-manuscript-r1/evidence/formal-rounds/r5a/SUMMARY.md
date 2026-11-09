# Round 5A implementation — not acceptance

The requested theorem is proved unconditionally:

`StackSort.Cut5.commonCutCount_proved : StackSort.Round3.CommonCutCount`

Import `StackSortCut5Final`. The theorem covers every r and s in the frozen bound; it has no extra hypothesis. The stronger unclipped identity `commonCutCount_raw` holds for every M>0 and arbitrary tuple arities.

New modules prove exact support partitioning and concatenation for labelled tuples; a finite bijection from labelled remainder/final-block pieces to all reducible collisions, retaining every index; the binomial cardinality sum; and clipping compatibility with literalX, literalI and the exact correction false definition. No new axiom, numerical seed computation, or alternative count is used.

All 73 inherited round-4 modules are preserved byte for byte. Six new modules use only the StackSortCut5 namespace prefix, including the audit utility. Printed theorem axioms are exactly propext, Classical.choice and Quot.sound. The source-only packet and all replay/audit evidence are lane-local. See results.json for final measured validation totals, PROOF.md for the proof, and REPRODUCE.md for replay.

MaximumFinalCount was not worked on. It remains the exact frozen Prop for parallel lane 5B. The source-reading refutation is still conditional on that other obligation after the present theorem is supplied. The maximum-fibre endpoints remain inherited unconditional results. Root integrates and decides acceptance; no self-acceptance or credit is claimed.

No child agents, git, browser tabs, network, external messages, publication, upload, or shared ledger edits were used. Every Lean, leanchecker and Python process used the lane-local resource wrapper, with an RSS watchdog, two CPUs, CPU/wall limits, MALLOC_ARENA_MAX=2 and -M3500 on Lean. No background job is retained at handback.

Final validation passed: a fresh extracted strict serial build and explicit-module leanchecker for all 79 modules. The independent closure audit matches 349,391 declarations from 3,594 imported modules, including 935 local declarations and 93 new declarations. All local metadata flags are zero, and the endpoint/helper traversals use only the three permitted axioms. Peak recorded RSS was 2,930,044 KiB; no watchdog kill occurred. The archive SHA-256 is 31dfd87cce967ee5e90ce7eeb1399e0a5bbee391f9c8be5a060dcab0ce98cb7d. All 73 inherited hashes match before and after. Replay is complete and no background jobs remain.
