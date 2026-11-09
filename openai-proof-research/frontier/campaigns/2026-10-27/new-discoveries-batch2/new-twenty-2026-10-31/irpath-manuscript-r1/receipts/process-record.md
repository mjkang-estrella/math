# Process record (candid), lane irpath-manuscript-r1

## Compliance

- **Computation.** Every computation ran as one foreground command per tool call: `PYTHONDONTWRITEBYTECODE=1 bash -c 'ulimit -v 2000000; timeout 100 python3 -I SCRIPT ARGS'`. Runs were sequential, with no background or parallel processes and no loops of runs. The longest run took 24.6 s (an order-9 chunk).
- **Rendering.** `pdftoppm` (poppler) ran only as a child of `scripts/render.py` or `scripts/zoom.py`, inside the same cap.
- **Prohibited tools.** No Lean, lake, leanchecker or SAT/ILP binaries were run. There were no child agents, no git, no network and no TLS changes.
- **Writes.** Nothing was written outside this lane: no `/tmp`, no scratchpad. Python bytecode was suppressed in every script with `sys.dont_write_bytecode`, and the scripts import no local modules.
- **Inputs.** The frozen inputs were hash-bound before and after. All 560 files are unchanged (aggregate `a2046205…6655`; see `inputs-compare.json`).

## Deviations and notes

1. **Hashing started late.** Hash binding began after the initial read-only inspection of the inputs: `cat`/`sed`/`grep`/`ls` and a few small inline `python3 -I -c` reads of JSON and abs pages. These were not computations of printed numbers and wrote nothing. They were not wrapped in the ulimit/timeout cap.
2. **Unwrapped edit.** One source-text edit, which replaced three phrases in `paper/manuscript.src`, was done with an inline `python3 -I` heredoc without the cap. Later edits used the editor tool.
3. **Extra reads.** For provenance, I also read the `launch.json` of `expanded-corpus-r209`, `irpath-review-r1` and `irpath-formal-r1` (read-only). These are not in the hash-bound set.
4. **Trial builds.** Trial PDF builds were written to `tmp/b1`–`tmp/b3` inside the lane. They were visually inspected and then deleted. They are not part of the dossier.
5. **Rewritten output.** `outputs/graph-facts.json` was produced once and then regenerated, after an extended organisation was added to `recompute.py`. The first version was deleted by me (it was my own output). The values common to both runs were identical.
6. **Fonts.** The PDF embeds whole system TrueType fonts (Liberation, under the SIL OFL; Noto Sans Math, under the SIL OFL), so it is about 1.5 MB.
7. **Search independence.** The search is my own code. Its methodology (one-vertex extensions with canonical deduplication) is similar to the review lane's, which I read as text. Its canonical form (individualisation-refinement with twin pruning) and its IR enumeration (level-wise growth by heredity) are different implementations.
