# Failures log (candid)

1. **Uninitialized trajectory tail (first `analyze`)**: g[1..c-1] were left as zeros
   before the state loop, corrupting preperiods and cycle detection. Detected by the
   independent crosscheck ("trajectory mismatch"); fixed by computing g[1..c-1] with
   the literal mex rule first.
2. **Divisibility direction inversion**: check wrote `m % p == 0` (p | m) instead of
   `p % m == 0` (m | p), which would have produced false "violations" (e.g. S=(1,3,5));
   caught by hand-checking (1,3,5) and (2,3,4) against theory; fixed.
3. **Valid-region truncation**: `analyze` returned g valid only up to the cycle-detection
   index; the preperiod scan and crosscheck compared beyond it (garbage zeros), giving
   wrong preperiods (e.g. 10 instead of 0 for (2,3,4)). Fixed by bounding all
   post-processing to `valid_upto` and returning it explicitly.
4. **Invalid list comprehension in the solution enumerator** (`[f(x), g(x), h(x) for x...]`)
   — syntax error; never ran. Fixed to tuple comprehension.
5. **Wrong constraint-scheduling key in DFS**: constraint x was scheduled at
   max(residues) without including x itself, so x was checked while unassigned
   (S=(1,3,5) on Z_2 incorrectly reported zero solutions). Fixed to
   max(residues[x] + [x]); revalidated against the known game cycle.
6. **Guard kill on first enumerator run**: O(L)-per-node full recheck made the DFS miss
   the 512MiB/230s caps with no output. Rewritten with O(1) per-node checks
   (constraints checked exactly when they become assignable), an immediate
   G(x)!=G(x-s) coloring prune, node cap, and streaming per-L output.
7. **Accidental html_render call** at session start (empty placeholder page); no effect
   on lane files or results.
8. No 403/429/robots/challenge events; no retries; no access-control bypasses.
