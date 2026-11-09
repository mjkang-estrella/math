# Reproduction

Run from this lane directory. No dependency downloads are required.
The frozen input archive is frozen/round3a-source.zip, SHA256
76d35a8b86707ff534088ba93e877c7a05c221b3c0010d889bec958562371e5f.
The source-only output archive is chord-source.zip.

1. `scripts/rebuild.sh` is a resumable serial build and explicit per-module
   leanchecker, using modules.txt dependency order.
2. `scripts/capped.sh python3 -I scripts/package.py` writes the source-only
   archive and extracts into a new empty fresh-extraction directory. It refuses
   an existing extraction and validates safe archive paths.
3. In fresh-extraction run `scripts/rebuild.sh`. No compiled objects are copied.
4. In fresh-extraction, source scripts/env.sh, then run
   `scripts/capped.sh "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o build/ChordModel4Audit.olean src/ChordModel4Audit.lean`,
   followed by `scripts/capped.sh "$LEAN_BIN/leanchecker" ChordModel4Audit`.
5. In the lane root run `scripts/capped.sh python3 -I scripts/regression4.py`
   and `scripts/capped.sh python3 -I scripts/results.py`.

Every Lean, leanchecker and Python call goes through capped.sh: taskset 0,1,
CPU 120 seconds, wall 140 seconds, summed process-session RSS kill at 6 GiB,
MALLOC_ARENA_MAX=2, lane-local TMPDIR and cache. Every Lean call has -M3500.
The wrapper joins its watchdog before returning. Full unique logs are retained.

The audit inventories the entire import closure, including generated names,
and compares it to the audited set. Values are inspected with allowOpaque true.
Local and upstream metadata are reported separately. Upstream implementation
metadata are disclosed, not silently attributed to local declarations.

results.json is generated after replay; it is authoritative for measured status.
The packet is partial implementation and is not self-accepted.
