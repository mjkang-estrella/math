# Reproduction

Use Lean 4.34.1 from the absolute binary directory in TASK.txt. Dependencies are the pinned read-only mathlib package cache at campaigns/2026-10-14/formal/.lake/packages (mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612). No network or lake update is used.

Extract chanlevine-round1-source.zip into a NEW empty directory inside this lane. The archive has only safe relative paths. Run:

```
python3 -I scripts/replay.py
```

To resume after an interruption, use `python3 -I scripts/replay.py --resume`. Successful module receipts are accepted only for the identical full Lean source manifest. Build outputs, logs, cache and temporary files are extraction-local. Sources are compiled serially in order Dynamics, Reduction, SourceSemantics, Cardinality, Endpoint, Controls, Audit. Each receives `-j1 -M3500 -DwarningAsError=true`, then leanchecker checks its compiled module. The runner prepends the pinned binary directory to PATH for leanchecker's subprocess.

cap.py limits affinity to CPUs 0 and 1, sets inherited CPU limit 120 seconds, kills the session after 140 seconds wall time or if summed session RSS exceeds 6 GiB, and sets no virtual-memory limit (mapped mathlib files require more virtual address space). MALLOC_ARENA_MAX is 2. Every process gets a unique log with resource measurements. No background job survives the synchronous runner.

Audit.lean inventories every declaration, including generated declarations, owned by the six local modules in the endpoint/control import closure. It rejects unsafe, partial, `_unsafe_rec`, implemented_by, extern and nonallowed transitive axioms. It prints the full conditional endpoint. replay.py independently traverses local source imports and checks equality with the audited module set and declaration row total. Upstream pinned mathlib and Lean are trusted dependencies; their entire tactic/compiler import environment is not claimed free of unsafe executable code. The audit checks all transitive logical axioms of every local declaration, not merely the named theorems.

Replay also runs three expected compilation failures and the exact Python SCC regression n = 3 through 8, m = 1 through 3. The distinct-gcd negative control combines independently computed row [26,24,24] with rejection of 26 = 24. Controls.lean proves the wrong weight convention fails and zero chips are not recurrent. The Python comparison checks cycle-test counts and uniqueness against the reviewer's copied literal state-graph script; it is evidence, not a general Lean cycle-test proof.

logs/replay-result.json contains replay receipts, source hashes, audit totals and the seven remaining Props. results.json is the delivery summary. The source archive excludes build outputs, generated logs, task metadata and cached inputs. Original failed development logs are retained in the lane.
