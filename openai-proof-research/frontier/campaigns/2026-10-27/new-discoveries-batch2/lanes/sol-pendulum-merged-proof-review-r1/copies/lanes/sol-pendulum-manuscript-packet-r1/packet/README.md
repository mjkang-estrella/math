# Pendulum convexity: candidate source-only packet

Research manuscript; independent root review and acceptance pending. No publication, priority or count claim.

`paper/paper.txt` is the standalone mathematical manuscript source. Form-feed characters delimit five intended pages. Lines prefixed `@` are displayed mathematical formulas; `int[l,r]` denotes integration over [l,r], and `_+` denotes positive part. No PDF was authored: the mandatory skill marker failed under the unchanged guard, including a memory-saving Node retry. No rendering or visual QA success is claimed.

Fourteen mathematical modules and all 139 actual declaration records are included. `FullAudit.lean` is the exhaustive audit driver (not a fifteenth mathematical module). All 14 modules, including the root's Result, are byte-identical to the frozen root assembly. `actual-declarations.json` records actual elaborated types, module origins, transitive axioms and flags for every declaration, including generated helpers. `dependency-hashes.json` records actual upstream compiled dependency hashes; no own compiled artifacts are archived.

Inputs are stored once per full SHA256 under inputs/. `input-records.json` maps original paths to these deduplicated copies. Full source/subsumption and investment reviews retain all objections and historical/current registry gaps. The inherited r166 proof includes ancillary strictness and curvature discussion; those statements are outside this manuscript's formal claim. Earlier reviews' HOLD recommendations reflect their dates and scopes and are retained verbatim.

## Exact reproduction in the pinned local environment

From packet/ (or a fresh extraction), with a NEW lane-local target directory:

```
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
python3 helper_guard.py python3 package.py ../merged-source.zip
python3 helper_guard.py python3 replay_guard.py python3 replay.py ../merged-source.zip ../fresh-extraction
```

The unchanged helper/replay guard caps helper AS and sampled group RSS at 512 MiB, CPU210/wall230 seconds. The unchanged Lean guard uses serial -j1 -M2700 warningAsError=true autoImplicit=false, sampled group RSS2800 MiB CPU210/wall230 seconds per module, nominal45ms. Guard files and pins are byte-identical to the predecessors. Do not raise limits. Nominal sampling cannot guarantee the true continuous RSS maximum.

Repackaging from extraction uses the same exhaustive manifest and byte-identical deterministic ZIP metadata, excludes all newly compiled outputs, and must reproduce the archive hash. External pinned toolchain/package files and frozen originals are required; no network retrieval is performed. The archive is source-only, not a vendored toolchain or self-contained dependency distribution.

Allowed axioms: propext, Classical.choice, Quot.sound only. The source endpoint has no premises beyond those bound in SourceClaim. Root independent review remains required. Historical capped merge intervals and OpenAI incomplete-tree/176 missing-patch coverage remain unresolved acceptance conditions.
