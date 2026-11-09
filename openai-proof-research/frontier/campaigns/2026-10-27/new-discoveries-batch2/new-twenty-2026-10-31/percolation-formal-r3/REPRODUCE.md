Run from this lane. Lean and leanchecker are from
/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
(Lean 4.34.1). Only bundled Std/Lean and local sources are imported. No mathlib,
network, installation, git operation or other lane's script is required.

The delivered source-only.zip contains src/, module-order.txt, guard.sh and
replay.sh. The already fresh-extracted directory is the exact extraction used
for the final strict replay; its logs contain every compiler and explicit-module
checker invocation, and module-times.json summarizes their times and memory.
Source hashes and the archive hash are recorded in results.json and provenance.json.

To resume the delivered extracted replay:

```bash
cd fresh-extracted
RESUME=1 bash replay.sh
```

To force a complete replay of that extraction:

```bash
cd fresh-extracted
bash replay.sh
```

The driver creates a whole-source signature. RESUME skips a module only when
both its successful compile/check marker and its compiled output exist and
the signature matches. Every invocation uses its own process, -M3500 and
-DwarningAsError=true; leanchecker always receives an explicit module argument.
The guard sets two-CPU affinity, CPU 120 seconds, wall 140 seconds, allocator
arenas 2, lane-local TMPDIR, and a 6 GiB process-group RSS watchdog. It waits
for and reaps its process. Run only one driver/heavy command at a time.

For data generation, the independent scripts in the lane are setup.py,
export.py, trim.py, generate_pilot.py, finalize.py and report.py. Every Python
invocation must use a real absolute script path and guard.sh, for example:

```bash
./guard.sh export-repeat python3 -I "$PWD/export.py"
```

setup.py copies only source modules and module-order.txt from the read-only
round-2 archive after checking archive paths. export.py implements the actual
truth-table enumeration order. ExportProbe.lean exports the actual Lean input
formula with #eval solely as data; finalize.py compare checks byte equality.
Solving was serial, once with and once without normalization:

```bash
./guard.sh solve-input-repeat /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical --lrat=true --binary=false input.cnf input.lrat
```

Exit 20 means UNSAT. trim.py takes input or normalized as its final argument;
it does backward reachability, then checks every retained step independently.
The unnormalized check approached the CPU cap, so future work should split
that external verification into bounded shards rather than increase limits.
The unused trim_only.py is an alternative checkpointing trimmer; it was not
used for the reported certificate checks.

The 500-addition and 2000-addition modules are separate measurement runs over
the same certificate prefix, not 2500 distinct proved steps. The delivered
prefix consists of exactly 2000 distinct additions. pilot-info.json records
the last original LRAT ID. input-trimmed.json stores all retained additions in
order. To continue, start at zero-based steps[2000], supply named theorems for
new input dependencies, and import Pilot2000. No symmetry bridge is necessary.
Do not run a monolithic full-certificate Lean computation. Size later modules
using the measured results.json rates and retain one-module-per-process replay.

The current endpoint remains conditional on ReplayFrontierUnsat5. This Prop
asserts that inputCNF5 together with all first-2000 derived clauses has no
satisfying valuation; it is not a claimed formal replay of the unreplayed suffix.
