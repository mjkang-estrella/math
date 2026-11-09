# Strict, resumable reproduction

Pinned toolchain: /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin, Lean 4.34.1, bundled Std/Lean only. No mathlib or network operation is needed. Every write, including extraction, build, temporary and cache files, must stay in this round-2 lane.

Extract source-only.zip into a new directory INSIDE this lane. The archive contains exactly frozen Lean sources, module-order.txt, source-manifest.sha256 and the replay, guard and scan utilities; it contains no oleans, compiled code or logs. For example, from this lane:

```sh
mkdir replay-root
unzip -q source-only.zip -d replay-root
cd replay-root
sha256sum -c source-manifest.sha256
./replay.sh
```

For an interrupted run: `RESUME=1 ./replay.sh`. Resume skips only modules with a success stamp matching the digest of ALL current Lean sources and an existing compiled output. A stamp is written only after both compiler and checker succeed. Any Lean source change invalidates every stamp. Delete build and logs or omit RESUME for a complete new replay.

The module order has 38 explicit names. The driver runs exactly one Lean module per process with `lean -M3500 -DwarningAsError=true`, then `leanchecker MODULE` with an explicit module, stopping on failure. Every call is wrapped by guard.sh: CPU affinity 0,1; CPU 120 s; wall 140 s; RSS watchdog 6 GiB; MALLOC_ARENA_MAX=2; lane-local TMPDIR, XDG_CACHE_HOME and PYTHONPYCACHEPREFIX. No process limit is raised after failure. It runs serially and waits for every guarded child. Source scan Python also runs under the guard, with -I and a real absolute script path. Do not invoke any neighboring lane's scripts.

Per-module compiler/checker stdout, stderr and wall/peak-RSS receipts are under logs/. Endpoint logs print transitive axioms; Audit logs inspect every local declaration for unsafe/partial/extern/implementation overrides, local assumptions and forbidden generated recursion helpers. The source scanner rejects the forbidden tokens, including bv_decide; the single audit string naming the forbidden helper is treated as an audit pattern, not executable use.

The delivered fresh-extracted/ is a clean extraction of source-only.zip and contains the actual strict replay logs. results.json gives all measured process times and statuses; fresh-replay.log gives the driver progress. packet/logs/ retains development failures and the successful development audit, separately from the fresh verification. package audit and source scan are required in every reproduction; no certificate is replayed because none has been implemented.

To regenerate results.json from the existing fresh extraction, run from this lane:

```sh
./packet/guard.sh python3 -I "$PWD/collect_results.py" "$PWD"
```

The archive's SHA256 is recorded in results.json. The original source definitions can be checked against the round-1 archive using the recorded byte comparisons and immutable hash. No source zip extraction or replay writes outside this lane.
