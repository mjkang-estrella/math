# Replay-fit diagnostic handoff

This lane does not claim acceptance or a completed replay-fit packet. Frozen source copies are in `original-330264` and `original-324342`. The 330264 archive was safely extracted with path and symlink checks and rejection of bundled objects. The 324342 source-only snapshot was created from the exact main, audit and control bytes bound by r4/MANIFEST.json, then safely extracted. No author script was executed.

Run from this lane, serially:

```sh
./run python3 -I prepare.py
./run python3 -I profile.py
./replay.sh 330264
./profile.sh 330264
./replay.sh 324342
./profile.sh 324342
```

Each replay stops at its first failed build or explicit-module checker. It resumes completed module/checker pairs in its existing lane-local build directory. For a fresh replay, use a fresh lane-local build directory and remove corresponding lane-local `.ok` files. Do not run these drivers concurrently. Diagnostic profile files add only `#eval IO.println` markers before declarations; they are not proposed replacement proof packets and have no claimed checker success.

`run` invokes the RSS watchdog with 6 GiB aggregate process-group RSS, CPU 120 seconds, wall 140 seconds, two-CPU affinity and MALLOC_ARENA_MAX=2. Every Lean call specifies -M3500, -j2 and warningAsError. TMPDIR, TMP, TEMP and XDG_CACHE_HOME are lane-local. Python is isolated (-I). Imported pinned mathlib and core objects are trusted, not rebuilt.

The driver does not proceed past failed imports to endpoint axiom audits, declaration metadata audits or conference controls. Those checks remain NOT REACHED if a prerequisite fails; the frozen historical audit output does not establish a fresh success.

For durable declaration diagnostics, run `./run python3 -I durable-profile.py` after `profile.py` and before `profile.sh`. This version logs entry and monotonic milliseconds directly to lane-local `logs/<id>-declarations.log` and flushes each marker. The initial 330264 stdout-marker profile was manually interrupted and replaced because redirected output was buffered; `330264-profile-buffered-interrupted.log` is that canceled diagnostic, not a resource-cap result. No limit was changed.

## Successful 324342 packet

The completed import-narrowed packet is `324342-replay-fit-source.zip`. All four modules passed in `fresh-324342`; `final324342.sh` resumes that replay. Only the endpoint-module imports changed; all remaining bytes of the main module and all bytes of supplied Audit/Controls remain identical. MetadataAudit is a new check.

For an independent fresh extraction and full replay, choose new lane-local names and run serially:

```sh
./run python3 -I extract324342.py root-fresh-324342
./final324342.sh root-fresh-324342 root324342
```

The second argument chooses separate log/checkpoint names, so previous successful logs are preserved. Both directory and log prefix must be lane-local relative names; use the example literally with unused names. Every checker invocation explicitly names its module. Strict compilation of Audit prints the endpoint axioms and all original module declaration axiom sets. MetadataAudit rejects unsafe/partial/implemented_by/extern/_unsafe_rec metadata and disallowed axioms for main/control declarations. Controls rebuilds the supplied Paley non-vacuity control. No negative test is claimed beyond the packet's supplied controls.

The original baseline drivers above remain diagnostics for the frozen sources; they are expected to stop at the recorded cap failures. They are not the replay driver for the successful 324342 replacement packet.
