# Replay-fit round 2, not acceptance

Run serially from this lane. No network, package installation or upstream writes are needed.
Lean 4.34.1 and read-only mathlib at d13f23b723b8a846827a245b89c10fc7d3f11612 are configured by env.sh.
Imported mathlib/core objects are trusted rather than rebuilt.

The source-only archive contains the original unchanged modules, split SpectralWitness modules and StatementClosure audit.
Its SHA-256 is in packet.sha256. For a new independent extraction and strict replay, choose an unused lane-local name:

    ./run python3 -I extract.py root-fresh
    ./replay.sh root-fresh

The driver compiles one module per process with -j2 -M3500 -DwarningAsError=true and checks each using explicit-module leanchecker.
All Lean, checker and Python invocations must go through ./run. The watchdog uses two CPUs (0,1), CPU 120 s, wall 140 s, aggregate process-group RSS 6 GiB, and MALLOC_ARENA_MAX=2.
TMPDIR, TMP, TEMP and XDG_CACHE_HOME point into this lane.
The driver stops on failure, and resumes only successful module/checker pairs in the named directory. Do not modify source or objects while resuming; select a fresh directory for changed sources. No parallel driver runs.

StatementClosure computes the endpoint's statement closure using the loaded environment, traversing packet constants' types and bodies, starting at constants in the endpoint's type. The endpoint itself is included without traversing its proof. It writes closure-raw.json into the build directory, prints closure members and endpoint axioms, and rejects forbidden local declaration metadata. Generated declarations are included in the metadata audit.

The original unsplit SpectralWitness exceeded the wall cap again, so closure computation uses the new compiled endpoint. preservation.py checks compiler-reported declaration source spans against the original extracted packet and checks whole-module byte identity for every closure module. It also checks all relocated/generated SpectralWitness declarations outside the closure. The endpoint module is wholly byte-identical.

Development reused eight unchanged round 1 prerequisite objects to shorten iteration; those development records are not fresh replay evidence. Final records use a newly extracted directory and compile every module. Full logs distinguish development, original profile and fresh replay.

Historical diagnostics: the first copied profiling source accidentally retained a round 1 marker-log destination. It appended diagnostic markers outside this lane before being stopped. No proof source or object there was changed; the log was not restored because that would be another out-of-lane write. The corrected profile writes only here. See RESULT.md for this instruction violation.

The metadata audit additionally required four code-generation changes outside the closure: NormalForm, TraceAction, AutomatonSemantics and MachineInvariant receive noncomputable sections; Movable, Clean, pluck, frontState, Machine.Accept and Machine.run receive explicit noncomputable modifiers. These prevent six generated partial `_unsafe_rec` declarations. preservation.py verifies that removing precisely these modifiers/sections restores the original module bytes. No logical declaration body or hypothesis in those modules changes.

To regenerate the closure/preservation report from a completed independent extraction, pass its directory name:

    ./run python3 -I preservation.py root-fresh
    ./run python3 -I report.py

Generated proof auxiliaries matrix._proof_1, matrix._proof_2 and matrix._proof_3 have no separate source ranges. The Lean metaprogram records their nearest source-bearing parent, matrix, and the source-span comparison checks that full declaration. This supplements complete whole-module byte identity for GroupSemantics and Endpoint.
