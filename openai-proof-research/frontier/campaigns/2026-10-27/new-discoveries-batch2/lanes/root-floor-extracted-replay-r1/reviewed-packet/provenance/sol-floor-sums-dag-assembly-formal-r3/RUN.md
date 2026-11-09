# Serial kernel replay

The pinned Lean binary and nine package revisions are in `pins.json`. Every
Python invocation uses the absolute `helper_guard.py` specified in the assignment,
with OPENBLAS_NUM_THREADS=1, OMP_NUM_THREADS=1 and PYTHONDONTWRITEBYTECODE=1.
Helpers retain AS/group RSS512MiB, CPU210 and wall230. `lean_guard.py` remains
under that helper guard; only its separate Lean process has its inherited soft AS
limit removed, as explicitly required for Lean. That process has -j1 -M2700,
group RSS2800MiB, CPU210 and wall230. No Lean resource limit is increased.

All mathematical source uses autoImplicit=false and warningAsError=true.
Exactly one Lean invocation runs at a time. No subprocess chains overlap.
`logs` records invocations; `attempts` and the numbered attempt directories
preserve failed source versions and diagnostics. Generated source is proof code,
not a trusted parser/checker axiom.

`source-only.tar.gz` contains current Lean sources, replay support and immutable
scientific reference bindings, with deterministic ordering, timestamps and gzip
header. It contains no own compiled objects and does not embed predecessor
archives recursively. Full immutable references and administrative snapshots
remain in the enclosing lane. Extract into a fresh directory and run
`bash replay.sh` there. Replay compiles exactly the successful mathematical
modules, in dependency order, then every exhaustive audit partition serially.
Attempt sources in the archive do not become checked merely by being packaged.

The audit selects declarations by actual Lean module origin, including private
and compiler-generated declarations. Every selected declaration has its full
explicit type, safety and transitive axioms printed. Partitioning by module
changes the size of an audit invocation, not declaration coverage. Audit/display
modules are separate from mathematical origins. Large logs are streamed by the
verifier. Only propext, Classical.choice and Quot.sound are allowed.

After replay and both audits, `manifest.py` writes the final manifest excluding
itself as a manifest artifact and the final receipt (the script itself is
included). A separate guarded `final_verify.py` invocation rechecks manifest
coverage and hashes, all originals/copies, source/pin bindings, byte identity of
the four inherited modules, extracted source identity and exhaustive audit
agreement. Its integrity result does not independently establish novelty or
campaign acceptance. Consult SUMMARY.md for the exact mathematical status.
