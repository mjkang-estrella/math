# Portable strict replay

Use Python 3, POSIX sh, Linux /proc and the pinned prebuilt dependency libraries.
Extract adverse-381433-manuscript-source.zip into a NEW EMPTY directory, first
rejecting absolute names, parent traversal, symlinks and compiled artifacts.
Verify SOURCE-MANIFEST.json before execution. No downloads are performed.

    export LEAN_BIN=/path/to/lean-4.34.1-linux/bin
    export LEAN_PACKAGES=/path/to/pinned/.lake/packages
    python3 -I replay.py

The local verification used Lean 4.34.1 commit
5045d0056413266e57c625dcd7c365b10e377c52, binary directory
/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin;
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, cached at
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages.
Dependency build libraries must match these pins; the replay verifies the Lean
version and proof source hashes, but does not rebuild or independently authenticate
all dependency oleans. The inherited dependency identity receipt is in the full dossier.

The driver refuses existing oleans, discards inherited Lean search/plugin options,
builds sequentially with -j1 -DwarningAsError=true, and runs leanchecker for each
of 13 proof modules and the reviewer-authored Reviewer module. DossierAudit
prints complete types, bodies, unsafe/partial flags and transitive axiom sets for
all 167 declarations (including generated declarations). Its own compiled module
also passes leanchecker. It permits only propext, Classical.choice, Quot.sound.
The original Audit.lean is retained byte-identically; DossierAudit extends its
scope to Reviewer without changing any original module.

Every Lean/leanchecker invocation, including --version and six negative controls,
is under scripts/bounded.py: at most two CPU affinity slots, CPU 120 s, wall
140 s, total process-group VmRSS sampled every 0.1 s and killed above 6 GiB,
MALLOC_ARENA_MAX=2. Shared pages may be counted twice, conservatively. Sampling
is not an instantaneous hard memory limit. Groups are killed/reaped after exit.
Only one invocation runs at a time. Negative controls reject wrong alpha,
upsilon, least eigenvalue and adjacency, plus corrupted fractional/kernel inputs.
A seventh control verifies refusal to reuse a compiled extraction.

Success: receipts/replay.json says strict_fresh_replay = pass, declaration_count
= 167, negative_controls = 7. Full audit: logs/full-audit.log.gz. Individual
resource receipts preserve limits, measured peaks, exit status and termination.
The full dossier includes the actual fresh extraction and its receipts. Do not
run again in that directory; start another empty extraction.

Rebuild the paper with python3 -I paper/manuscript.py (ReportLab and DejaVu fonts);
render using pdftoppm -r 100 -png paper/adverse-latin6-draft.pdf qa/page.
