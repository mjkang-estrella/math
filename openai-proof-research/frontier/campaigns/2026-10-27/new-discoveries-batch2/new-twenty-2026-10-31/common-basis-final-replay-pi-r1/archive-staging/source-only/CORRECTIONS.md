Corrections and honest tooling history (root-review copy, lane common-basis-final-replay-pi-r1, 2026-11-05)
============================================================================================================

This archive is the corrected successor of the pi-r2 source-only proof archive. Everything from the
original archive is retained byte-identical, including replay.sh and PORTABILITY.md, which are kept
as HISTORICAL records of the pi-r2 lane, not as cap-enforcing tools:

- replay.sh (original, retained verbatim): inherits the ambient PATH, HOME and Lean environment;
  sets only LEAN_PATH, a pinned-binary PATH prefix and MALLOC_ARENA_MAX=2. It does NOT enforce CPU
  affinity, CPU/wall/RSS/address-space limits, does NOT reject a nonempty build directory, and does
  NOT verify dependency hashes. Its header comment's "resource discipline" phrasing described the
  frozen lane's discipline, not an enforcement mechanism of this script.

- capped_replay.py (NEW, enforced wrapper, Python standard library only): the actual replay path.
  Verified archive SHA-256; safe extraction (relative paths, regular entries, no symlinks; per-member
  SHA-256 recorded and checked against lean-source-manifest.json and the author manifest); fresh
  build dir, refused if nonempty, no preexisting .olean; minimal private HOME; PATH pinned to
  LEAN_BIN first; LEAN_PATH = fresh build dir + discovered external package trees; per module
  `lean -j1 -M3500 -DwarningAsError=true` then `leanchecker`; per call <=2 CPU affinity, CPU 120 s
  (RLIMIT_CPU), wall 140 s, sampled-RSS 6 GiB guard, RLIMIT_AS 12 GiB with 64 GiB sampled-VmPeak
  hard guard, MALLOC_ARENA_MAX=2; every command, environment, exit status and resource peak logged.
  The pinned Lean 4.34.1 (commit 5045d005...) binaries and the mathlib d13f23b... checkout are
  verified against the completed review's pin manifest. The upstream packages are TRUSTED PREBUILT:
  no source-to-olean attestation is claimed or checked for them.

In the completed final replay (2026-11-05, lane common-basis-final-replay-pi-r1) this wrapper
produced 24/24 strict stages (12 modules x lean+leanchecker), the 106-declaration body-presence
review audit, and two negative controls failing exactly as scoped. Full receipts ship in that lane
and in the full-dossier archive under verification/.
