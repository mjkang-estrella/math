Portability and limits (DRAFT dossier, lane common-basis-manuscript-pi-r2)
===========================================================================

Contents
- src/*.lean          the 12 immutable mathematical modules, byte-identical to
                      the frozen author lane expanded-corpus-r250 (SHA-256 in
                      lean-source-manifest.json; verified before packaging)
- matroid-certificate.json   the complete finite certificate: 76 bases, both
                      deletion-complementary base lists, exchange flag
- author-ordinary-check.log  this lane's ordinary recheck of every number
- replay.sh           portable strict rebuild, see header comment
- ordinary_check.py   standalone rerun of the ordinary mathematics

Pinned external dependencies (NOT shipped, user-supplied)
- Lean 4.34.1 binaries via env LEAN_BIN
- mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 prebuilt package trees via
  env LEAN_PACKAGES
No prebuilt .olean files and no large caches are included in this archive. The
upstream packages are trusted prebuilt oleans in the frozen lane as well; this
archive makes NO source-to-olean attestation claim for them.

What was and was not run in this lane
- The 12-module strict replay was NOT rerun here; the independent strict
  Lean-fidelity audit was running in a separate lane at authoring time, and the
  author-side records in the frozen lane (replay-result.json, 24 successful
  stages) remain the only execution evidence. replay.sh above is provided
  verified for path/portability hygiene but its full execution is left to the
  audit, the root final replay, or the reader.
- The ordinary mathematics (Sections 2-5 of the paper) WAS rederived in this
  lane; see author-ordinary-check.log and ordinary_check.py.

Status: everything in this DRAFT is zero-credit pending the independent strict
audit, root manuscript review, and final replay.
