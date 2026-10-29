# Factorial product proof packet

Pending independent final review; credit 0. No acceptance or count change.
The author line follows the campaign convention "Research manuscript"; it asserts no invented human authorship.

The ordinary proof is paper.pdf; its editable source is paper.json and its deterministic builder is build_paper.py.
certificate.py regenerates all 176 integer valuation entries and checks exact rational products.
Both complete dissent-bearing reviews are retained under component/inputs and evidence/.
No survey inventories or own compiled Lean artifacts are packaged.

Use Python 3 with reportlab 4.4.3 and Poppler (version recorded below) (actual versions in build-environment.json).
All helpers must run under the unchanged helper_guard.py. From this directory:

    python helper_guard.py python certificate.py
    python helper_guard.py python build_paper.py
    python helper_guard.py python pack.py /absolute/new/packet.zip
    python helper_guard.py python component/replay.py source-only.zip /absolute/new/replay-directory

The strict original replay checks the pinned installed dependencies and historical frozen originals at their recorded paths.
For a self-contained provenance check without access to those historical originals, run:

    python helper_guard.py python portable_replay.py /absolute/new/replay-directory

This verifies every shipped component byte and all frozen copied inputs, the Lean binary, mathlib and eight pins,
upstream dependency artifacts including private/server hashes, then runs the unchanged Lean guard and exhaustive audit.
It does not claim to reverify unavailable historical originals. Only the portable orchestration differs; mathematical
source, FullAudit and the Lean guard are byte-identical. The strict replay receipt is separately retained by the lane.
Both replay modes compile one mathematical module and audit exactly 31 actual declarations with only the standard three axioms.
Pinned packages must be preinstalled at the exact paths in pins.json; neither replay downloads dependencies.
The Lean command is serial -j1 -M2700 with warningAsError, CPU210, wall230s, group RSS2800MiB at45ms.
The helper guard is AS/groupRSS512MiB CPU210 wall230s at40ms, BLAS1. Never raise caps.

To rebuild the outer archive byte-identically after extraction, run pack.py outside its input directory.
manifest.json verifies the full payload; the packer rejects unlisted files. Run compilation in a new external scratch
directory so generated .olean files cannot enter the payload. Historical failed logs remain in component/logs.

Install Python build packages in a local environment: reportlab==4.4.3 pillow==13.0.0 charset-normalizer==3.5.2.
See PREPARATION-FAILURES.md for the legacy NEXT hash and unavailable PDF marker qualifications.
