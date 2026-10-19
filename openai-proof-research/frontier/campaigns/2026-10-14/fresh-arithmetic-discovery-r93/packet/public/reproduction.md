# Reproduction and artifact controls

Use Python3; the verifier has no third-party dependencies. Supply the detached FINAL SHA256 from the external handoff, never a hash derived silently from the packet being trusted:

    python -B packet/public/code/verify.py --root /absolute/path/to/fresh-arithmetic-discovery-r93 --final-sha256 DETACHED_FINAL_SHA256

The root contains `FINAL.json`, the outside `REPORT.md`, reproduction/acquisition/search scripts and `packet/`. FINAL binds the outside report, exact packet manifest, frozen bytes, complete canonical tree and listed root scripts. The manifest lists every payload except itself and every directory including the root; file bytes, sizes, modes and link counts, and directory modes are checked. Symlinks are rejected. FINAL itself is authenticated by the required detached hash. The manifest's own mode and root-level extra-file inventory are not sealed; its bytes are sealed. Root script bytes are bound, not a full root permission policy.

The verifier installs a Python audit hook denying write opens, filesystem mutations and subprocess creation. It prints its result only. The code is available for inspection. Successful execution plus unchanged input snapshots is an artifact observation, not a general proof about every possible Python runtime or a mathematical theorem.

Canonical checks compare all22 retained source metadata records against the copied complete tree, verify pinned raw URLs, size/SHA256 and the Git blob SHA1 with its header. The four successful retained primary PDF/text pairs are Chen v1, Anghel v1, BHM v2 and Horrocks's1980 original volume; successful acquisition does not imply full semantic reading. The28 history and5 context copies have separate exact hash metadata. Reading and failed retrieval limits are in `reading-limits.md`.

Run copied controls only within the owned directory:

    python -B packet/public/code/controls.py --root /absolute/path/to/fresh-arithmetic-discovery-r93 --final-sha256 DETACHED_FINAL_SHA256

The runner creates `control-work` under that root, makes one copy at a time, and removes the whole temporary workspace before comparing the original root. It never alters original payloads. It compares every copied input before/after verification and the full original root before/after temporary-workspace removal, using paths, bytes, modes and link counts. It prints its receipt to stdout; recording that receipt afterward is a separately disclosed new root file.

The14 cases are baseline; wrong detached anchor; changed or missing proof; extra file or directory; payload symlink, mode or hardlink; changed manifest or outside report; and three deliberately NEW test anchors for canonical-metadata, source-Git-blob and freeze-receipt corruption. Those last three reseal only copied test metadata so the internal checks are exercised. They are not alternative trusted author anchors. No audit-denial probe is in this suite, and no finite mathematical test is run.

The external control receipt is not recursively included in the already sealed packet. Its SHA256 and result are reported separately in the handoff. Artifact checks assign no correctness, contribution, eligibility, acceptance or campaign count.
