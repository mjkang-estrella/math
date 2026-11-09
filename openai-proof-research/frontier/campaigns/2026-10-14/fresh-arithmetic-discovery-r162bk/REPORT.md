# r162bk detached seal report

Status: PREFREEZE / no nominee. No mathematical gates or campaign increment.

FINAL.md SHA256: 6b2a689cb6ed32e4032b83549ccdd4096d7d6389a8ff2c5f10e7af417ec44056
MANIFEST.json SHA256: 65655d69cfdc17891ba1f03e2de692263513772c6a9bf07e5baa82ca9a460797

Payload: 64 regular files, 6303095 bytes.
Directories: 22, including the root. Whole packet: 66 files.
MANIFEST.json excludes itself and this REPORT.md; both have mode 0o100644.
The report's own detached SHA256 is emitted with the final handoff.

Before these seal files were created, the identical final verifier payload logic
passed exact safe membership, sorted uniqueness, hashes, lengths and full modes.
All33 canonical Git blob bindings matched. The five exact completed originals
matched initial hashes/lengths/permission bits, their byte copies, and the later
full-mode record. Initial full st_mode was not captured; the later record does
not repair or backdate that limitation.

Tiny copied controls passed the valid and restored cases and rejected a mutated
payload and wrong FINAL/MANIFEST/REPORT anchors. These are artifact checks only.
No sealed payload file is changed by this seal or its read-only verifier.

Run verify.py with --root and the three explicit detached --final, --manifest,
and --report SHA256 anchors. The final post-seal verification result is reported
in the handoff, without changing this report to record itself.
