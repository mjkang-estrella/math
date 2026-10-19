# Local prefreeze research archive

Read report.md, then spin-moments.md, atomic-conditioning.md, sle-clock.md, geometric-screens.md and reading-limits.md. RIGHTS.md separates original work from private evidence. No candidate is nominated.

The parent receives detached FINAL.json and REPORT.md SHA256 anchors outside the packet. Verification requires both explicit arguments:

    python -B packet/public/verify.py --root ROOT --tree REPO/sources/preprints-tree.json --finalhash DETACHED_FINAL_SHA256 --reporthash DETACHED_REPORT_SHA256

MANIFEST.json lists exactly every packet file and directory; FINAL.json binds it and both report identities. The verifier performs reads only. integrity_controls.py creates disposable COPIES under ROOT/controls, exercises acceptance/rejection cases against the same final anchors, removes its temporary copies and writes an integrity-only receipt. It does not mutate the sealed original packet or decide mathematics.
