# r79 local research archive

Read `research.md` for the three sustained mechanism screens and exact unresolved interface. Read `reading-limits.md` before treating any source as fully inspected. No target was frozen and no nominee is submitted.

`private/` is evidence retained under its original rights. `public/` contains original prose and integrity code. The detached `REPORT.md`, `MANIFEST.json`, and `FINAL.json` sit outside `packet/`.

Run the read-only verifier with the FINAL SHA256 supplied externally by the agent or parent:

    python -B packet/public/verify.py --root /absolute/path/to/fresh-arithmetic-discovery-r79 --finalhash DETACHED_FINAL_SHA256

The verifier never infers its trusted final anchor from local files. `copied_controls.py` uses the same required external anchor and mutates temporary copies inside this owned directory. It leaves original payload and anchor files unchanged. Hash checks and controls are not mathematical verification.
