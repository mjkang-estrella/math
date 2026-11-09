# Failures and access log — pi-mathdb-finite-arithmetic-triage-r302

All timestamps UTC 2026-10-30.

1. **Live MathDB API rate-limited (HTTP 429 / CF error 1015).** Two probes via guarded
   `scripts/fetch.py` (`detail 350863`, `list combinatorics 0`) returned 429. Per access
   discipline: stopped immediately, no retry, no bypass. All record data therefore comes
   from **local caches only**; no live statement, solution body, or registry was read.
   Consequence: "closest primary proof body" was **not** read for any shortlisted record;
   every shortlist entry carries a mandatory primary-read step.

2. **sol-mathdb-technical-shortlist-r300 not found.** No directory or file matching the
   interrupted r300 lane exists under the campaign tree; nothing to resume. Recorded in
   administrative/input-bindings.json era notes; root informed via this report.

3. **numpy unavailable in the guarded system python** (`ModuleNotFoundError`). The Delannoy
   real-rootedness check was reimplemented with pure-Python Durand–Kerner
   (`scripts/check_misc3.py`). No package installation was performed.

4. **Transient script defects (fixed in-place, retained):** `scripts/check_nim.py` used a
   buggy local-window period test producing false period-equality violations; corrected in
   `scripts/check_nim2.py` (full-tail minimal period). `check_misc.py`/`check_misc2.py`
   used a wrong Delannoy boundary (`D(0,k)=0` vs `=1`); both conventions were run and,
   notably, **both** gave non-real roots for all n≥2 rows of the squared Delannoy triangle,
   contradicting the source paper's reported supporting evidence — recorded as a
   convention-conflict objection on 375724 rather than a disposition.

5. **Statement mangling in cached records.** MathDB LaTeX→cache conversion damaged the
   literal statements of 353474, 380719 (unreadable placeholders) and 378937, 362667
   (recoverable but flagged). These were not promoted without qualification.

6. **Not performed (out of scope / forbidden):** Google requests; GitHub API/raw/codeload/
   diff/patch routes; ScienceDirect; any MathDB/shared/git mutation; browser tabs; reading
   lane r301 corpus outputs or any mutable sibling-lane output.

7. **First-run Bonse check** (`check_bonse2.py` initial version) had a bytearray sieve bug
   (IndexError) fixed in the same invocation window; final output is the recorded one.
