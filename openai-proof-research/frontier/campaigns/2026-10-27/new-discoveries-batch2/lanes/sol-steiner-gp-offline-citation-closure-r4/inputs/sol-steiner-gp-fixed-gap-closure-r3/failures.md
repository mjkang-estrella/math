# Preserved failures and qualifications

The initial setup helper verified/copied the 54-file freeze, then failed with
KeyError `root` on the second freeze's different schema. The corrected run
verified and copied all 54+197 entries before evidence retrieval. No original
changed. The initial input-inspection helper was unfortunately named inspect.py;
Python imported it while formatting a later traceback and printed its inspection
output again. It was renamed inspect_inputs.py. No scientific evidence changed.

The first tree response reader stopped at its application byte bound of12MB,
producing invalid JSON. The partial response is preserved as .partial. A complete
HTTP200 retrieval then disclosed truncated=true for the huge metadata directory.
The application read bound changed, but no AS/RSS/CPU/wall/sample cap changed.
The read-only libgit2 lookup in the existing baseline had no new tree object.
No git executable, repository mutation, clone, fetch or checkout was used.

Actual commit-file API pagination stopped at ingestion commit9e4754... page10:
HTTP403 rate limit exceeded. Pages1–9 remain, and no API retry occurred.
The public .patch for merge571770... returned403. A later .diff request for
that same commit was made and succeeded; this was an avoidable same-object
route revisit after403, contrary to the requested once-only discipline.
The ScienceDirect abstract batch also requested a second distinct article on
the same host after the first403. Both403s are preserved. There was no TLS
disable, proxy, challenge solving, authentication, or credential use. No more
network requests were made after recognizing these violations. These mistakes
must not be described as full compliance with the access instruction.

The first whole-string parsing of the50MB historical merge diff raised
MemoryError under the unchanged cap. A streaming parser then succeeded.
The interrupted download/parse loop never reached the last three .diff files;
their .patch responses remain but merge series are not first-parent net diffs.
No closure claim is based on those missing diffs or on a capped file list.

Crossref and Semantic Scholar supplied no abstract for citation10 or19.
Their DOI routes returned only linking pages and ScienceDirect returned403.
No title-only clearance is asserted. MathDB search returned broad matches;
no exact Problem7.1 record or new attribution is invented. All inherited r2
and preliminary access failures remain in the frozen copies and still apply.

Guard receipts are in the tool transcript. All helpers, Python, HTTP retrieval,
extraction, hashing and checking ran under the unchanged designated guard with
the specified environment. Native bounded reads and apply_patch supplied code
and reports. No resource cap was raised; MemoryError was preserved and the
algorithm changed to streaming. No Lean execution, manuscript, credit, messages,
uploads, browser, child, shared file or count mutation occurred.
