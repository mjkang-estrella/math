# Preserved failures and qualifications

All executions used the unchanged designated guard, with OPENBLAS_NUM_THREADS=1,
OMP_NUM_THREADS=1 and PYTHONDONTWRITEBYTECODE=1. No cap was raised. Guard receipts
are in the session tool transcript; per-request records are in retrieval.jsonl.
Sampled RSS is not an assurance about unsampled peaks.

1. The first verification/copy helper exited 1 after successfully verifying all
136 frozen entries: pathlib.relative_to received an absolute original and a
relative base. No original changed; the corrected absolute-base run reverified
all entries and copied them. This is a helper failure, not failed integrity.
2. A new publisher article.php route on the already TLS-failing dmgt host was
unnecessarily attempted. It again failed certificate verification. This was a
same-host revisit contrary to the requested avoidance of failed publisher routes;
it supplies no body evidence. No TLS checks were disabled and that host was then
abandoned. Exact URL/error retained. Prior publisher/Crossref/Google/EuDML/Sciendo
failures remain in the copied prior retrieval.jsonl and were not cleared here.
3. Guessed FNM Peterin page: 404. Old author PDF host discovered from OpenAlex:
DNS failure. Neither is source evidence.
4. Both Bing RSS responses are irrelevant (letter N and Microsoft results).
Neither supplies meaningful search coverage or absence evidence. DuckDuckGo
returned a human challenge (202); no submission, retry or bypass occurred.
5. OpenAlex citation request for W3170465799 was an erroneous unverified identifier.
Its empty response is DISCARDED. Correct source identity W3163236126 was obtained
from the source DOI, then its citation endpoint returned 19 records.
6. Initial Maribor download returned an ordinary study-use terms form, saved
with misleading .pdf suffix. pdftotext exited 1, reporting non-PDF syntax and no
xref table; no text/body evidence was obtained then. A form submission without
session cookie again returned HTML. The ordinary GET/form submission with cookie
session succeeded (147004 bytes). These were download-form HTTP POSTs accepting
study-use terms, not external messages, uploads or public posts. No login,
challenge solving, private endpoint or access-control bypass was used. All HTML
responses remain, distinguished from changat-session-body.pdf. Its MD5 matches
the public repository record; extraction then succeeded. Failed extraction
did not modify the successful PDF or any frozen original.
7. Two old historical compare intervals remain capped/unclosed. New fixed delta
coverage and unchanged current Problems tree do not fill deleted historical
bodies, issues, discussions, unindexed publications or all current proof bodies.
8. No resource termination occurred. Runtime/sampled-memory receipts remain in
the tool transcript; this lane does not claim a complete independently saved
per-execution stderr archive. No Lean, manuscript, child, git or shared edit.
