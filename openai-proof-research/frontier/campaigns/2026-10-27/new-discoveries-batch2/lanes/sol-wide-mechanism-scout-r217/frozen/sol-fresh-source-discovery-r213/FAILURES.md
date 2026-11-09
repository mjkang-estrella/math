# Preserved failures and limits

Initial native pwd/rg read-only inventory and bounded cat/ancestor-instruction reads were outside helper_guard before guard usage was established. All later helper, Python, HTTP, extraction, editing and hashing used the prescribed guard. No shared writes.

1. bs4 parser attempt: ModuleNotFoundError: No module named bs4. No installation or retry; standard-library regex used for search descriptions only. Scientific PDF bodies extracted by pdftotext.
2. Gessel section locator: ValueError: substring not found for "4. Jacobi". Corrected bounded offset read found actual Section4 title; source bytes unchanged.
3. checks.py extended diagnostic ran204.256 seconds, peak sampled group RSS76,029,952 bytes, guard exit1, no cap raised. It reached final JSON TypeError: Object of type One is not JSON serializable. Full script/stderr and empty stdout retained. Intermediate assertions are NOT promoted to recorded results.
4. checks-bounded.py first run had the same SymPy-integer JSON serialization failure; failed-checks-bounded.py and failed-checks-bounded.stderr retained. Corrected output explicitly converts degrees/root counts to Python integers; smaller replay completes in under1second.
5. Crossref exact-title query returned unrelated records. They were not assigned to the source; journal DOI/body remain unauthenticated.
6. Pattern-covers bytes downloaded unnecessarily after early screen already showed r108. Retained unused, no reopening or fresh-slot claim.

No access denial encountered anew; all inherited denied routes left untouched. Current registry/all-history and journal-body gaps remain. stdout truncation in some large native tool reads was corrected by focused body reads; no claim of auditing every page of each source. All retrieval receipts and scientific byte bindings retained. Sampled RSS cannot rule out unsampled transients.
