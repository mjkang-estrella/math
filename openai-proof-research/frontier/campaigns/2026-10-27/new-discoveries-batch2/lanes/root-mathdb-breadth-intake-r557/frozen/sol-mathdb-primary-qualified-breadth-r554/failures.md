# Failures, access holds and deviations

- Initial extract.py failed with ModuleNotFoundError: bs4. Failed source retained as extract-failed-bs4.py. Replaced with stdlib HTMLParser, without changing guard caps. No derivative was read from the failed run.
- First passages.py and short.py outputs were truncated by the output budget. No whole-body reading inferred from them; final_passages.py emitted bounded retained selections. Disposition coverage claims are limited to passages actually displayed.
- Zero MathDB requests: inherited HTTP429 hold. Current proof registry unavailable; every row retains registry HOLD. No absence-of-hits inference.
- Parked AIM, Kourovka, EGRES, AIProofWatch, DMGT TLS, ProjectEuclid challenge, ResearchGate403 and OEIS A274199/internal403 routes untouched. No Google/GitHub API/raw/codeload/diff, ScienceDirect, browser/preview, TLS bypass, accounts, messages, uploads or publications.
- Four lawful primary/institutional fetches succeeded; no new HTTP failure or retry. No alternate-route fishing.
- No Lean, manuscript, credit, shared ledger/index/NEXT or git changes. No child workers. Guard limits unchanged: AS/groupRSS512MiB, CPU210s, wall230s; every Python/helper computation launched via the fixed guard with requested environment and -B.
- No promoted target. r304/r363 and ledger context were bound, then scoped ID/context inspection used; their full historical trees and manuscripts were not read. This bounds prior claims rather than supplying clearance.
- Initial sealing negative test rejected the hash fixture at file-set equality because the excluded final receipt had not yet been created. This was a fixture-order failure, not hash acceptance. Failed sealing source retained as seal-failed-receipt-fixture.py. Added the named receipt placeholder before sealing/testing; final receipt replaces it after verification.
