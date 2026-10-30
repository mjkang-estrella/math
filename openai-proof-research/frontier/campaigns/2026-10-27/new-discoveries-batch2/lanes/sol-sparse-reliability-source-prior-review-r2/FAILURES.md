# Preserved failures and limits

- The first pwd/recursive rg inventory ran outside the required helper guard. It produced a very large truncated listing. No files were edited by that call. This was an execution-policy failure; all subsequent helper/Python/retrieval/edit/hash commands used the assigned guard. Native bounded reads and apply_patch were used as permitted.
- Initial broad printing caused output truncation; scoped subsequent reads were used. No full-body-reading claim is based on truncated output.
- A guarded parser attempt failed with ModuleNotFoundError: No module named 'bs4', exit 1. No installation was attempted; standard-library regex/XML parsing replaced it.
- retrieval.jsonl retains all HTTP failures and hashes of returned error bodies. Wiley returned 403 once; stopped. Two guessed author/institutional URLs returned 404 once each. Neither denial nor a missing guessed URL proves body absence.
- Bing returned irrelevant results for both scholarly queries. Both responses are preserved as unusable search coverage, not absence evidence.
- No previously denied GitHub/ScienceDirect/Google challenge/Colibri route or rate-limited Crossref query was retried. No proxy or TLS changes, no bypass.
- Procedia version of record and Networks 2018 article remain unread. A 2025 arXiv predecessor was obtained and compared, not conflated with the published version.
- Current public proof-registry body/head audit and all-history clearance remain unavailable. No parked historical search was reopened.
- Exact finite diagnostics refute specified predecessor inequalities; they do not prove the unbounded candidate optimum. No acceptance, formal certificate, paper or novelty clearance is supplied.
