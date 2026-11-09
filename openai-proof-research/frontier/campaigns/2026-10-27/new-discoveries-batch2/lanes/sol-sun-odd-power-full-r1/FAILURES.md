# Preserved failures and limits

- Initial inventory command (pwd/rg/head) ran outside helper_guard.py. Native bounded instruction reads followed; all subsequent helper/Python/retrieval/edit/hash commands used the specified guard and environment. This initial protocol error is retained in the transcript and freeze.json, not represented as a fully compliant run.
- First parsing attempt failed under the guard: ModuleNotFoundError: bs4. No installation; stdlib parsing used. Exit1 retained in tool transcript.
- Author-page https://jwguo.faculty.ecnu.edu.cn/ failed DNS (exact receipt http.jsonl); no retry.
- Two arXiv search requests with unsupported order=date returned400; receipts retained. Later distinct queries used a supported sort; no access-control bypass.
- Bing searches returned irrelevant broad homonym results despite HTTP200. They do not clear prior art.
- NIST https://dlmf.nist.gov/17.7.E4.tex returned403 at2026-10-30T08:19:19.961496+00:00. Stop respected, no alternate NIST route or bypass.
- OpenAlex DOI lookup returned an empty result; the DOI was an unverified exploratory lookup, not an established source identifier. No inference about citations follows.
- Inherited GitHub API/raw/codeload/diff/patch, AMS, ScienceDirect and Google challenge routes were not retried. Current proof registries were not cleared, no live head hash claimed.
- Retrieved sources were initially read as local download artifacts; a separate before-further-work copy freeze was later made. Assigned scientific inputs were selectively frozen before scientific reading. This distinction is explicit in retrieved-freeze.json.
- No resource-cap increase; guard imposes512MiB AS/RSS,210s CPU,230s wall. Guard stderr receipts are in the tool transcript. No resource failure occurred in successful checks.
- No worldwide literature priority, all-history clearance, or fresh proof-registry clearance. No staged/accepted/countable outcome.
