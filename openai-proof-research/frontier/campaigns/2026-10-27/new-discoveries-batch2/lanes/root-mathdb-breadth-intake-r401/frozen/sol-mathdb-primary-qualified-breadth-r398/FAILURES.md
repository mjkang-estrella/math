# Failures and limits retained

All work is lane-local. No upstream verifier was run and no upstream receipt rewritten. Fixed helper guard: 512 MiB address space and sampled group RSS, 210 CPU seconds, 230 wall seconds, no increases. Every Python helper invocation used OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 and the specified helper_guard.py with python3 -B.

Pre-content freeze attempts are retained as freeze-attempt1.py through freeze-attempt4.py; each exited nonzero before scientific content was read:

1. TypeError at r304 manifest parsing: expected a dict with files, but r304 uses a list. Guard exit 1, sampled peak group RSS 28,344,320 bytes.
2. AssertionError on r304 README: helper incorrectly required an absent size/bytes field, comparing the actual size with None. Guard exit 1, sampled peak 25,649,152 bytes. This was not a hash mismatch.
3. AssertionError against the current ledger using a historical snapshot binding. Current ledger and historical snapshot are different versions; both were frozen independently. Guard exit 1, sampled peak 27,115,520 bytes.
4. AssertionError on r304 snapshot ledger: again the absent-size-field helper bug, not a snapshot SHA256 mismatch. Guard exit 1, sampled peak 28,299,264 bytes.

Final helper accepts absent optional size metadata while recording actual sizes. r304-manifest-audit.json independently confirms all six r304 manifest SHA256 entries match. The final freeze bound 100 files and checked all twenty r301 corpus chunks in place plus r397 manifest entries, copies and actual originals. No recursive evidence copies were made. Initial commentary incorrectly described the README check as stale metadata; that was explicitly corrected when the absent-size-field cause was identified.

read-attempt1.py exited 1 with KeyError 'id': queue uses mathdb_id. No corpus statement was read before this assignment check failed. Corrected read.py verified exact assignment/disjointness, then extracted only the fifty assigned normalized records. Native corpus iteration decoded other rows solely to filter IDs; no other-active-reservation statements were displayed, retained or scientifically investigated.

An early filename search over Dev returned too many AGENTS paths and was truncated; applicable ancestor instructions were then read through exact paths. A later display of accepted-family/history summaries was truncated; it was not treated as full historical review. All 39 accepted-family scopes were subsequently displayed in bounded compact form, and exact assigned-ID matching was performed over full r304 history in memory. No exact assigned-ID match was found. This is not live or exhaustive semantic dedup clearance.

No new network failure occurred. Three allowed public PDF requests returned 200. Zero MathDB or AIM requests, zero Google/GitHub API/raw/codeload/diff/ScienceDirect/preview/browser/account/message/publish/upload operations, no TLS bypass or denied-route retries. Inherited AIM hostname-validation failures were respected without retry. Search leads were not treated as proof bodies. Original AIM source/version gaps and missing current proof-registry checks remain HOLD.

No qualified brief, theorem, counterexample, complete dependency audit, accepted result, count change, Lean or manuscript. Existing endpoints, helper constructions, low-dimensional instances and assumption repairs receive zero credit. 9 additional /39 total /next40 unchanged.
