# Preserved failures and limitations (r271)

## Mathematical
* No proof or refutation of the finite Swanepoel question. Conjecture k = 9 rests on finite search only.
* My intermediate conjecture "three triangles always witness non-c.s.c." (which would have given k = 9) is **false**: exact six-point counterexample in `exact-checks.json` / `logs/t_six.txt`.
* Topological Helly via triangle sets fails as stated: intersections of 2 triangle sets have up to 4 components and of 5 up to 8 (exact nerve computation).
* The near-symmetric model is a first-order derivation, validated on 392 + 112 exact instances but not proved for all small ε. The Hadwiger step needs a limiting argument when segments touch at shared arc endpoints; not supplied.
* The bounded-set transfer (Theorem T) is rigorous but only a reduction; it gives no bound.
* Lead 2 (Bergman Q6) and Lead 3 (Konyagin–Łaba) received source reading only, with no mathematics attempted.

## Computational
* `t_three.py` (exact exhaustive triple search) was killed by the guard's 210 s CPU limit (guard_exit −9) and then by a 200 s `timeout` (exit 143), without output. It was replaced by `t_three_fast.py` (float prefilter, exact confirmation). Logged in `logs/failures.jsonl`.
* `explore1.py` (2^(N−1) scale patterns at fixed factor 0.93) took 147 s. Its fixed 0.93 scale is not matched to δ_N, so its N = 11, 13 nulls do not count as evidence; `search_odd.py` replaced it.
* The first `t_six.txt` log was truncated by `cut -c1-300`; it was regenerated in full.
* The searches use rational approximations of regular polygons (denominators 10⁵–10⁹). Every certificate is exact for the rational set actually tested, not for the irrational ideal polygon.

## Access and protocol
* Semantic Scholar citations API returned HTTP 429 once and was not retried. OpenAlex reports 0 citing works for the published version; OpenAlex citation coverage is incomplete, so this is not clearance. No GitHub API/raw/codeload/diff/patch, ScienceDirect, Google, proxy, TLS bypass or browser access was used. Current public proof-registry heads were not obtained (inherited denied routes stay parked).
* Bergman's errata page (math.berkeley.edu) and the post-2004 Falconer-for-norms literature were not checked.
* Protocol deviation: I read the r268 files (SUMMARY, discovery, SCOUTING, FAILURES, progress, provenance, scripts) and the root STATUS before running this lane's freeze. SCOUTING, discovery, SUMMARY, FAILURES, check.py, the 1801.07238v1 PDF/text and the root STATUS were frozen immediately after (bound in `bindings.jsonl`). r268 progress.md and provenance.json were read but not frozen; nothing here relies on them. The primary 1801.07238v1 text was read only after the freeze and the fresh byte-identical refetch.
* Administrative files (AGENTS.md ×2, ledger.json, prior-campaign-context.json, root STATUS) are snapshots only and are not compared after writes.
