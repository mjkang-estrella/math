# Progress and reproducibility

29 October2026, worker r80, solo. Read ancestor/batch AGENTS, sources/upstream.json and catalogue introduction, latest ledger accepted/excluded/candidate entries, prior accepted families, NEXT current/historical relevant notes, r78 summary, r52/r77 duplicate sections. Shared state untouched. No agent children.

The initial broad filesystem discovery included unrelated Dev paths and produced noisy truncation; subsequent reads were restricted to the authorized research context. It performed no writes. Initial context concatenation also truncated; exact accepted scopes and candidate dispositions were subsequently extracted, with complete structured context preserved by audit.py.

Early filename-first searches used all campaign dates and .md/.json, including FINDINGS filenames. A later helper initially used rg defaults: under its inherited512MiB AS limit, its incomplete seven-file output was inadequate. Final audit explicitly disables mmap, uses one thread and --no-ignore, and checks rg return status. Final rg returns0/empty stderr,30 filenames and55 bounded matching sections. The incomplete filename list is preserved. The broad initial sections over giant catalogue JSON were noisy; final audit streams64KiB chunks and caps per-file excerpts.

Failed helper1: audit-failed1.py reads an entire giant matched JSON into memory and raises MemoryError under the mandated guard. Observed sampled peak341393408 bytes, wall0.299s, exit1. No limits raised; no output from that run used as clearance. Corrected audit.py uses bounded streaming; final guard audit.guard.json reports303755264 sampled bytes,1.977s, exit0. Successful historical intermediate audit before --threads1 was not sufficient duplicate clearance. No claim of complete registry audit.

check.py: exact DP n140, direct parking enumeration n<=6, source table n<=9, sum identity all rows; exit0, sampled peak14598144 bytes, wall0.399s. Finds stronger route obstructions(80,40),(62,30), no source-unimodality failure.

check-large.py: same independent finite recurrence extended to n500, not preference/permutation enumeration. Exit0, sampled peak123035648 bytes, wall61.866s. All rows sum to(n+1)^(n-1); no source-unimodality failure. Check-large-result.json retains modes and first stronger failures. This was a single bounded extension after discovering the invalid stronger invariants; no repeated larger sweep or capraise.

fetch.py: six legitimate public HTTP reads, all200, exit0, peak24858624 bytes, wall2.280s. Exact URLs/UTC times/SHA256 in http.json. No403/429/challenge was encountered; no retry/proxy/bypass. Read public repository page gives new HEAD11c6ddfe..., freshness HOLD remains.

Failed helper2: route_checks-failed1.py accidentally evaluates1**(-1) as float at k0 in the known parking-count factor. The floating result contaminates the nominally exact EGF check and eventually triggers AssertionError. Failed source and traceback/guard preserved. Corrected route_checks.py uses literal integer1 at k0; now all arithmetic is integral. Successful route.guard.json: exit0, peak12402688 bytes,0.0984s. It checks3280 Foata/standardization words,234 Riccati coefficients, exact obstruction integers, and artificial weighted-mixture valley. None is a full unimodality proof.

Every Python/helper experiment ran as `python capped_run.py python SCRIPT`; capped_run.py copied unchanged from r70. Child AS512MiB, process-group RSS512MiB, CPU210s, wall230s, sample40ms, BLAS/OpenMP threads1. Sampling cannot exclude unsampled transients. No cap raise. All jobs terminal at handback.

No PROOF.md: the substantive selected candidate is unresolved. The short screen-only6.3 ordinary argument is retained in discovery.md with routine eligibility exclusion, not promoted into a discovery or paper. No acceptance/count changes.
