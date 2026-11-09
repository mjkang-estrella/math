# Failures and corrections (retained)
1. extract.py first run: `rg` is a shell function (not on PATH for subprocess) → FileNotFoundError; replaced by grep -rniFI.
2. Second run: uncapped grep output collected in memory → MemoryError under the 3G scope; fixed by streaming through `cut -c1-1200` (logs: extract-first-failure.log). History search is therefore line-capped (1200 chars) and bounded.
3. A first quick multipath Euler-characteristic computation was written to /tmp by mistake and deleted immediately; recomputed inside the lane (`scripts/defect_checks.py`).
4. yip_search.py first run: sympy unavailable under `python -I`; replaced by an own Rabin irreducibility test.
5. Lean: RLIMIT_AS=12GiB prevented thread creation (logs/lean-01-thread-failure.log); raised virtual cap to 64GiB with resident memory capped by systemd MemoryMax=8G.
6. Lean iterations lean-02..05 (deprecated tactics/lemma names, AdjoinRoot simp normal form, recursion from unfolding 5^8) and lean-v3-01..02 (decide stuck on Finset-of-Finset quotients; rewritten with Boolean incidence and proved bridges). All logs retained.
7. Omega API URL guessed wrongly first (404 Omega-Research/omega); corrected to the inherited the-omega-institute/trureturing receipt URL.
