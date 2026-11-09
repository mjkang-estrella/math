# r66 investigator handback — 2026-11-01

**No qualifying new solution and no Lean endpoint are proposed. Zero credit. The accepted count remains 7/20 beyond the 39 prior results. Root acceptance is required and has not occurred.**

The lane contains exactly 40 ID-keyed dispositions in `results.json`, covering exactly `reservation.json`. Every literal statement was read and extracted from its original JSONL line, preserving the newline. `extracted.json` records the one-based line, full chunk SHA-256, raw-line SHA-256, and statement UTF-8 SHA-256. `raw/` holds the exact 40 lines. `outputs/validation.json` verifies key equality and retained hashes. All writes were confined to this lane; no git, shared ledger edits, agents, publication, external messages, or browser tabs were used.

## Main dispositions

Four claims are already resolved by their cited primary papers and are excluded from discovery credit:

- **370510:** arXiv:2509.18567 Theorem 1.4 gives F_3(27)=15, below the claimed lower bound 18; Sections 2–3 contain proofs and constructions.
- **371073:** arXiv:2510.18529 gives an explicit nonaffine permutation at n=23 with every cyclic shift of cycle type (1,22). The retained script independently checks this source witness.
- **371162:** arXiv:2510.23249 Corollary 2.3 proves the difference n/2+O(log^5 n), stronger than the recorded conjecture. The graph-component reduction and proof bounds were inspected.
- **371382:** arXiv:2511.06617 Corollary 6 refutes the cul-de-sac conjecture using explicit folds attaining Z(w)+1 and the flanked-word upper bound Z(w).

**370838** is excluded as an elementary bound defect, not submitted as a significant discovery. Its actual source quantifies over caterpillars. P_4 at k=1 gives 49/4>2. The source includes a purported proof, but it assumes the right inequality without justification. The required arXiv:2507.14568 lead was fetched first and its v1 and v3 inspected; no exact subsumption bridge from that lead is claimed.

**370867** needs a source-version warning: the latest Trail of Lost Pennies body explicitly withdraws the recorded global maximizer claim after contrary numerical evidence. This is not a rigorous refutation. No certified lambda_max separation was obtained.

**370463** has a material source mismatch: the supplied arXiv HTML body concerns noncommutative Floquet-Bloch theory. The stated Lamzouri conjecture was not recovered from that body. A bounded author/maximum search did not authenticate the missing source.

## Sustained mathematical routes

`ATTEMPTS.md` records the arguments and exact remaining lemmas.

- **371170:** exact rooted DP checks all 32,505 nonisomorphic trees of orders 4–16; R_n is a maximizer throughout. Independent literal subset enumeration validates the DP on every tree through order 9. Exact double-star comparisons extend through order 100 and length-1/2 spider comparisons through order 60. A weighted independent-set deficit identity isolates the missing sharp quantitative inequality. No full graph surgery or deficit proof was found.
- **371040:** the known switch-graph distance n minus alternating-cycle count does not extend directly to arbitrary orbital relations. Two-step switch simulation would lose a factor two, and greedy cycle splitting fails near the target for long-cycle relations. The required uniform double-coset factorization/closing lemma remains open here.
- **371211/371212:** clique hinges miss the degree-sum threshold by at least one; complete bipartite quadric obstructions also fall short; universal coning preserves the deficit. Source edge-count bounds already rule out the simplest Maxwell shortage route. No flexible graph meeting the source hypotheses was found.

The other 31 entries are parked with individual definition, scope, known-special-case and remaining-gap notes. This includes the source mismatch and withdrawn numerical lead. They are not novelty-cleared or asserted globally open.

## Source and prior-art evidence

Public HTTP receipts in `sources/*.receipt.json` retain UTC, URL, returned URL/status, byte count and SHA-256. Primary HTML was available for 34 of the 35 distinct assigned source URLs; the one HTML 404 (2510.00291) was recovered from the lawful PDF endpoint and text extracted. Version-specific v1 bodies were fetched for 2507.14568 and 2511.09718. For the latter, the v1 Palis statement was recovered and distinguished from the revised C0 generic-attractor results.

Live registry heads were requested strictly using `/commits/HEAD`:

- OpenAI/math: `4eaee87548250b2682affda7d05d947c05554bae`, unchanged. The inherited complete preprints listing was byte-hashed and reused.
- Omega: `ed4c3c8e2898438925aeba4e746916d5132d50a1`, commit timestamp 2026-11-01T19:19:37Z. New complete D5 and Problems subtree listings were fetched. Their hashes equal the r65 listings; D5 has 13,332 entries and Problems 1,634, neither truncated. None of the 40 IDs occurs in a path.

These are **path screens**, not exhaustive proof-body or deleted-history audits. `outputs/registry-screen.json` preserves the scope. Campaign history was searched by exact ID/title in prose and conclusion JSON and filtered for numeric boundaries; the only relevant matches were this reservation in the shared ledger. The unfiltered log contains many hash/numeric false positives, retained for transparency.

Additional dated arXiv API searches were made for nearly-independent sets, perfect-matching association schemes, and graph-rigidity degree sums. The first broad tree query returned unrelated entries and is not clearance; the corrected title query found the target and two 2026 follow-ups. Those follow-ups (2604.11813 and 2602.16272) concern count ratios and complement-count inequalities, rather than the average-size extremizer; selected theorem statements were compared, with no demonstrated subsumption. Search results are bounded and some are irrelevant. There was **no comprehensive later-paper search or primary-proof audit for every one of the 40 IDs**. No claim of worldwide novelty, exhaustive historical coverage or finished semantic recovery is made. General web/Crossref and MathDB denied routes were not retried.

## Reproduction and formal status

Scripts are under `scripts/`: extraction/history scan, source fetch/text conversion, registry refresh, targeted follow-ups, exact tree/family diagnostics, source-known checks, report generation and validation. Retained diagnostic logs are under `outputs/`. `trees.py` and `families.py` use the existing `/tmp/venv-r3/bin/python` with NetworkX; fetch/report/validation use system Python. Resource-intensive calls were run with CPU affinity to two CPUs, address-space cap 6 GiB where set, CPU 120 s and wall 140 s limits. No background jobs remain.

No new full-scope ordinary theorem survived the qualification gates, so no dummy Lean packet was created. Strict Lean rebuild, leanchecker and local-declaration axiom audit were **not run and are not claimed**. Any resumed endpoint must still meet all those requirements against Lean 4.34.1 and the specified mathlib pin. This handback supplies a bounded investigation and honest parked gaps, not a solution certificate.
