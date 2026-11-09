# Expanded corpus r110: investigative handback

No qualifying new solution or Lean endpoint is proposed. Credit is zero for all 20 reserved IDs. No campaign counts or shared files were changed.

The main exclusions are substantive source checks:

- **375504:** the original v1 Riccati Conjecture 1 is proved by the current source's Theorem 2, equation (31). The entire five-step proof was read: componentwise balance, weighted Cauchy–Schwarz, simultaneous attainment, DARE/stability, and the intersection-component bridge. The lane also tested 31,872 numerical cases over every orientation of each unlabeled tree of orders 4 through 9 at two discount factors; this adds no discovery credit.
- **359747:** the current source explicitly retracts uniformity and supplies the two-clique/conic-at-infinity obstruction, acknowledging Steven Gortler. No new counterexample is proposed.
- **364032:** the exact minimax search reproduces a tie at C(8,8), but the source's own Ferris-wheel Table 6 already prints that tie, contradicting its Conjecture 10. This is a zero-credit source correction.
- **353371:** the wheel-product conjecture disagrees with the source's own W6 datum: 96/25 versus 96/26. No credit for this printed formula conflict.
- **340354:** the even-degree claim has a routine permutation-sign proof for n at least 4, with degree 2 directly checked. See ATTEMPTS.md. It was not promoted to Lean as a significant discovery.

The strongest unresolved routes received additional work:

1. **339514, switch map:** corrected coprime dinv diagnostics exhaust placement words of object length at most 10 (input rows at most 20), then sample 60,000 words at larger lengths with rows up to 200. No mismatch under the documented pair convention. Fixed points of Phi and noncoprime semantics remain unimplemented. The first diagnostic incorrectly filtered image pides; its failures are explicitly invalidated.
2. **358215, Petersen flow:** 100 seeded numerical optimizations in the full 12-coordinate cycle-space representation find squared norm ratio approximately 7/3, without an improvement. A global lower-bound certificate remains missing.
3. **371616, prefix reversals:** exact small-order group calculations and 54 sampled triples beyond the authors' n=100 range found no failed persistence implication. Beyond-range tests use SymPy's probabilistic Alt/Sym recognizer and are not exhaustive or Lean certificates.
4. **340474, wall crossing:** all partitions through size 12 were checked for nesting, followed by 50 initial partitions each at sizes 41 and 42 (beyond the source's size 40), totaling 27,050 and 29,150 completed wall steps respectively. No nesting failure. The size 48 run hit its CPU cap. The good-box semantic bridge remains unaudited, so these are diagnostics only.

Other exact or bounded calculations include all even-size compositions through size 22, principal permutation Möbius values through kappa_4, 45 coprime Ulam-sequence parameter pairs through integer value 100,000, source-known cage checks, cyclic Ramsey MILPs, and cactus-relation checks in the already proved rooted-forest subfamily. Exact scopes, failures and remaining lemmas are in the 20 ID-keyed entries of results.json and full logs.

## Provenance and limits

All 20 literal raw corpus lines, including newline, are retained in raw/. extracted.json binds one-based chunk lines, full chunk hashes, raw-line hashes and UTF-8 statement hashes. Each primary HTTP retrieval has a dated URL/status/SHA-256 receipt. All 20 initial arXiv HTML bodies were retrieved successfully. Additional original Riccati v1 and later related sources are retained.

Live registry heads were checked via /commits/HEAD: OpenAI/math 4eaee87548250b2682affda7d05d947c05554bae; Omega 4d32bc84e3a664b3d68e374b8dbd7828c3258966. Complete untruncated preprints, D5 and Problems listings were fetched. These are path screens, not proof-body clearance. Two relevant prefix-reversal non-generation bodies were read and do not establish this persistence conjecture.

Historical exact-ID/title searches were supplemented with source aliases. The cage question is the same as prior 349120 in r41; that inherited hold is preserved. Other same-paper questions are distinguished in outputs/history-source-aliases.json. The broad history grep has false numeric/hash hits; it is not evidence that those files technically reviewed these questions.

Not every requested finite search was completed in full semantics: general d-complete generation, switch Phi, wall-crossing good boxes, and several global/asymptotic problems remain open gates. There is no claim of a complete literature audit, all-registry-body review, worldwide novelty clearance, or a formal theorem. The hard complexity/algebra/modularity questions received source-backed dispositions, not inappropriate finite-instance claims. No dummy Lean packet was created.

## Reproduction and resources

Run scripts from this lane with `python scripts/limited.py NAME python scripts/SCRIPT.py [MODE]`. Full stdout/stderr is in logs/NAME.log; each completed managed call has a resource receipt. finite.py modes: gf, loopy, prefix. deep.py modes: flow, beyond. more.py modes: comp, mobius, ulam, ramsey. Standalone scripts: riccati.py, switch2.py, switch_sample.py, wall.py, cactus.py, cage.py. Initial switch.py is retained only to document its invalidated diagnostic.

Limits were two CPU affinity slots, 120 CPU seconds, 140 wall seconds, sampled 6 GiB process RSS and 12 GiB address space per managed call. Monitoring is process-based, not a cgroup/transient-peak attestation. Numerical libraries used preinstalled dependencies; no packages were installed. An unavailable g++ attempt failed before compilation; the Python composition calculation completed instead. The final runner also directs temporary files and bytecode policy into the lane. No Java, git, external messages, browser tabs, publication, uploads, shared-ledger mutations or child agents were used. No research process remains running at handback.
