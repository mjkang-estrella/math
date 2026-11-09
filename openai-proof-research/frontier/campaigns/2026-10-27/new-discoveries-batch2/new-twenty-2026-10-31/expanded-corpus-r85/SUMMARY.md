# r85 bounded investigation — no proposed credit

Counts are unchanged: **13/20 current, beyond 39 prior**. Exactly 20 ID-keyed dispositions are in `results.json`. No qualifying new Lean endpoint was found. No acceptance is requested. No Lean packet, strict rebuild, leanchecker run or local-declaration audit is claimed.

This is a **partial investigation**, not completion of the requested several-hour deep pass. In particular, global prior-art clearance, author-catalogue coverage for every ID, and bounded spatial covering/dome searches are unfinished. The source and search records should be retained for continuation rather than treating all 20 targets as exhausted.

## Useful outcomes

Seven targets should not receive new credit on this evidence:

* **341683:** authors' 2025 Lemma 13 proves origami-monoid finiteness for the original presentation via derived contextual commutation.
* **342179:** Cichomski–Petrov (2022) prove the independent coherent-opinions inequality. Their threshold t=1−δ gives exactly the reserved bound.
* **342633:** He (2021), Theorem 3.2 and section 4.1, proves the exact event-stationary MMPP SCV inequality, even with zero individual arrival rates. A complete stationary-energy proof developed here is recorded but is not new. The earlier authors' 2018 paper is withdrawn and was not used as the exclusion basis.
* **343051:** Nguyen-Dang–Wang (2026), Corollary 5.12, covers all normalized key polynomials. The ordinary-key layer extraction was checked in the primary body.
* **343052:** Zhang (2026), Theorem 1.1, covers every finite-variable normalized skew Schur polynomial, including zero cases.
* **345055:** Liu–Xu–Zhuang's finite-generation paper, Theorem 1.6, gives the exact reduced uniform/K-polystability equivalence for log Fano pairs.
* **345310:** routine application of Li–Zhou, Corollary 3.5: the pattern Hopf algebra is commutative and coalgebra-connected over characteristic zero, so it is polynomial. `ATTEMPTS.md` spells out why noncommutative presheaf multiplication does not invalidate this bridge.

These are bounded, source-backed exclusions. They are not seven new solutions. The other 13 entries remain parked or incomplete, with exact gaps recorded.

## Sustained routes

`ATTEMPTS.md` records the stationary-energy argument and its prior-art closure; the connected-Hopf specialization and its significance exclusion; and a complete ordinary truncated-binomial Lyapunov argument on the fixed positive integer k, b_n=n reading. The last route lacks final source-scope clearance and would face the routine-classical-framework exclusion even before Lean. It is not nominated.

The standard-map registry theorem was checked in the pinned primary introduction: it proves the large-positive-parameter tail, whereas **345911 asks all nonzero parameters**. It is not a full-scope exclusion. The continuous counterexample in the interval-map source likewise does not refute its separate C1 conjecture **347298**.

## Finite search coverage

Full outputs and limitations are in `outputs/search-coverage.json` and the individual search files. These are diagnostics, not kernel certificates.

* Prime sieve to 10,000,000: lower alternating-prime inequality at n=50..332289; all eligible consecutive prime gaps. No violation. The alternating-sum upper inequality starts outside this range and was not tested.
* All integers 0..1,000,000 tested for digit-specialness in every base that can contain all its digits. Finite enumeration cannot settle finiteness.
* Origami words: all 8,191 words through length 12 at degree 2; all 5,461 words through length 6 at degree 3. Congruence derivations are limited to those staying within the length cap and do not certify distinct monoid elements.
* All 32,768 completely multiplicative prime-sign prefixes through N=50; no infinite extension claim.
* 8,241 integer orbits for even k from −40 through 40 and n from −100 through 100; all eventually repeat within the 10,000-step cap. No claim of global Collatz periodicity.
* Exact binomial moments for k=1..20 and n=1..400. Four cumulative Lyapunov ratios per k retained.
* 593 exact rational-rate MMPPs of orders two and three; no SCV violation.
* 1,322 small coherent probability grids, testing all relevant rational δ thresholds; no violation. Arbitrary marginal weights are not exhausted.
* Every weak composition in 1..4 variables with total size at most 7: exact key coefficients, M-convex exchange and exact normalized-Hessian inertia; no violation. All 284 contained skew shapes with outer size at most 7 and at most 3 rows, in 3 variables, pass the same checks.
* All labelled graphs through order 5, with all simplicial complexes on those vertices enumerated as possible balanced CM witnesses. An additional NetworkX atlas sweep covers **all graph isomorphism classes through order 7**. All 57 distinct F2-CM flag f-vectors in that atlas have balanced F2-CM flag witnesses on the same vertex count. Their graph6 certificates are retained in `outputs/340460-atlas-search.json`. General characteristic and larger vertex counts are not covered.

No exhaustive realization search was implemented for continuous homothetic coverings or spatial domes. Finite samples of smooth dynamics or billiards would not decide metric entropy, closedness or ergodicity; no such sample is presented as coverage.

## Provenance, live registries and limits

`raw/` preserves the exact 20 corpus lines including newline. `extracted.json` includes one-based chunk line, chunk/raw/statement SHA-256 and literal statement. `history-matches.txt` retains actual historical search output, including assignment matches and numeric false positives. No substantive earlier ID/title review was located by that bounded search.

Live `/commits/HEAD` receipts were fetched for both registries. OpenAI HEAD is `4eaee87548250b2682affda7d05d947c05554bae`; its current root confirms the reused complete preprints tree SHA `3f56f68a176b4494c346091ea0a319651bc217ec`. Omega HEAD is `6e37b782cf6cfe60366783f4272ac2ab8645a3e6`. Its root-recursive listing was truncated, so complete **D5** and **Problems** subtrees were subsequently fetched and screened. No registry non-finding is claimed from the truncated listing. Registry path checks are not complete proof-body review or global novelty clearance.

All 19 distinct original source PDFs and relevant follow-up bodies are retained with dated URL/status/byte-hash receipts. Unversioned arXiv download bytes are identified by hashes and version headers. Follow-up searches and author catalogue receipts are bounded, not exhaustive. The Penaguião thesis URL returned 404; it was not counted as read. Two initial SymPy Boolean-handling failures and the corrected successful polynomial run are retained. Missing guessed paths returned 404; access-control bypasses were not attempted. No MathDB/Palomar denial retry was made.

Capped jobs use `scripts/limited.py`: affinity at most two CPUs, CPU 120 s, wall 140 s, sampled private-process RSS limit 6 GiB, address-space limit 12 GiB. RSS sampling is not a cgroup or transient-memory guarantee. Scripts set OpenBLAS to one thread. All jobs completed; no job was intentionally left running. Shared ledgers, historical reports and external services were not modified.

Run `python scripts/report.py` from any working directory to regenerate the ID dispositions, and use the recorded script command names with `limited.py` to replay searches. The atlas uses an existing read-only NetworkX vendor tree identified in its output. No dependency was installed or changed.
