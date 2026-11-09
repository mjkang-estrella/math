# Independent adversarial review of MathDB 358158

Review date: 2026-11-02 UTC. Recommendation: **HOLD, zero credit pending root adjudication**. This is an independent review, not acceptance. The strict improvement is mathematically sound, and the extracted kernel replay succeeds. The decisive unresolved issue is prior art, especially the unread 2024 journal extension and a newly identified 2026 capacity paper. There are also endpoint-completeness and generated-declaration qualifications described below.

## A. Source and MathDB fidelity — QUALIFIED_PASS

I read the actual cached arXiv:2304.11403v1 body, not only the candidate summary, and the literal raw MathDB 358158 record. Definition 3 requires **every consecutive length-m window** of a longer sequence to contain more than m/2 letters from {T,C}. At length m this is exactly the Lean `TCDominant m`. The source explicitly uses consecutive subsequences. Complement is A↔T, C↔G; reverse complement complements the reversed word. Definition 4 requires maximality under inclusion, forbids a reverse-complement pair even if its members coincide, and is correctly transcribed in `IsGeneratingSet`. For odd m no self-pairs exist. Definition 5's `C_n(S)` and the Lean filter quantify over all windows, not a selected subset. Zero-based starts satisfying i+m≤n are equivalent to the source's one-based starts 1 through n−m+1. The proof recursion starts at n=5 and covers every n≥5; the vacuous short-word convention does not affect asymptotic rates.

Definition 2 uses a limit of normalized base-two logarithms. Theorem 6 identifies overall SSA capacity with the maximum of the generating-set capacities over all of S_m, not only dominant constructions or sets invariant under alphabet symmetries. I found no admissibility weakening in the witness. The source's argument around Lemma 2 is only an outline and contains loose polynomial-versus-constant counting language, but the candidate does not use it: a larger-rate valid generating set directly refutes the stated maximum claim. The source's “m-SSR” spelling and its m≥2 / 2<m conventions are irrelevant to the witness m=5.

The alphabet swap A↔T commutes with complementation and hence reverse complement, is bijective, and respects shifts/windows. I independently checked all 1024 words and that the swap sends the file's set to exactly the printed TC set with the listed 22 replacements. Thus Lean's `S5` is a differently oriented but valid witness. The Lean comparison set is the actual TC set, not AC or an approximation to TC. Formalizing the alphabet isomorphism is unnecessary for the existential refutation, though it would strengthen identification with the prose's specifically named witness.

The two negated universal endpoints really negate maximality for limsup and liminf; `conjecture1_false_m5` exhibits the particular m=5 witness and proves both strict inequalities and an eventual positive gap. The unrestricted natural-number quantification of the universal endpoints includes m=1, whereas the source starts at m≥2; inspecting the proof shows the contradiction is at m=5, so this is not an exploited domain loophole.

**Qualification:** the limit version `rate_limit_gap` assumes both `Tendsto` hypotheses. Neither it nor `conjecture1_false_m5` formally supplies those hypotheses. Therefore the packet does not literally contain a closed negation of the original limit-based assertion with existence of both limits included. The unconditional limsup and liminf statements and eventual gap are stronger than a numerical comparison, but they do not alone prove convergence. Ordinary convergence is easy here: splitting an admissible word into a prefix and suffix injects C_{n+k}(S) into C_n(S)×C_k(S), so log counts are subadditive; both languages have words at every length (constant A for the stored witness, constant T for TC). Fekete's lemma gives finite limits. This is a missing formal bridge, not an apparent mathematical counterexample to the result. Root should require that bridge if exact limit-based formal endpoints are mandatory.

## B. Ordinary mathematics — PASS for refutation; global optimum UNKNOWN

My `scripts/math.py` constructs the graph independently from word strings and literal TC counting. It implements its own strongly connected component decomposition and integer power iteration. For each component it obtains exact rational Collatz–Wielandt bounds min_i (Av)_i/v_i and max_i (Av)_i/v_i, then maximizes the component bounds. This computes rigorous enclosures rather than claiming that a finite decimal is an exact algebraic eigenvalue. The exact rational numerators/denominators are in `math-results.json`; both final widths are less than 10^−50. Rounded values are:

| Quantity | TC | Stored S5 |
| --- | ---: | ---: |
| Spectral radius | 3.24433345856344747002917909950021169525268615865655 | 3.24803759011152189238406374451999558198112463417677 |
| log2 spectral radius | 1.6979221100274076784 | 1.6995683291837003407 |
| Largest strongly connected component | 512 vertices | 504 vertices |

The witness also has eight singleton components. The finite integer lower certificate has minimum slack 0 and the upper certificate minimum slack 199781; nonnegative lower weights, a positive witness weight, and strictly positive TC upper weights all check. I separately parsed all three generated Lean trees: each has 1024 leaves in alphabet order A,C,G,T and matches the JSON membership/vector entries on its relevant domain. Thus the ordinary calculation and formal certificate concern the same set and data. Masked vector values outside the corresponding sets are irrelevant.

Direct exhaustive enumeration agrees with the independent dynamic program for n=5,6,7,8. DP continues through n=60. Selected exact counts:

| n | TC count | Stored S5 count |
| --- | ---: | ---: |
| 5 | 512 | 512 |
| 6 | 1664 | 1700 |
| 8 | 18176 | 18433 |
| 10 | 190464 | 192332 |
| 20 | 24560795648 | 25199434533 |
| 60 | 6842263000197440090314637312000 | 7349063540405072461822107728623 |

These counts are consistency checks; the proof of an eventual rate gap comes from the exact certificates, not a finite count experiment.

**Numerical correction:** the candidate prose's 1.699591 bits/nt is wrong. The gain is approximately **0.00164621915629266235 bits/nt**, not 0.00167. This does not affect the certified rational separator 3.245 < 3.2475. The source's Table I value 1.6980 is a coarse numerical approximation to the same TC rate, but is not the correctly rounded four-decimal value (1.6979). Its rounded binary spectral value 1.6222 explains the displayed 1.6980. Treat it as agreement in scale/construction, not exact four-decimal agreement.

The source already reports 1.7267, but explicitly for m=6 in Section V.B. It does not print the improved m=5 set or its value. Its m=4 discussion concerns even-length tie choices; it does not subsume this odd-length counterexample. I found no source-internal refutation.

My separate numerical screen (`scripts/local.py`) tries all 512 single reverse-complement-pair flips and 80 seeded random two-pair flips from the witness. None improves the spectral value at tolerance 10^−9 after 130 normalized float iterations. This is only local numerical evidence. The space has 2^512 orientations, and no exhaustive reduction or global upper bound was established. **Do not call 3.2480375901 the true optimum.**

## C. Lean audit — QUALIFIED_PASS

All seven original source files were copied byte-for-byte into a new empty `source-only/SSA5` directory. No candidate oleans were copied. I rebuilt Defs, Data, Checks, Bridge, Main, Endpoint and Audit with Lean 4.34.1, `-j1 -DwarningAsError=true`, then ran each module through its own `leanchecker` process. All final runs returned 0. Dependencies use the specified read-only pinned mathlib package cache; mathlib itself was not rebuilt. The first checker invocation failed because `lean` was absent from PATH; I corrected the runner and repeated the complete replay successfully.

The original audit checks all 198 local declarations' transitive axioms and finds only propext, Classical.choice and Quot.sound. My independent `FullAudit.lean` retrieves every constant type and `value? (allowOpaque := true)`, records type/body fingerprints and local references, and checks unsafe/partial flags and transitive axioms. Its final log includes every type. This is a programmatic audit of generated terms, not a claim that I manually read millions of lines of elaborated expressions. The manual source review covered all seven modules, including the transfer bijection, weight iteration, initial bounds and limiting estimates. Finite checks use `decide +kernel`; no native_decide bridge or added axiom was found.

**Nontrivial audit qualification:** `SSA.QT.get._unsafe_rec` has `isPartial=true`, `isUnsafe=false`, and no axioms. It is the compiler-generated executable recursion companion; `SSA.QT.get` itself has a structural `brecOn` kernel body. The full body and type of both are in `logs/flag-inspection.log`. No other local declaration has either flag. The type/body dependency graph of each of the four requested endpoints avoids that partial companion (see `declaration-dependencies.json`). This does not invalidate the kernel proofs, but a blanket “all generated declarations are nonpartial” assertion is false. If campaign policy bans partial declarations anywhere, rather than partial proof dependencies, root must resolve this explicitly or require a representation that avoids the generated companion. I am not waiving that policy.

Lean negative controls prove TC's limsup is not strictly larger than itself, and that inflating the TTACA lower-certificate coordinate to 10^20 violates its inequality. The independent Python mutation also fails exactly at TTACA. Negative and audit modules themselves passed strict Lean and separate leanchecker runs. The first full raw-expression audit aborted on the discovered partial flag; its compressed log is preserved. Later audits enumerate all 198 declarations rather than stopping at the first flag.

## D. Prior art — HOLD (decisive)

Search and access date: 2026-11-02. I used public HTTP/search without browser tabs, accounts, messages or uploads. The original denied IEEE journal route was not requested. No author was contacted.

Read evidence:

* The complete source preprint body and its live [arXiv listing](https://arxiv.org/abs/2304.11403), which still lists v1 only. This does not establish identity with the journal extension.
* [arXiv:2302.13714](https://arxiv.org/abs/2302.13714), actual PDF construction and theorem bodies, especially Theorems 3–5. It gives the 1.3031 rate at m=3, symbol-composition families, and a large-stem m≥3 log n+4 encoder. No inspected result refutes TC at fixed m=5. The latter scaling regime cannot be substituted for the fixed-m asymptotic rate.
* [arXiv:2307.00221](https://arxiv.org/abs/2307.00221), actual PDF body, Section III's dominant construction and Table I, and subsequent combined-constraint theorems. It reuses dominance and prints 1.6980 at m=5; the additional constraints reduce rates. No m=5 improvement is reported there. This v1 is not a substitute for checking every later publication version.
* Zhang–Wu, [On secondary structure avoidance of codes for DNA storage](https://pmc.ncbi.nlm.nih.gov/articles/PMC10749251/), actual public HTML body, Theorems 1–2 and conclusion. The main guarantee concerns m≥2 log2 n+2 and loop length at least 4, so it does not subsume this fixed-m limit. Direct CSBJ PDF access returned 403 and was not retried. The web connector returned a challenge on PMC, while the ordinary public HTTP request returned the article body; no challenge was solved or access control bypassed.
* [DBDS 2025 abstract book](https://www.jh-inst.cas.cz/dbds25/docs/DBDS_BOA_final.pdf), actual author abstract on printed page 47. It reports optimality only for m=2,3 and cites the 2024 journal work. This is useful evidence of continuity, but is an abstract, not the journal body.
* [arXiv:2407.16449v1](https://arxiv.org/abs/2407.16449), body introduction and Theorem 1.1 / Proposition 1.2. It supplies general forbidden-substring generating-function/capacity methods and explicitly recalls subadditivity/Fekete convergence. Its inspected results do not optimize reverse-complement-free generating sets or give this counterexample. The eventual 2025 journal version was not inspected.

Unread and material:

1. Wang–Chu–Ge–Zhang, *The Capacity of Secondary Structure Avoidance Codes for DNA Sequences*, IEEE TMBMC 10(2), 359–367 (2024), DOI 10.1109/TMBMC.2024.3396404, document 10517954. Title and author-copy/repository searches found no lawful body. OpenAlex metadata reports closed access and no repository full text; the dated response is saved. The author abstract cannot rule out a removed, modified or already refuted Conjecture 1. **This alone prevents novelty clearance.**
2. Ma–Zhang, *The Capacity of (m,d)-Secondary Structure Avoidance Systems*, ISIT 2026, DOI 10.1109/ISIT62367.2026.11653698. Search surfaced this relevant capacity paper; its actual body remains unread. Bibliographic/search summaries are leads only, not evidence that its results do or do not include the d=0, m=5 case.
3. Later journal versions of the inspected preprints and the 2026 survey *Propelling DNA-Based Archival Storage With an Algorithmic Mindset* were not cleared by body review. Search snippets do not provide clearance.

I found no actual body reporting the candidate value or a refutation, but this is explicitly **not** evidence of novelty sufficient for acceptance. Search queries and URL leads are recorded separately in `receipts/search-log.json`.

Live registries were queried only through `/commits/HEAD`. OpenAI/math remains **4eaee87548250b2682affda7d05d947c05554bae**. Omega's live head is **71b4592f31a0ce564acedcbee195fbd50f30bd8c**, newer than the supplied root-known 01b573fd9b691a4be3a8b0ecbb41b3311eda19b5 and the candidate's earlier 3e6639b6 snapshot. Its returned single-file change concerns an unrelated theory document. A HEAD response is not a cumulative diff or full registry scan; I cannot clear all intervening Omega content under this access scope. An initial request accidentally targeted teorth/analysis instead of the Omega repository; that receipt is retained and is not used as Omega evidence. Cached path screens do not close this live coverage gap.

## E. Significance — QUALIFIED_PASS intrinsically, conditional on novelty

This is a counterexample to a human-posed universal optimality conjecture. The first untested odd case m=5 falsifies the rule itself; it is not merely evaluating a parameter of an already proved theorem. Exact certificates and the transfer proof turn a numerical search into a substantive refutation. The absence of a proof of the true optimum does not weaken that refutation.

The significance is nevertheless modest. The corrected gain is only about 0.001646 bits/nt, the conjecture arose in a cs.IT preprint from m=3 brute-force evidence, and the source already treats generating-set choice as a computational optimization problem. A local annealing improvement using standard Perron bounds does not itself supply a general structural theory or a scalable code construction. Its human origin avoids the automatically-generated-conjecture objection, but human origin alone does not guarantee the campaign's significance threshold. I would regard a demonstrably new strict refutation as eligible for root's substantive judgment, with these qualifications, rather than reject it merely because the witness is computationally found or the gain is small. The unread journal extension and 2026 paper prevent an overall PASS now.

## Deliverables and next actions

`review.json` has the machine-readable per-gate verdicts. `source-only/SSA5` is the hash-identical extraction; review-only audit and negative-control modules are adjacent. `scripts`, `logs`, `receipts`, `prior`, `math-results.json`, `local-results.json`, `data-check.json` and `declaration-dependencies.json` contain the independent checks and access records. The runner imposes two-CPU affinity, CPU 120 seconds, wall 140 seconds, sampled private RSS 6 GiB, AS 64 GiB with a watchdog, MALLOC_ARENA_MAX=2 and lane-local TMPDIR. Sampling is not a cgroup or transient-memory guarantee. Initial setup and small read-only shell inspections are not individually watchdog-wrapped. No Java, git, ledger changes, publishing or child agents were used.

Before acceptance, root should obtain and compare the actual journal and 2026 capacity bodies, resolve the live Omega interval coverage, close the formal convergence bridge, decide the policy treatment of the generated partial companion, and correct the numerical prose. Global m=5 optimality need not be established. Credit remains zero. No acceptance or shared-state change is made by this review.
