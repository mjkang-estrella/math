# Independent adversarial review — MathDB 338258

Recommendation: **PROCEED to manuscript and root replay**, with the qualifications below. This is a review recommendation, not acceptance. Credit remains zero; root decides. Review date: 2026-11-03 UTC. No child agents, git operations, shared edits, uploads, messages to authors, or browser tabs were used.

Verdicts: **A QUALIFIED_PASS; B PASS; C PASS; D QUALIFIED_PASS; E QUALIFIED_PASS.**

## A. Statement fidelity — QUALIFIED_PASS

All source line numbers below count physical newline-separated lines, including form-feed characters within a line. They therefore agree with `nl -ba`, not Python `splitlines()`. `source-passages.txt` retains numbered excerpts from both input bodies.

The arXiv body, `../expanded-corpus-r126/sources/1801.07021v1.txt`, defines the binary Riordan matrix at lines 119–133, and Definition 2.2 at lines 138–149 gives adjacency as B(zg,f) + B(zg,f)^T. The journal manuscript `sources/riordan-journal.txt` has the same definition and line numbers. Vertices are 1 through n; binary coefficients are reduced modulo 2 before symmetrization. The proper Bell case has f = zg and g(0) odd, so the subdiagonal consists of ones. The witness has g(0) = 1. With zero-based i > j, its adjacency is [z^(i-j-1)]g^(j+1) modulo 2. This is an ordinary symmetric 0/1 adjacency matrix, and the kernel is over the reals, not over F_2.

Definition 2.9 at lines 285–291 in **both** bodies is explicitly a condition on the finite graph: its even-induced graph is null, and its odd-induced graph is isomorphic to the smaller graph for the same generating functions. It does not explicitly demand an infinite-matrix identity. Lemma 2.11 at lines 295–296 then gives g_(2j+1) = g_j modulo 2 without a truncation qualification. The cited [3] is *Riordan graphs I: Structural properties*. I fetched its actual body independently: `receipts/graphs-I.txt`, Definition 4.1 in Section 4.1, Lemma 4.4 and Remark 4.5 at lines 1958–1973. The finite definition and infinite coefficient characterization are both present there too. A finite principal graph cannot constrain an arbitrary unused coefficient, so the unqualified infinite necessity must be read as a family characterization, or with suitable finite truncation conventions. This is a source presentation issue that should be explained in the manuscript.

The supplied polynomial itself does **not** satisfy the infinite identity: g_7 = 1 whereas g_15 = 0. Nevertheless, the n = 15 graph is not exploiting this distinction. Set

    h(z) = sum_{e in {0,6,8,12}} sum_{k >= 0} z^((e+1) 2^k - 1).

Every nonnegative index is uniquely of this form with an even e. The coefficients satisfy h_(2j+1) = h_j, and h and the supplied g agree through degree 13. Thus G_15(h,zh) is exactly the supplied graph, and it belongs even to the infinite-family interpretation. This is an ordinary mathematical bridge; the archive proves the finite definition, not this infinite-series bridge. The graph also satisfies the stronger **canonical** odd-copy identity, not just abstract isomorphism.

The source's singularity definition is at arXiv lines 306–309. Lines 1722–1727 introduce X as an arbitrary zero eigenvector, with X_o taking 1-based odd indices. Lemma 7.6 starts at 1730, and Conjecture 7.7 at 1762. Journal counterparts are 1723–1728, 1731, and 1763. The preceding Theorem 7.5 (arXiv 1668–1720; journal starts 1669) specifies a block form of the matrix, not a preferred eigenvector. There is no restriction to a distinguished zero eigenvector. Moreover, this example has nullity 1: **every** nonzero zero eigenvector has nonzero odd part, so even an existential reading would not save the conjecture.

Formal semantics: `extracted/Core.lean:9–29` defines the polynomial and convolution and proves the polynomial coefficient bridge; lines 376–382 define `entry`, `sourceEntry`, and their equality. `extracted/Endpoint.lean:55–63` proves the literal Bell coefficient bridge. Lines 65–76 use real vectors, require a nonzero vector and exact zero matrix product, and select zero-based even indices, which are precisely source odd vertices. Lines 78–92 prove `Riordan.source_conjecture_false`.

Precision qualification: `SourceConjecture` is a sufficient specialization of the source universal claim, not a syntactically complete encoding of every integer formal power series and arbitrary odd-subgraph isomorphism: it quantifies over natural-coefficient polynomials and imposes the canonical odd-copy equality. Those restrictions **strengthen the hypotheses**, so refuting the restriction refutes the source conjecture under its finite definition. No unrelated matrix or mod-2 kernel surrogate is substituted. If root requires an infinite-series statement as the literal Lean endpoint, the archive does not contain that extra bridge; it must not be claimed to do so.

The candidate contradicts no checked proved result of the source. Independently, the stacked matrix D = [A_8; B^T] has rank 8, as Theorem 7.5 requires. B has rank 7, and B X_e = (-1,1,0,0,1,-1,-2,0), so both sides of Lemma 7.6's equivalence are false. Theorem 7.1's bounds read 0 <= 1 <= 1 here. Theorem 7.8's universal-zero-odd-space reading also has both sides false: nullity(A) = 1 differs from nullity(B) = 0. The refutation does not assume any of those theorems.

## B. Independent mathematics — PASS

My code is `scripts/math.py`, run with `python3 -I`; it uses integer polynomial convolution and exact `fractions.Fraction` row reduction. It imports no discovery-lane code. `math-witness.json` contains the complete lower binary matrix B(zg,zg), its symmetrized adjacency, all 15 integer entries of Ax, and the rational kernel basis.

Both finite io conditions hold. Ax is exactly zero. The rational kernel dimension is 1, with basis

    (-1,1,0,0,-1,1,0,1,1,-2,0,1,1,-1,1).

Its odd part is (-1,0,-1,0,1,0,1,1). Exact rational rank equals real rank because the matrix has rational entries and its nonzero minors remain nonzero over the reals.

I independently enumerated **all** prefixes in the infinite-recurrence family for every n from 2 to 15, without modular filtering. Counts at n = 2,...,15 are 1,1,2,2,4,4,8,8,16,16,32,32,64,64. There are no counterexamples through n = 14, and exactly one at n = 15, mask 44, precisely this witness. Higher coefficients cannot affect the graph. `search.json` and `logs/math.log` retain the coverage. This proves computational minimality for n >= 2 in that coefficient family, not a Lean minimality theorem.

I also searched the **literal broader finite definition**, allowing arbitrary odd-subgraph isomorphism, using my own degree-pruned exact bijection search (`scripts/finite.py`). Every binary prefix g_0 = 1 through degree n-2 was checked: 2^(n-2) prefixes for each n = 2,...,15, 16,383 prefixes total. The finite io counts are 1,1,2,2,4,10,20,20,40,36,72,72,144,104; counterexample counts are 0,0,0,0,0,1,1,6,5,4,4,2,2,3. Full records are in `finite-search.json`.

In that broader interpretation the smallest n >= 2 is **7**, not 15: g = 1+z+z^2+z^4+z^5 has identical adjacency rows at vertices 1 and 5. The vector (-1,0,0,0,1,0,0) is in its kernel. The odd subgraph is isomorphic to G_4 under the zero-based map (1,0,3,2), but not canonically identical. `finite-n7.json` gives a complete certificate. This is a warning against claiming unconditional minimality and against using arbitrary finite isomorphism to infer the source's infinite identity; it is not a proposed separately credited result. The n = 15 candidate survives the stronger intended family and avoids this twin mechanism. At n = 1 the isolated graph already has a nonzero odd kernel vector if the conjecture is read literally without its preceding n >= 2 context; this degenerate endpoint is not the submitted refutation's basis.

## C. Lean replay and audit — PASS

The proof archive SHA-256 is exactly `628b850b31e347ab2d395fa6c11474c4ea8765c1cbdb6cc051e1ed3d77b0d198`. Before extraction I checked all 21 members for absolute paths, parent traversal, backslashes and symbolic links; none are unsafe. `archive-check.json` records the member list. Only source and manifest files were extracted. No supplied olean was used.

`Core`, `Row0` through `Row14`, `Table`, and `Endpoint` were compiled in dependency order in `extracted/` with Lean 4.34.1, `-j1 -M3500 -DwarningAsError=true`. All 18 passed. `scripts/build.py`, `scripts/check.py`, and per-module `logs/build-*.{log,json}` and `logs/check-fixed-*.{log,json}` are retained. Leanchecker passed separately on all 18 freshly built modules.

The independently written `extracted/IndependentAudit.lean` inventories every declaration whose module belongs to that closure, including generated proof declarations: **398 total**. It rejects unsafe flags, partial definitions, missing bodies, `_unsafe_rec` suffixes, `implemented_by` attributes, `extern` attributes, and axioms outside the allowed three. All pass. Source scanning also found no forbidden proof mechanisms (`source-scan.json`). `logs/independent-audit.log:1182` gives the count, and line 1406 prints the endpoint axiom set:

    [propext, Classical.choice, Quot.sound]

I read the coefficient definitions, convolution bridge, matrix bridges, row/table structure, vector definition, finite io predicates and endpoint. The row proofs use ordinary exact arithmetic and coefficient lemmas. Audit metaprogramming is review tooling, not an axiom or premise of the refutation.

The trusted cache is read-only mathlib at `d13f23b723b8a846827a245b89c10fc7d3f11612`; its lake manifest hash matches the supplied pin. The Lean and leanchecker binary hashes match too (`pins.json`). This does not claim a rebuild of upstream mathlib. Root still performs the decisive fresh replay.

Each expensive child was restricted to two allowed CPUs, CPU 120 seconds, wall 140 seconds, MALLOC_ARENA_MAX=2, and monitored process-group RSS below 6 GiB. Final peak sampled RSS was approximately 2.54 GB; virtual address space was capped at 12 GiB to allow Lean's mapped cache. Sampling is not a cgroup hard RSS guarantee. Only one heavy process ran at a time. An initial 6 GiB **virtual** cap caused a mapped-file read failure; it was corrected to the stated RSS policy. An initial leanchecker launch lacked Lean in PATH; the corrected runs all passed. My first audit had type/namespace errors and the first broader finite search lacked `__file__`; their full failed logs are retained as `*-initial.*`. The first mapped-file error was overwritten by the successful Core rerun; its tool-output transcription is retained in `logs/setup-failures.txt`, so a complete original failure log is not claimed. These were tooling setup failures, not failed candidate proofs. No background process remains at handback.

## D. Prior art — QUALIFIED_PASS

Live searches and HTTP receipts were made on 2026-11-03. `receipts/web2.json`, `web3.json`, and `web4.json` retain the queries/results. Queries explicitly included Riordan graphs III, later spectral work, nullity, eigenvectors, Conjecture 7.7, corrections, and Pascal/Catalan graphs. No matching public refutation, correction, withdrawal, or Riordan graphs III body was located. This is a bounded search finding, not proof of absence.

The live [arXiv abstract page](https://arxiv.org/abs/1801.07021) lists only v1. The institutional accepted manuscript retains Conjecture 7.7; its actual cached PDF and body were read, rather than relying on the journal abstract. The publisher's final typeset text was not accessed. No denied Crossref, Semantic Scholar, arXiv search API or ScienceDirect route was requested. Search-engine snippets mentioning ScienceDirect were not treated as body evidence.

An independent OpenAlex query identified the journal work W2963094373 and retrieved its complete returned citing list: nine records, including a duplicate preprint/journal pair (`receipts/openalex-search.json`, `openalex-citing.json`, with HTTP/hash receipts). Relevant later actual bodies inspected were:

- [Diameter of io-decomposable Riordan graphs of the Bell type](https://arxiv.org/abs/1901.11156), Jung: `receipts/diameter.txt:92–96` repeats the finite definition; lines 168–182 give the A-sequence family and 13 diameter counterexamples. Those stated diameter properties do not give a nonzero odd kernel. This paper resolves a different conjecture, not 7.7.
- [Counting independent sets in Riordan graphs](https://arxiv.org/abs/2006.16579), Cheon, Jung, Kang, Kim, Kim, Kitaev, Mojallal: `independent.txt:161–163` defines io-decomposability, and lines 668–810 give independence results and the block decomposition. No odd kernel assertion or correction to 7.7 was found in the body.
- [Encoding labelled p-Riordan graphs](https://arxiv.org/abs/2009.01410): `encoding.txt:67–104` and 191–279 concern adjacency encodings and coefficient subclasses, not a zero-eigenspace theorem.
- [Oriented Riordan graphs and their fractal property](https://arxiv.org/abs/2009.01677): actual body saved as `oriented.txt`; its mod-3 skew-adjacency setting is distinct. No matching undirected real-kernel counterexample was located.
- [Families of Integral Cographs within a Triangular Array](https://arxiv.org/abs/2009.02770): explicit-example screen, not just title screening. `cographs.txt:80–115` specifies joins of two cliques with an empty graph; lines 646–678 specify their complements and characteristic polynomials, and 698–780 discuss Hosoya graphs, loops and isolates. The paper cites Riordan graphs but does not state those examples are proper io-decomposable Bell graphs. Its disconnected complements/looped or isolated examples do not supply this target's hypotheses. No stated-properties contradiction of 7.7 was found.

The source's own explicit eigenvectors were checked: Section 5 distinguishes the Catalan eigenvalue -1 vector from the Pascal eigenvalue 0 vectors. Theorem 5.6 has nonzero coordinates at **even** vertices 2 and 2^p; it does not already contradict 7.7. The earlier 2018 *Spectral properties of Pascal graphs* was located through its institutional record (DOI 10.1080/03081087.2017.1356261), but its full body was not independently obtained. This remains a literature limitation. The live October 2026 math.CO listing was also fetched; its two Riordan mentions concern arrays/polynomials, not Riordan-graph kernels. This is not a complete 2018–2026 listing audit.

Current public registry heads were checked: OpenAI/math is `4eaee87548250b2682affda7d05d947c05554bae` (2026-10-30), unchanged from the candidate screen. Omega is now `bbd7a670a08b1b14ca49992f2b3490462bed4f53` (2026-11-03). The comparison from the candidate's `65a253616c22829023b8ff1c09cf1d5e6a221cf6` covers four commits and three unrelated quantum/reference-filter paths (`registry-omega-diff.json`). The prior cached path screen had only a different Barry Riordan/Pascal determinant target. This bounds changes since that screen, not a fresh reading of the entire registries. No chronology-based priority claim beyond the retrieved evidence is made.

## E. Significance and exclusions — QUALIFIED_PASS

This is a substantive counterexample to the intended n >= 2, infinite-family-compatible conjecture, not merely a correction at n = 1 or an exploitation of arbitrary finite graph isomorphism. It is connected (all consecutive edges occur), has no identical adjacency rows, and has nullity exactly 1 with a nonzero odd projection. It is not even unlabelled-isomorphic to the 15-vertex Pascal or Catalan graph: their degree multisets differ (`classical-screen.json`). The failed conjecture concerned a real zero-eigenspace feature beyond the proved full-column-rank statement; full rank of D does not prohibit cancellation against B X_e. That cancellation is exactly what occurs here.

I found no source-internal proved theorem contradicted **by this candidate**, no existing resolution in the bounded literature search, and no routine classical example yielding its certificate. The separate finite n = 7 twin example exposes a definition/characterization presentation mismatch; it should not replace the n = 15 example or earn extra credit. The infinite extension above makes the n = 15 refutation robust to that mismatch.

Proceed with a manuscript that explicitly states the finite/formal scope, gives the infinite extension argument, avoids unconditional n = 15 minimality, and acknowledges the bounded prior-art investigation. Formalizing the infinite extension would strengthen the packet if root chooses that interpretation. Worldwide novelty, inaccessible publisher bodies, and a complete later-literature census are not certified. Root adjudicates significance and acceptance.

## Integrity and reproducibility

All 503 files under the discovery input lane were SHA-256-bound before and after. `inputs-before.json` and `inputs-after.json` are byte-identical; each has SHA-256 `79d3e69a9c78241e30b97e0ebe16654068bd72868ed9d2d0b23efb62162816a9`. `input-integrity.json` records the equality. This includes the requested summary, proof narrative, results entry's containing file, proof zip, formal files, outputs, logs, scripts, sources, and raw/338258.jsonl. No discovery-lane script was executed or reused. Review code, extracted builds, temporary directory and caches are lane-local. The reports and evidence do not modify any ledger or award credit.
