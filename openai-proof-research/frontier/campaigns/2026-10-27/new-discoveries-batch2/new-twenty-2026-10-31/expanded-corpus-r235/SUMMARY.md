# expanded-corpus-r235: bounded research handback

No qualifying new solution or literal Lean endpoint was obtained. Exactly 20 reserved records are keyed in `results.json`: 10 excluded for prior/source results and 10 parked. Nothing is self-accepted, and no campaign count or ledger was changed.

## Substantive finding, excluded

An exact finite search found a six-element counterexample to Jackson–Tanigawa's original valuation criterion (349809). On E={0,1,2,3,4,5}, prescribe circuits

{0,1,2,3}, {0,1,4}, {2,3,4}, {0,1,5}, {2,3,5}.

The diagnostic unique maximum is the cycle matroid of a square with a doubled diagonal, with 4 and 5 parallel. The computed valuation violates submodularity at A={0,4,5}, B={2,4,5}: v(A)=v(B)=2, v(A∩B)=2 and v(A∪B)=3. This is not a Lean-certified nomination.

A further literature search found Liwski et al., *Minimal matroids in dependency posets: algorithms and applications to computing irreducible decompositions of circuit varieties*, arXiv:2502.00799, Section 6, Example 6.5. It explicitly refutes the same original criterion with a seven-element example and introduces a refined valuation. The target is already refuted, regardless of the smaller witness. Stop this route; do not formalize it for campaign credit. See `sources/refined-prior.pdf`, its immutable HTTP receipt, and `matroid-witness-preliminary.json`.

## Exact diagnostic coverage

These computations are reproducible diagnostics, not kernel-certified mathematical endpoints.

- 349809: all labelled matroids on grounds of size 1–5, generated from basis exchange; every circuit subfamily was checked. Counts of matroids: 2, 5, 16, 68, 406. All corresponding feasible circuit families through five elements had a unique maximum and submodular valuation. At six elements all 3,807 labelled matroids were generated. All 59,220 feasible circuit families of size at most four were accumulated; 59,175 had a unique maximum and none failed submodularity. All 110,967 feasible families of exactly five circuits had unique maxima; 45 labelled failures were found. The valuation computation is dynamic programming on union masks, maximizing proper-sequence length for each union; it is not an unrestricted sequence-length truncation. Scripts: `matroids.py`, `matroid6.py`, `matroid6-extend.py`.
- 358860: exhaustive union-closed families with every member of size at least two on fixed labelled grounds of size 2, 3, 4, 5. Nonempty-family counts: 1, 11, 416, 243,785. All have at least two elements of frequency strictly greater than one half. No restriction to separating families or fixed full support was imposed. Script: `union.py`.
- 381752: every reduced Latin square of order 2–6 (counts 1, 1, 4, 56, 9,408), plus the first 120 lexicographic reduced squares at order seven. For each square enumerate every matching of size n−1 by its omitted row and injective column choice; compare its colour-count profiles against every weak composition of n−1. All profiles realized, no failures. Row/column/symbol permutations preserve this property, so reduction loses no counterexamples through order six. The order-seven sample is not exhaustive or random. Scripts: `matchings.py`, `matchings-extend.py`.
- 365728: every labelled simple subcubic planar graph of orders 2–6: 2, 8, 64, 768, 12,058. Both colouring assertions passed exact backtracking. On at most six vertices the only subcubic nonplanar simple graph is K3,3; its ten labelings are excluded at n=6. Graphs need not be connected. Script: `subcubic.py`.

## Primary-source exclusions

- 357056: Akman–Sissokho, arXiv:2607.23411, Theorem 1. The ambient affine/projective dimension shift is N=n−1, d=k−1; n≥2k yields N>2d. The successor explicitly identifies the conjecture.
- 368604: Murai–Rhoades–Wilson, arXiv:2505.24027v2, Theorem A and Theorem 5.1, already prove the reserved module isomorphism.
- 381915: Wang–Zhang, arXiv:2309.05903, Theorem 2.7; the current source itself explicitly reports the resolution after Conjecture 5.5.
- 381980: arXiv:2212.12588v2, Theorem 1.1, is precisely the two reserved initial values.
- 349818 and 349819: arXiv:2102.10155v1 settles both conjectures, including its explicit small-dimension verification paragraph.
- 349948: Johnston–Tait, arXiv:2302.11459, Theorem 3.1, proves the complete graph is the unique minimizer.
- 349953: Athanasiadis, arXiv:2302.00754, Theorem 1.1, proves the binomial-cone Eulerian transformation statement.
- 349555: Matuš–Ben-Efraim, Kybernetika 56 (2020), pp.934–936, explicitly report algebraic noncyclic Dowling geometries from Evans–Hrushovski. Their Definition 2.2 includes joints, as does the source DG definition. The original older construction body was not independently retrieved; this prior report blocks a novelty claim, rather than constituting a new refutation here.
- 349809: prior refutation described above.

## Evidence and limits

`raw/` preserves exact corpus lines including their newline. `extracted.json` records chunk path, one-based line, chunk SHA-256, raw-line SHA-256, and literal statement SHA-256 for all 20 records. `source-manifest.json` lists downloaded PDFs and their original receipts. All arXiv versions advertised by each of the 19 source abstract pages were downloaded, and converted to text. Downloading/converting every version is not a claim of reading every theorem and figure in every version; actual passages reviewed are specified per record. No potentially new counterexample survives the prior-result gate, so no full printed-obstruction comparison is certified.

`history-matches.txt` preserves the initial broad prior ID/title search. It includes large irrelevant numeric-substring and registry-blob matches; these are not evidence that the reserved records were previously reviewed. `inherited-review.json` records read-only inherited ledger/context hashes. Accepted and excluded families remain protected.

Current GitHub heads were fetched: Lean Pool `01db1d7049cf9668bda1e9e106875ee1278b43e6`; OpenAI/math `4eaee87548250b2682affda7d05d947c05554bae`; Omega `d574c5a7824082ef549f28b48ee0fa3a505dbfed`. Lean Pool's recursive tree is complete; the other two root recursive trees are truncated, so they cannot establish absence. Lean Pool's pinned `LeanPool/projects.yml` and all `candidates/` blobs were fetched. Six repository searches (Jackson/Tanigawa; Cui/Hu; source 2212.03100; Hocquard; nearly-ladder; Cachazo/Feynman, all with Lean) returned zero repository hits; this does not search every GitHub file. Relevant metadata/path screening does not establish a literal theorem audit. The complete Lean Pool metadata fetch and repository searches occurred after the first matroid/union-closed diagnostics, although a current path screen and literature search preceded them. This falls short of the task's strict metadata-first ordering, and is disclosed rather than retroactively claimed compliant. No candidate has novelty clearance.

The computational routes above were sustained through extensions, but this was not the requested several-hour, all-target exhaustive investigation. No signed-planar enumeration, general-design flow enumeration, nearly-ladder n=8 triangulation count, or n≥9 realizability-aware GFD enumeration was implemented. Their exact gaps are parked in `results.json`. Hard queen-completion complexity, oriented planar colouring, and unbounded-support attainment targets were not represented by misleading finite tests. These remaining breadth limits are material.

All successful numerical processes used the resource wrapper: at most two CPU affinities, CPU 120 seconds, wall 140 seconds, sampled RSS 6 GiB, and MALLOC_ARENA_MAX=2. Monitoring is not a cgroup/transient RSS guarantee. Full logs and resource receipts are retained. An attempted C++ compile could not start because g++ is unavailable; `union.py` supplied the successful computation instead. No packages were installed. All Python invocations used `-I -B`. No Lean process ran, no child agents were launched, and no background search remains. HTTP bodies and dated URL/status/hash receipts were preserved without overwrite. No disabled TLS checks or denied-host bypass was used.
