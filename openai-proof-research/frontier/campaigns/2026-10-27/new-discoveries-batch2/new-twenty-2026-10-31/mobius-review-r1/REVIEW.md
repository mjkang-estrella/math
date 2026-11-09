# Independent adversarial review: MathDB 339235

Recommendation: **HOLD**. This is a valid, independently verified counterexample at n = 6, with a successful independent Lean replay. I did not find an earlier positive result for an even-parameter Möbius ladder. However, Gate C is not cleared. Root alone decides acceptance; no credit is awarded here.

Review date: 2026-11-05 UTC. All paths below are relative to this directory unless prefixed `../expanded-corpus-r246/`. This review used no child agents, git operations, external messages, browser tabs, or discovery-lane executable scripts.

| Gate | Verdict | Reason |
| --- | --- | --- |
| A | QUALIFIED_PASS | Exact arXiv statement and MathDB match; journal indexing preserves it with new numbering, but full journal retrieval failed. |
| B | PASS | Own exact verification of M12 and M8, odd-cycle lower bound, and independent bounded larger search. |
| C | FAIL | Novelty clearance incomplete, particularly workshop slides and unexamined citation bodies. No duplicate positively identified. |
| D | QUALIFIED_PASS | M12 is distinct from an M8 arithmetic correction and from the accepted full-tree result; construction-comparison limits remain. |
| E | PASS | Fresh final-packet compilation, explicit-module kernel replay, and 19-declaration axiom audit succeed; endpoint negates the universal statement. |

## A. Statement fidelity

Authors are Gee-Choon Lau, Wai-Chee Shiu, and Ho-Kuen Ng. Title: *On local antimagic chromatic number of cycle-related join graphs*. The live arXiv submission history (`downloads/arxiv-abs/body:180–183`) contains only v1, 13 May 2018. I fetched that version independently, rather than assuming the discovery lane's version count.

The exact mathematical definitions in the source are: `f : E → {1, …, |E|}` is bijective; `f⁺(u) = ∑ f(e)` over incident edges; adjacent vertices have different induced labels; `c(f)` counts distinct induced colors; `χ_la(G) = min{c(f) : f is a local antimagic labeling of G}`. These are the source's mathematical expressions, with typography normalized, not an alternative notion such as total or distance antimagic labeling. See `downloads/arxiv-v1/text.txt:27–35,42–51` and the preserved excerpts in `logs/source-exact-excerpts.txt`.

The ladder definition has cycle `C₂ₙ = u₁u₂⋯uₙv₁v₂⋯vₙu₁` and additional edges `uᵢvᵢ`, `1 ≤ i ≤ n`, for `n ≥ 2` (`downloads/arxiv-v1/text.txt:453–454`). The exact conjecture is:

> Conjecture 3.2. For even n ≥ 4, χla(M2n) = 4.

Theorem 3.11 concerns odd n ≥ 3 (`:457–481`); M4 = K4 is explicitly separated (`:490`). The literal MathDB JSON line `../expanded-corpus-r246/raw/339235.jsonl:1` has precisely the same graph, even parameter, threshold and value. Its word “even-order” in the title does not replace the even-n hypothesis; both parities of n give even graph order.

The journal is *Discussiones Mathematicae Graph Theory* 41 (2021), 133–152, DOI 10.7151/dmgt.2177. Public search indexing of its PDF shows the same graph and conjecture, renumbered Conjecture 3.14, with odd case Theorem 3.12. This is secondary retrieval evidence of the primary journal text, not a complete independently downloaded journal edition. HTTPS retrieval from both www and bare publisher hosts failed certificate-chain verification; the web retrieval timed out (`downloads/journal*/`, `logs/fetch4.log`). TLS verification was never disabled. Consequently I cannot supply a complete journal-version diff or certify that no correction notice exists. The 2022 follow-up's live arXiv page also lists only v1 (`downloads/regular-latest/body:160–163`); its cached full body still asserts the even conjecture and the stronger M8 result. No examined later body withdrew the 2018 conjecture.

## B. Independent mathematics

My code is `scripts/verify.py`; its full exact output is `logs/math-verification.json`. It independently builds the cycle-plus-antipodes edge set, checks distinct undirected edges, checks the full label permutation, computes incident sums, and checks every edge and color count. It does not import discovery code.

For n = 6 the labels are

`17 13 7 8 3 15 6 18 4 5 12 2 | 10 1 9 16 14 11`.

The sums, in vertex order 0 through 11, are

`29 31 29 31 25 29 31 25 31 25 31 25`.

For n = 4 the labels are

`11 2 9 12 5 10 6 8 | 3 7 4 1`.

The sums are `22 20 15 22 20 22 20 15`. Both labelings are bijections, are proper at every edge, and have exactly three sums.

For every even n ≥ 4, the cycle path 0,1,…,n plus the antipodal edge back to 0 is an odd cycle of length n+1. Thus χ(M₂ₙ) ≥ 3. Each local antimagic labeling gives a proper coloring, so χ_la ≥ χ ≥ 3. Combined with these witnesses, χ_la(M12) = χ_la(M8) = 3. The lower bound is ordinary mathematics; the Lean endpoint needs only the upper bound to refute four.

I independently implemented a deterministic-seeded randomized proper-coloring/label-swap annealer (`scripts/search.py`). It searches n = 8 and 10 for 15 seconds each. Neither run found a labeling; best within-class variance scores were 7 and 14 after 3,697,500 and 3,425,000 swap trials (`logs/search.log`). These are bounded failures, with no claim of exhaustive coverage or a general even-n result. A preliminary C version was not run because no compiler executable was available; see `logs/search-failure.txt`. The Python search replaced it.

In the 2022 source `../expanded-corpus-r246/sources/regular-2022.txt:339–368`, Theorem 2.4 claims every cubic graph of order eight has value four. Its proof prints `2x + 3y + 3z = 132` at line 354 and uses that total in subsequent case restrictions. A cubic order-eight graph has twelve edges, so the correct total is `2(1+⋯+12) = 156`. The M8 witness has the size-two class of sum 15 and two size-three classes of sums 20 and 22: `2·15 + 3·20 + 3·22 = 156`. This is a substantive invalid case reduction, not just a harmless isolated typesetting error. M12 is outside that finite theorem's scope.

## C. Prior art: clearance not established

All HTTP bodies and immutable receipts are in distinct, initially empty `downloads/<request>/` directories. `scripts/fetch.py` records URL, UTC time, final URL, status, headers, SHA256 and failures; blocks denied hosts and denied redirect destinations; does not disable TLS or retry forbidden responses. I did not directly query Crossref, Semantic Scholar, arXiv search API, ScienceDirect, or DBLP. Search-engine results sometimes mention those services; those entries were not used as primary evidence. Earlier search queries are described here; the last broad query result is preserved fully in `logs/literature-web-final.json`.

The independent screen included exact source title, both Mobius/Möbius spellings with local antimagic, even M2n, counterexample, Gallian, Lau workshop 2020, and Haslegrave. No positive earlier three-color labeling for an even n was located. This negative search result is bounded evidence only.

Concrete body checks:

* Haslegrave, arXiv:1705.09957: Theorem 12 (`downloads/haslegrave/text.txt:503ff`) establishes existence of local antimagic labelings. It does not bound the color number by three, so does not resolve the ladder conjecture.
* Arumugam, Premalatha, Bača, Semaničová-Fenovčíková (2017), DOI 10.1007/s00373-017-1758-7: the live Springer HTML includes theorem/proof bodies, preserved in `downloads/arumugam/`. The extracted text has no Möbius/ladder occurrence. Its basic cycles, friendship graphs, wheels and join results do not directly give a three-color labeling of the cubic M12. This is a body screen, not merely an abstract screen.
* Lau–Ng–Shiu, *Affirmative Solutions*, arXiv:1805.02886: independently downloaded body, no ladder determination located; the join lower-bound discussion is not the even-ladder question.
* Lau–Li–Ng–Shiu, arXiv:2009.01996: despite its broad circulant abstract, Section 2 restricts generators to units strictly below half the order (`downloads/approaches/text.txt:142–156`). The antipodal generator n of C₂ₙ(1,n) is excluded, and its degree contribution is one rather than two. Thus the advertised circulant sufficient condition does not automatically cover these cubic ladders.
* Lau et al., arXiv:2112.04142: inspected cycle/path join constructions and examples; no ladder result located.
* Lau–Shiu, arXiv:2203.06594: the full cached primary body is crucial adverse evidence about reliability, but it asserts four rather than an earlier refutation. Live metadata confirms only v1.
* Lau–Shiu, arXiv:2203.16359: Theorems 2.6, 2.9 and 2.10 (`downloads/lexicographic/text.txt:274,320–426`) require even degrees/Eulerian graphs or even degrees on both nonsingleton parts. M12 is cubic, so these hypotheses fail. Results on lexicographic blowups do not directly identify this ladder.
* arXiv:1906.10332 explicitly mentions Möbius ladders at `downloads/total/text.txt:1499`. The nearby Corollaries 3.19–3.21 concern total labeling or a join with K1, and identify CB₂ₖ with M₂ₖ only for odd k. They do not refute the even-k edge-labeling conjecture.
* The 2023 circulant-join paper (`downloads/circulant-join/`) studies joins with null graphs/cycles and unit-generator circulants. Its C12(1,5) example is 4-regular, not the cubic C12(1,6).
* The matrix-construction paper, BICA 107 (2026), 68–89, accepted April 2025 (`downloads/matrix-2025/`), constructs graphs of size 10k. M12 has 18 edges and M8 has 12. These are not instances of its stated family. The body has no ladder determination.
* Gallian's **28th edition, October 30, 2025**, was fetched from the official EJC route. Pages 246–248 (`downloads/survey/text.txt:11200–11330`) summarize local antimagic results, including the small regular-graph paper, existence theorem, and even-degree constructions. No even-ladder three-color result is stated there. A survey's silence does not clear all cited literature.

OpenAlex: independent DOI lookup identified W2802677295, metadata citing count 32. The citing-works filter returned **31 records**, all retained, not rounded up to 32 (`downloads/citing/`, `logs/citation-screen.log`). I screened their titles/locations and selected the relevant full bodies above. Several 2024–2026 graph-operation, join, and disconnected-family bodies remain unexamined. This is not an exhaustive citation-content audit, nor a complete bibliography of every Lau–Shiu paper.

Workshop slides: the public Scribd URL returned HTTP 200, but visible HTML contains metadata, an AI-generated description, navigation and subscription prompts, not the 50-slide mathematical body (`downloads/slides/visible.txt:1–45`). I did not attempt to bypass that restriction. The page does not authenticate its date/authorship sufficiently to replace the missing slides. A full authorized public slide copy and its actual ladder claims remain needed.

Current proof registries: Lean Pool HEAD was independently pinned to `01db1d7049cf9668bda1e9e106875ee1278b43e6`. The complete recursive tree is not truncated. Unlike the discovery lane's failed root-path request, I found and fetched the actual `LeanPool/projects.yml`, and every indexed `candidates/` file. Content screens found only unrelated Möbius arithmetic/geometry entries, no target/antimagic match (`logs/registry-screen.log`). Four repository API queries, spaced three seconds apart, all returned zero repositories; exact queries/receipts remain under `downloads/github-query-*`. Repository search is not GitHub code search. This cannot exclude a proof in an unindexed repository. This review's registry screen occurred after discovery; it does not repair the discovery lane's disclosed pre-investigation sequencing failure.

Gate C FAIL means missing novelty evidence, not a demonstrated prior refutation. Required next evidence: read the authentic full workshop slides; obtain the journal body/correction history through an allowed verified route; finish a documented content/scope screen of the remaining plausible citing constructions and later Lau–Shiu papers, including chronology. No acceptance packaging recommendation is justified before this is resolved.

## D. Significance and exclusions

The target is the 2018 all-even-n conjecture; n = 6 is not a parameter instance of a previously proved negative result in the examined sources. It is also not merely an M8 correction to the 2022 finite theorem. A finite exact counterexample can be mathematically significant under the campaign precedents. The M12 witness is not obtained by evaluating the printed odd-n formula: that formula is expressly for odd n and its half-integer expressions do not define an integer labeling at n = 6 (`downloads/arxiv-v1/text.txt:463–480`). Odd-parameter ladders are bipartite, while this witness graph is not.

I compared the source's printed-example categories: wheel deletions (Figures 1–3), generalized Petersen examples (Example 3.1), and the book/union constructions (Examples 3.2–3.3), using the source text and figure label extraction. G(5,2) has the wrong order; G(6,2) has triangles while M12 is triangle-free; G(6,3) in the source's degenerate case is not the cubic M12. Wheels/book examples have different degree structures. No printed M12 three-color witness was identified. I did not prove a universal nonderivability statement under arbitrary graph switches, rank-normalizations, or small modifications; the missing slide figures matter to that screen. The 2022 proof's printed triple case lists are tied to the incorrect total and do not supply this 18-edge witness by evaluation.

MathDB 354228 concerns local antimagic full trees, with leaf-based bounds and an acyclic graph family. M12 is a cubic graph without leaves and with odd cycles, refuting a distinct conjecture; it is not a tree-family parameter variant. Shared vocabulary alone is not a duplicate-credit reason. I recommend neither exclusion merely for being computer-found nor acceptance merely for being old and labeled open. On present evidence D is a qualified pass, subordinate to unresolved C and root's substantive-credit judgment.

## E. Independent Lean route and literal endpoint

Manifest selects **proof-packet-full.zip**, SHA256 `ffa01d95d108d91cc5f90638a1ef46fd9f76ac2cc743487a2c0b9644e2f7a2ea`. The older `proof-packet.zip` is SHA256 `2713eb3f36167f8fecbfee72cf59e102b565caedf5388a7100888821d0e5797c`; it was hash-bound but not mistaken for the final packet. My extractor `scripts/extract.py` checks exact allowlisted member names, every manifest hash, and extracts bytes into a fresh empty `replay/fresh/`. It never executes discovery scripts.

`scripts/replay.sh` independently ran, in sequence, Lean 4.34.1 with `-j2 -M3500 -DwarningAsError=true`, then **`leanchecker Mobius`**, then the strict Audit file. All returned exit code zero. Logs: `logs/build.log`, `logs/checker.log` (empty successful checker output), and `logs/audit.log`. Audit enumerates 19 local declarations, including generated auxiliaries. Only propext, Classical.choice and Quot.sound occur. Imports are Init only; mathlib is unnecessary. Prebuilt core oleans and the installed kernel/checker remain trusted; I do not claim an upstream rebuild.

Semantic inspection of `replay/fresh/Mobius.lean`:

* Lines 6–8 enumerate the general ladder family: cycle edges, then n antipodes.
* Lines 9–17 compute all incident sums and require a permutation of 1,…,3n with every edge proper. The permutation supplies exact list length, preventing default out-of-range indexing from contributing.
* Lines 21–24 define equality to the **attained minimum**, not existence of a k-color labeling alone. For nonempty attainable color sets, this is exactly equality of χ_la to k. A Nat-valued minimization function is not required for expressing its equality relation.
* Lines 25–34 certify the witness and refute minimum four. Lines 36–39 negate the entire universal even-n ≥ 4 statement, specializing it to n = 6.
* Lines 41–50 certify undirected simplicity, endpoint range/no loops, and all 144 ordered vertex adjacency pairs for the actual counterexample.

There is no missing mathematical bridge to the literal negation when the permitted general ladder-family encoding is used. A generic arbitrary `SimpleGraph` API is absent, and global simplicity/enumeration lemmas for every n are not proved, but the task permits definitions for the general Möbius family. The n = 6 bridge is kernel-certified, and inspection of the general definitions identifies the universal statement with the source. Nothing here claims the Lean packet proves exact value three or a general theorem for every even n. If root additionally demands an independently defined SimpleGraph minimization endpoint, that would be extra packaging work; it does not invalidate this family-based certificate.

## Integrity, resources and remaining limits

`inputs-before.sha256` bound 240 discovery inputs, including both packets, manifest, candidate, literal record, Lean source and all cached source/receipt files, before the independent replay and substantive review. All 240 verified unchanged (`logs/input-integrity.log`); `inputs-after.sha256` gives the final recomputation. The candidate matches the task's expected SHA256 `50badc8dae0b3a04375fbd318080e16614db838e028d3f1f548fa67f6d7ba6b6`.

Every local Python invocation used a real lane-local script path with `python3 -I -B`. `scripts/cap.sh` supplies a process-group RSS watchdog (6 GiB), taskset CPUs 0 and 1, CPU limit 120 seconds, wall limit 140 seconds, MALLOC_ARENA_MAX=2, and lane-local TMPDIR/cache paths. Heavy calculations/replays were serial. No heavy job is left running. Timing/RSS maxima were not separately sampled into a performance report; the enforcement driver is retained. No shared ledger or other lane was edited.

HOLD is specifically for novelty/source-comparison clearance and final root adjudication, not an objection to the verified witness or a failed Lean replay. No manuscript or acceptance is claimed by this review.
