# shrink-review-r1: independent adversarial review of MathDB 346320 (S1S2 counterexample)

Reviewer: Claude Opus 5.5 (lane shrink-review-r1), 2026-11-03. Brief: `TASK.txt` in this lane.
This is a review, not an acceptance. Root decides.

## Verdicts

| Gate | Verdict | One-line reason |
|---|---|---|
| A. Statement and rule fidelity | QUALIFIED_PASS | The counterexample is faithful to the printed definitions (eq. (11), (15)–(16), Theorem 4.4 with its witness, Theorem 4.5, Algorithm S1S2). But the authors' own released code, which the paper names as the real implementation, leaves out the S1 witness test. Under the code's rule the instance is confluent. |
| B. Independent recomputation | PASS | My own code confirms (y, x) ∈ P_A. Under all three execution semantics, S1S2 has exactly 2 terminal outcomes, with 3 and 4 vertices. C1, C1C2, C1C2C3 and S1 each give a single outcome up to isomorphism. |
| C. Prior art | QUALIFIED_PASS | No resolution found. Kobeaga's 2021 thesis (open BCAM copy, read) restates the conjecture as open Conjecture 3.22. The only citing works are the authors' own 2023 EJOR paper (arXiv v2 body read; it does not mention the conjecture) and one unrelated 2024 paper (title only). |
| D. Significance | QUALIFIED_PASS (weak) | It is a genuine refutation of the printed statement, and the statement was not withdrawn. However, the failure depends entirely on the global witness clause of rule S1. Without that clause, or with a fixed value-1 depot, no failure exists in any searched case. |
| E. Lean feasibility | QUALIFIED_PASS | Feasible and small, roughly 300 to 600 lines. The draft needs changes before it can serve as a faithful endpoint: heap-level semantics, ℝ instead of ℚ, decidability set-up, and the strategy quantifier. |

**Overall recommendation: HOLD.** The mathematics is correct and the certificate is tiny. Before any Lean effort, root should rule on one significance question (Section D):

> Does a counterexample that works only because of rule S1's global witness clause count, given two facts? First, the authors' own implementation never checks that clause. Second, the conjecture appears to hold, in every case searched, both for the clause-free rule and for the depot setting the authors had in mind.

- If root rules that the printed definitions govern and that this is substantive, upgrade to PROCEED_TO_LEAN, using the formal plan in Section E.
- If root treats it as a definition-versus-implementation artefact, EXCLUDE.

My own reading leans slightly toward the artefact view. I do not think the result clears the campaign's "mathematically significant" bar on its own merits. I give HOLD rather than EXCLUDE because the printed statement is unambiguous, and the witness clause is a necessary hypothesis of Theorem 4.4, not a typo.

## Input binding

- I hash-bound all 595 files under `expanded-corpus-r123/` before and after the review: `hashes/before.sha256` and `hashes/after.sha256`. **They are identical**, and the list file's sha256 is `92b19c7b7df5f982c8d481d6de2284340e4519a1ade10ad792edf05b4a820f7c` for both.
- The key input hashes, which are also in those files, are:
  - `SUMMARY.md` 1d9d0015…; `results.json` 0759e2e9…;
  - `candidates/346320/PROOF.md` 3fcdddcb…; `candidates/346320/lean/MathDB346320.lean` c0d7ed20…;
  - `raw/346320.jsonl` 065aec4e…;
  - `sources/2004.14574v4.pdf` c29b371f… (it matches its receipt); `sources/2004.14574v4.txt` c3ae0585….
- I did not run, import or read the r123 scripts. All computation here uses my own scripts in `scripts/`.

## A. Statement and rule fidelity

All line numbers refer to `expanded-corpus-r123/sources/2004.14574v4.txt`, the post-review version. v1 to v3 print the conjecture, Theorem 4.4, Theorem 4.5 and Algorithm S1S2 identically: conjecture at v1 1419, v2 1417, v3 1419; Algorithm S1S2 at v1 1736, v2 1734, v3 1733.

**P_A^G.** (7a) x(δ(v)) − 2y_v = 0 is at line 236. (7b) y_v − x_e ≥ 0 for e ∈ δ(v), (7e) 0 ≤ y_v ≤ 1 and (7f) x_e ≥ 0 are at 237–241. (11) P_A^G = {(y, x) : (7a), (7b), (7e), (7f)} is at line 297. The instance satisfies all of them; see B.

**Shrinking.**
- (15a) V[S] = (V − S) ∪ {s} and (15b) E[S] = E(V − S) ∪ {[s, v] : x(S : v) > 0} are at lines 334–335.
- (16a)–(16d) are at 336–343: edge values are kept; x[S]([s, v]) = x(S : v); unmerged vertices keep y; and y[S](s) = x(δ(S))/2.
- The algorithm works on the support graph Ḡ, as Table A.1 at line 1572 shows. Iterating (16b) gives, for any block, the sum of the original edge values, and iterating (16d) gives half the original boundary of the union. Both my code and the Lean draft use this closed form.

**Rule S1 (Theorem 4.4, lines 840–842), exactly as printed:**
- the hypothesis is x[u,v] = y_u = y_v = c;
- the witness condition is "If there exists a vertex w ∈ V − {u, v} such that y_w ≥ c". This is global: w ranges over all current vertices, and it need not be adjacent to u or v.
- Algorithm S1 line 7 and Algorithm S1S2 line 7 (lines 1740 and 1761) state the same thing over the current vertex set V̄.
- The witness is used in the proof at (31d), line 858, where y_w replaces y_v.

**Rule S2 (Theorem 4.5, lines 866–867):** x[u,v] > max{y_u, y_v}.

**Algorithm S1S2 (Appendix A.1, lines 1752–1772):**
- **Selection.** Line 2, "Select a vertex u ∈ H", is unspecified. The prose at line 1243 says "we draw one of its vertex".
- **Scan.** Line 5 is "for v ∈ N(u)" in an unspecified order.
- **Test order.** Line 6 tests y_v = c ∧ x[u,v] = c first. If that holds, S1 fires only when a witness exists. There is no fall-through: when the line 6 test holds and no witness exists, the else-if branch is skipped. That is harmless, because x = y_u then rules S2 out. Line 12 is the else-if for S2.
- **After a shrink**, "goto line 17" leaves the scan.
- **SHRINK/UPDATE (lines 1610–1634).** Line 4 is H ← H[S]. By eq. (17), that puts s into H only if S meets H. Line 21 then adds every neighbour n of s.
- **Prose discrepancy.** The prose at line 1246 says "we add the newly created vertex s and its neighbours", which always adds s. This disagrees with the pseudocode. I enumerated both readings (HEAP-P and HEAP-T in B), and the terminal outcome sets are identical.

**Meaning of "the graphs obtained … are isomorphic".**
- The text never defines it. The motivating sentence (lines 1416–1418) is: "the number of vertices and edges in the shrunk graph (the final result) is independent of the ordering of the considered rules and the shrinkable sets. This suggests the idea that the obtained shrunk graphs are isomorphic."
- So the objects are the final shrunk support graphs, and the variation is over orderings.
- The weakest reading is isomorphism of plain graphs. Isomorphism of graphs with y and x labels, or of weighted support graphs, implies it. Runs A and B differ in vertex count (3 versus 4), so they are non-isomorphic under every reading.

**Nondeterminism.**
- The conjecture is only meaningful if the algorithm is nondeterministic: under one fixed order on a fixed labelled input it would be trivially true.
- The source says plainly that orderings vary: "independent of the ordering of the considered rules and the shrinkable sets" (1416–1417); "does not depend on the different implementations of a shrinking strategy … e.g., by reordering the vertices in the heap" (1422–1425).
- The only fixed order anywhere is "V̄ ← sort V̄ decreasingly by y" in the separation drivers (EH line 1, at text line 1794; also lines 1820 and 1842). Ties are unspecified there.
- The thesis (line 4150) says ties are broken randomly in a related ordering.
- The C code (`graph.c` sort_nodes, REORDER == 0) breaks ties with `rand()`.
- No "lexicographic" convention appears.

**Does the counterexample survive under every fixed order?**
- Not for every labelling. Under any fixed deterministic implementation, a given labelled input produces one outcome.
- I simulated 12 fixed implementations: queue policies FIFO, LIFO and MIN-rank; both heap-update readings; initial order by index or by y descending with index tie-break. I ran each on all 720 relabellings of the instance.
- Every implementation outputs 3 vertices on some relabellings and 4 on others: FIFO gives 600 versus 120, and LIFO and MIN give 288 versus 432.
- So even a fixed implementation gives non-isomorphic outputs on isomorphic inputs, and the counterexample does not depend on an adversarial scheduler.

**Legal runs to termination.**
- Both runs are legal Algorithm S1S2 executions that end with H empty.
- My exhaustive heap-level enumeration (B) reaches exactly these two terminal partitions.
- **Equivalence of heap and rule semantics.** In general, heap termination coincides with "no rule applies":
  - Applicability of a pair changes only through (a) a merge that involves one of its ends, after which all neighbours of the new vertex go back into H, or (b) loss of an S1 witness. Values are never raised: S1 preserves y (Lemma 4.7, line 914), and S2 lowers it (Lemma 4.6).
  - So the invariant "every applicable pair has an endpoint in H" holds.
  - Conversely, every rule-level move can be realised by popping that endpoint and scanning the partner first.
  - The enumeration confirms that rule-level and heap-level outcome sets coincide on this instance.

**The fidelity qualification (why A is qualified, not a plain pass).**
- Line 1566 says: "The pseudocodes should be considered as illustrations of the implementations … The source code in C of the computational implementations is available at Kobeaga (2020)". The reference at line 1529 is gkobeaga/cpsrksec, Zenodo 10.5281/zenodo.3873356.
- I fetched that repository at commit `d702b9688722fde35040db62b29d3c50ba07c126`; files are in `sources/github/`.
- `src/cp/shrinking/s1.c` implements S1 and, under `par->srk_s2`, S2. **Its S1 test has no global witness check:**
  - The loop condition stops at the first edge with |x − c| < ε and |y_tail − y_head| < ε.
  - It then merges unless the partner is `graph->tail`. In `graph.c`, `graph->tail` is vertex 0, the OP depot, or the first vertex after reordering.
  - The tail can still absorb a partner.
- The later solver gkobeaga/op-solver at commit `992a2443…` (`src/cp/exact/bac/shrinking/s1.c`) has the same structure.
- The empirical observation behind the conjecture was therefore made with a witness-free S1. That matters for D.

## B. Independent recomputation

Scripts, all my own:
- `scripts/review_shrink.py` uses exact `Fraction` arithmetic and follows the source definitions directly;
- `scripts/variant_search.py` uses integer scaling;
- `scripts/variant_sample.py` and `scripts/instance_variants.py` are smaller helpers.

Every process ran alone through `scripts/cap.sh`, with:
- `ulimit -t 120`, `ulimit -v 6 GiB`, `timeout 140` and `taskset` to 2 CPUs;
- MALLOC_ARENA_MAX=2 and a lane-local TMPDIR;
- `/usr/bin/time -v` RSS logging.

Logs and receipts are in `logs/`. The peak RSS was 25 MB.

**Membership.** `in_PA` finds no failures, using exact arithmetic on (7a), (7b), (7e), (7f) and symmetry. Vertex degree sums are 1, 2, 2, 2, 2, 2, which equals 2y. The two edges at vertex 0 are tight at x = y_0 = 1/2.

**Run A** (`logs/review_shrink.log`):
1. S1 on {4,5} gives y = 1.
2. S1 on {1,2} gives y = 1.
3. S2 on {1,2,3} gives y = 1/2.

The final state has 3 vertices: {0} (1/2), {4,5} (1) and {1,2,3} (1/2). Its 2 edges are 0–{4,5} = 1 and {4,5}–{1,2,3} = 1. No moves remain.

**Run B:**
1. S1 on {1,2}.
2. S2 on {1,2,3}, giving y = 1/2.

The final state has 4 vertices: {0}, {4}, {5} and {1,2,3}. Its 5 edges are 0–4 = 0–5 = 4–{1,2,3} = 5–{1,2,3} = 1/2 and 4–5 = 1. No moves remain: {4,5} has no witness because the other values are 1/2.

**Exhaustive enumeration of all legal executions from this point:**

| Strategy | HEAP-P states / terminals / vertex counts | HEAP-T | RULE | iso classes (weighted, plain) |
|---|---|---|---|---|
| S1S2 | 42 / 2 / {3, 4} | 42 / 2 / {3, 4} | 8 / 2 / {3, 4} | 2, 2 |
| S1 | 54 / 2 / {4} | same | 6 / 2 / {4} | 1, 1 |
| C1 | 80 / 2 / {5} | same | 3 / 2 / {5} | 1, 1 |
| C1C2 | 64 / 1 / {6} | same | 1 / 1 / {6} | 1, 1 |
| C1C2C3 | 64 / 1 / {6} | same | 1 / 1 / {6} | 1, 1 |

- For S1S2 the distinct terminal outcomes are exactly runs A and B.
- The other four strategies are confluent up to weighted isomorphism on this instance.
- For C1C2C3 I used Theorem 3.6's hypotheses (i)–(iii) for |S| = 3. The printed pseudocode (Algorithm C1C2C3, lines 1691–1720; the condition is at line 1708) has an unbound t on line 15, and it omits y_w = c and the x[w,t] term. Figure 4 also misprints x(E(S)) as c instead of 2c. The pseudocode for C1 tests x[v,t] = c where Figure 4 tests x[t,u] = c; this is symmetric and immaterial.

**Cross-check of r123's search counts with my own generator.**
- n = 6 gives 2759 labelled half-integral inputs, matching r123.
- At n = 7 the classes with k = 1 to 7 value-1/2 vertices give 16260, 5550, 2112, 933, 480, 270 and 465 inputs, and k = 0 gives 52065. All match r123.
- Under the paper semantics (V1), there are 0 failures for n ≤ 5, 60 at n = 6, and 2160 + 430 at n = 7 (k = 1, 2). There are none for k ≥ 3, and none in the k = 0 class, which r123 never ran for S1S2.
- This independently confirms that n = 6 is minimal within the half-integral class.

## C. Prior art

Every route was public HTTP, with one request per route and no retries. I used no denied routes: no Crossref, Semantic Scholar, arXiv search API, ScienceDirect or Springer. Receipts are the `logs/fetch-*` files.

- **Kobeaga, PhD thesis, "Algorithms for large orienteering problems" (UPV/EHU, 2021).**
  - OpenAlex lists the record as W3149106527, with the ADDI copy (handle 10810/51029) flagged as not open access, and an open BCAM copy at hdl 20.500.11824/1254.
  - I downloaded it from bird.bcamath.org: `sources/thesis/thesis.pdf`, sha256 55aad24b…, 2302189 bytes. It was converted with pdftotext and read.
  - The thesis restates the rule and the conjecture verbatim, as Theorem 3.13 (Rule S1, with the witness, line 3419) and **Conjecture 3.22 (line 4308)**. The motivating sentence is at lines 4304–4307, and Algorithm S1S2 at line 6858.
  - There is no resolution, example or remark. Future Work (lines 6208 onward) does not mention it.
  - Chapter 4 (lines 4760–4765) repeats the exclusion of S2 for the OP.
- **The same group's later paper**, arXiv:2011.02743.
  - v2 is the latest version (abs page fetched: v1 on 5 Nov 2020, v2 on 13 Jan 2021). It was published in EJOR 2023 (10.1016/j.ejor.2023.07.034); the published body was not read, because ScienceDirect is denied.
  - I read the r123 cached v2 text (`sources2/2011.02743.pdf.txt`, lines 467–482). It excludes S2 "which leads to excessively aggressive shrinking strategies and hence to vanish violated CCs in some cases" and keeps C1C2 and S1 for the OP. "conjecture" and "isomorph" each occur 0 times.
- **Works citing the paper** (OpenAlex filter cites:W3023570891; 2 results): the 2023 EJOR paper above, and Arza, Le Goff and Hart, "Generalized Early Stopping in Evolutionary Direct Policy Search" (2024, ACM TELO). I judged the second unrelated from its title alone and did not read its body.
- The authors' code repositories (cpsrksec, last pushed 2020-06-04; op-solver, last pushed 2025-04-29) contain no tests or notes on confluence. op-solver still exposes `srk_s2` as an option.
- **Withdrawn, corrected or resolved?** Not withdrawn: the thesis restates it after the S2 exclusion was written. Not corrected or resolved in any source I could reach. S2 was dropped only for the OP joint SEC and CC separation, for an unrelated reason, and it remains an option in the code.

## D. Significance

**Points in favour:**
- The published statement is explicit, and it appears in four arXiv versions, the AOR article and the thesis.
- The refutation is exact, has 6 vertices, and is minimal in the half-integral class.
- The input is not degenerate: y_0 = 1/2 is interior to [0, 1].
- The point violates the SEC for Q = {0,4,5}: x(δ(Q)) = 1 < 2. So it is exactly the kind of LP point (in P_A but not in P_SEC) the procedure exists to process.
- Under the paper's semantics, failures also occur in 83 of 116 381 random points of the cycle polytope (averages of 2 to 4 random cycles, n = 6 to 9; `logs/vsample-s2.log`). The phenomenon is not confined to contrived points.
- It is not a known result, and the conjecture was never withdrawn.

**Points against, in order of weight:**
1. **The failure is entirely due to the global witness clause of Theorem 4.4.** I re-ran the complete half-integral search under two alternative semantics:
   - **V2, the authors' code semantics:** S1 without the witness, and S2 only when more than 2 vertices remain, mirroring `graph->n3v > 2`.
   - **V3, a fixed value-1 depot that is never shrunk:** the witness then always exists.
   
   Results:
   - In both, there are **0 failures** among all inputs for n ≤ 7: 2759 at n = 6, and 78135 at n = 7 for V2; for V3, every value-1 depot choice was run for k ≥ 1, and the last value-1 vertex was used for k = 0, which is no loss of generality because that labelled class is closed under permutations.
   - In both, there are **0 failures in 116 381 random cycle-polytope samples**, where V1 had 83.
   - On the instance itself, V2 has the single outcome {0}, {4,5}, {1,2,3}.
   
   So the refuted object differs from the algorithm whose behaviour prompted the conjecture: the paper (line 1566) calls its pseudocode "illustrations" and defers to C code that does not check the clause. It also differs from the depot setting the authors had in mind, cycle problems with y_d = 1. The conjecture as the authors actually tested it appears to survive. This is close to the brief's "wording or endpoint artefact" category, though not squarely inside it.
2. **The mechanism is routine.** A rule with a global side condition can be disabled by another rule that lowers values (S2, Lemma 4.6). This is the textbook way confluence fails, and the source supplies both ingredients.
3. **The conjecture is a heuristic observation drawn from computational tables.** Its stated purpose (lines 1422–1425) is practical.
4. **S2 was later excluded for the OP** (2011.02743, thesis Chapter 4), for a different reason. This lowers its practical weight. It does not amount to a withdrawal, because the thesis restates the conjecture.

**Not applicable:** it is not a known result, it is not a degenerate boundary input, and the strategy was not formally abandoned.

**Recommendation for D:** QUALIFIED_PASS (weak), with low significance. Root should explicitly decide point 1 before any Lean investment.

## E. Lean feasibility (draft assessed without compiling)

File: `candidates/346320/lean/MathDB346320.lean`, 150 lines, sha256 c0d7ed20…, marked UNCOMPILED.

**What is right:**
- `InPA` (lines 29–33) encodes (7a), (7b), (7e) and (7f) on K_n, with a symmetric, loopless x.
- `X` and `Y` (lines 41–48) are the iterated (16b) and (16d) in closed form, with singletons keeping y as in (16c).
- `Move` (lines 51–55) matches S1, including the global witness over vertices in other blocks, and S2. It also requires adjacency, 0 < X.
- `shrunk` (lines 78–81) is the plain support graph on representatives. Plain-graph non-isomorphism is the strongest negation, since it implies every labelled or weighted reading.
- The labellings check out by hand: A1 = merge id 4 5 gives [0,1,2,3,4,4]; A2 gives [0,1,1,3,4,4]; merge A2 1 3 gives LA = [0,1,1,1,4,4]; and merge B1 1 3 gives LB = [0,1,1,1,4,5]. The values agree with my computation.

**What a faithful endpoint still needs, with the risks:**
1. **Algorithm semantics** (moderate fidelity risk).
   - `Obtained` (line 71) is rule-level reachability plus "no move", not Algorithm S1S2's heap executions. PROOF.md admits that heap realisability is "argued, not formalised".
   - The cleanest repair is to model a state as (L, H : Finset (Fin n)) with a pop step, where the scanned neighbour is "any applicable neighbour". That is equivalent to "some scan order of N(u)", as argued in A.
   - SHRINK/UPDATE would be modelled with H[S] ∪ N(s), with terminal meaning H = ∅. The two explicit traces have 6 to 12 pops each.
   - Proving the heap and rule equivalence in general is not needed for the negation.
2. **The scalar field** (moderate fidelity risk). The source is over ℝ^{V×E}, but the draft uses ℚ. Either state the definitions over ℝ (or over any linear ordered field) and instantiate with casts, which means trading `decide` for `norm_num` / `simp [Fin.sum_univ_succ]`, or prove a transfer lemma.
3. **The strategy quantifier** (low risk). The conjecture quantifies over SRK ∈ {C1, C1C2, C1C2C3, S1, S1S2}. Refuting only S1S2 is logically enough for ¬∀, but a literal endpoint should name the strategy set, or at least state the S1S2 instance as the chosen SRK. Defining the other four strategies faithfully would add about 100 lines. Note the pseudocode typos in C1C2C3 described in B.
4. **Decidability and kernel cost** (moderate technical risk).
   - The `Decidable (Move …)` instance is built with `unfold Move; infer_instance` (lines 57–58). That leaves `Eq.mpr` casts, which the elaborator-side `decide` may not reduce.
   - Prefer `inferInstanceAs`, an `abbrev`, or `decide +kernel`.
   - `decide` over ℚ Finset sums on `Fin 6` is probably feasible but may be slow. A clean fallback is to scale by 4 into ℕ, as my scripts do.
5. **Graph and shrink definitions** (low to moderate fidelity risk). Root's fidelity reviewer may want a one-step shrink operation per (15)–(16), plus a lemma that iterating it equals the closed forms `X` and `Y`. That is about 80 lines of Finset sum algebra.
6. **The toolchain** (Lean 4.34.1, mathlib d13f23b…) is unverified here, because no Lean was run.

**Estimate:** 300 to 600 lines in total, all finite computation plus small Finset lemmas, and no deep mathematics. **Verdict for E: QUALIFIED_PASS.** It is feasible, but the current draft is not yet a faithful literal endpoint (items 1, 2 and 4).

## Notes on r123's PROOF.md accuracy

- Its counts, runs, final graphs and line references (Section 6.5; conjecture lines) all match my checks.
- It describes SHRINK/UPDATE as always adding s, which is the prose reading. The literal pseudocode uses H[S]. This is immaterial: the outcome sets are identical.
- It does not mention that the authors' C implementation lacks the witness test. That omission is the main new information this review adds.
- Its sentence "the heap always contains every current vertex that has not been examined since the last shrink next to it" is informal. The invariant in A is the precise version.

## Conduct

- I started no child agents, and wrote only inside this lane.
- I did not run Lean, lake, leanchecker, SAT or ILP.
- I made no git operations, ledger edits, uploads, messages or browser tabs.
- Each process ran capped and on its own, and no background job remains.
- I did not create an OpenAlex API key, though its notice suggested one, because that would need the user's email.
- Downloads are in `sources/`, with hashes in `hashes/lane-files.sha256`. PDFs were only converted with pdftotext.
