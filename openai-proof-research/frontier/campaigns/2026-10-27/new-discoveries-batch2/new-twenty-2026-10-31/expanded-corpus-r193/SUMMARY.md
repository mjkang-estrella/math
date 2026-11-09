# r193 research handoff

No qualified new MathDB solution and no accepted credit. This is a bounded investigation, not a claim that all 20 questions have been resolved or cleared for novelty. The lane contains exactly 20 ID-keyed dispositions in `results.json`.

The most useful prior-art finding is the April 2026 refutation of the tower-of-cubes conjecture (326345): Jabal Ameli, Nederlof and Wang, arXiv:2604.05661, Theorem 3.4. The primary proof gives a 34-element poset with 260553 ideals and 131576429145341435860520294400 linear extensions, beating the tower with 262143 sets and (17!)² chains. Adding arbitrary missing sets reaches the exact required cardinality without losing chains. This is published prior work, not a lane discovery.

Other firm dispositions are the published order-8 incomparable trees (325169), Liu's Alexandrov eigenvalue bound (325918), Brewster–Moore Lemma 4.12 on eventual odd-cycle mixing (381235), and the source's explicit Four Colour Theorem equivalence (324843). The Grigorchuk nonamenability target (325395) is subsumed by the source's Schreier/property-(T) implication and the later Aut(F_n) theorems for n ≥ 5. Directed-star inducibility (322882) has a published all-k theorem; its literal stability wording also conflates density and optimal part proportion. No new uniqueness theorem is claimed here.

Three tempting literal refutations have zero credit: 324899 has the inequality direction inconsistent with the source's own shortest-occurrence argument; 322856 requires an integer in (b,b+1) when a = 1 despite its own printed data; 324812 quantifies over constants smaller than the elementary lower bound chi_s ≥ average degree. For 361148 the earlier fixed-embedding claim was explicitly retracted by the source, which now quantifies existentially over embeddings. Finite graphs cannot refute the intended infinite bounded-distance assertion.

## Sustained finite route: 322924

The source's cycle verification stops at n = 12. Its exact Hall criterion reduces even-cycle and path replication feasibility to checking every subset of base vertices. I implemented both a literal subset checker and an independent threshold dynamic program, crosschecked on 1899 bounded inputs.

Exhaustive positive weight-vector enumeration, with only reflection and cycle-minimum symmetry reductions, reproduced rho_R(P_6) = rho_R(C_6) = 14 and rho_R(P_8) = rho_R(C_8) = 23. The respective vector counts tested are 1099, 700, 196991 and 119402; these include every smaller total and stop at the first feasible vector at the reported minimum. The independent equivalence to graph semantics uses the source's Hall theorem and perfection; no Lean bridge has been proved.

Structured searches at n = 14 and n = 16 push beyond the cycle verification range. At n = 14, 2914097 proposals at total 65 found no feasible cycle vector. At n = 16, both cycle and path total-87 vectors were found. The cycle vector passes all 65535 nonempty subset checks; every single-edge cut of that particular cycle vector fails, but a different path vector of total 87 exists. Therefore this does not refute equality. Further fixed-sum descent logs are retained. All stochastic failures are bounded non-findings, not lower bounds.

The decisive missing ingredient is an exact lower bound for a path minimum beyond the source's cycle range, or a new full-scope structural argument. A certificate merely beating a printed upper bound is insufficient. See `CANDIDATE.md` for the rejected diagnostic lead.

## Coverage and limitations

All 20 literal corpus lines, including their newline, were preserved with one-based locations and chunk/raw/statement hashes in `extracted.json` and `raw/`. Historical prose/results/ledger searches found no substantive old target disposition; the two exact-ID matches were this lane's launch record. Campaign ledgers were read and copied read-only as evidence; shared files were not changed.

Every advertised arXiv version was fetched with a distinct receipt. Selected conjectures, definitions and neighbouring theorem/proof bodies were reviewed; downloading a version does not mean every proof in it was read. VOR discovery and access are incomplete for several parked targets. The DOI route returned 403 and was stopped. EJC versions and the accessible mixing manuscript were fetched directly. `results.json` states the actual review depth and remaining gaps.

The GitHub screen used exactly eight spaced repository queries, all returning no repositories. Lean Pool HEAD was fetched using `/commits/HEAD`, followed by `projects.yml` and all candidate files at that SHA. Complete Omega D5/Problems and OpenAI preprints path listings were retrieved separately after recursive root listings proved truncated. Exact query/status/head/screen evidence is in `outputs/registry-screen.json`; path screening is not proof-body reading and does not establish global novelty. No prior public proof was independently certified absent.

The deep targets 326223, 326269, 326596, 326700, 356170 and 381159 were parked with source-backed scope reasons. No general-drawing generator for 326856 or exact higher-dimensional rigidity enumeration for 365224 was completed. These are explicit coverage gaps. This pass also does not meet the brief's requested several-hour research depth or complete VOR review for every target; it must not be represented as that exhaustive pass.

Numerical work used the lane-local wrapper: two CPU affinity slots, CPU 120 seconds, wall 140 seconds, sampled process-group RSS limit 6 GiB, and MALLOC_ARENA_MAX=2. Logs are retained. The initial SciPy approach failed because NumPy was unavailable; nothing was installed. One sequencing lapse occurred: the first replication stochastic job was launched before the previous tower job's completion had been explicitly confirmed. The overlap duration was not measured; both used about 13 MiB sampled RSS and completed within their caps. This fails the brief's strict confirmation rule and is disclosed rather than described as compliant. Subsequent numerical jobs were started after confirmed completion. No Lean invocation was run and no dummy endpoint or Lean packet is claimed.

No git operations, child agents, browser tabs, uploads, external messages or author contacts were used. All created artifacts are inside this lane. Acceptance and independent review remain the parent's responsibility.

Final descent check: both P_16 and C_16 have independently subset-verified weight vectors of total 85 (`outputs/replication-descent-exact.json`). The cycle and path descent runs made 2420368 and 2108144 proposals respectively. Neither is a certified minimum. The two published EJC parts associated with 324899 were also fetched; neither retains the reserved decreasing-minimization conjecture. Liu's current PDF labels the Alexandrov theorem 1.5 (earlier versions label it 1.3).
