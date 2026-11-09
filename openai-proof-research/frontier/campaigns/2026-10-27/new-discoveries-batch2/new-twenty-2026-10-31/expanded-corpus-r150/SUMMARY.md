# expanded-corpus-r150 (Claude, reserve7): summary

Outcome: **no candidate**. This lane found no new solution that qualifies for credit and does not self-accept anything. All 20 reserved IDs have ID-keyed entries in `results.json`, each with exact corpus provenance (chunk, one-based line, chunk, raw and statement SHA-256), source version and receipt hashes, review depth, outcome, evidence and remaining lemmas. No Lean, lake, SAT or ILP was run. Every computation was a capped `python3 -I` process run one at a time through `scripts/limited.py` (2 CPUs, CPU 120 s, wall 140 s, sampled RSS cap 1.5 GiB, address space 4 GiB). Full logs and receipts are in `logs/`. The highest sampled RSS was about 167 MB.

## Provenance and history

- `scripts/extract.py` (copied from r59 and adapted) wrote `raw/<id>.jsonl` (exact raw lines including the newline) and `extracted.json`.
- The campaign-wide history grep for the IDs (`outputs/history-id-matches.txt`) and for the source arXiv IDs and titles (`outputs/history-arxiv-matches.txt`) found only index, queue and ledger-launch entries. The one related disposition is r131's exclusion of the sibling 341256, which comes from the same source as 341257.
- arXiv abstract pages and PDFs of the current versions were fetched with dated receipts (`sources/`). Version lists are in `outputs/arxiv-abs-info.json`. No 403 or 429 responses were met. TLS verification was never disabled.

## Settled or excluded (zero credit)

- **332446**: settled. Hakopian–Vardanyan (Adv. Comput. Math. 2019, arXiv:1807.08182) proved the corrected form under the Gasca–Maeztu hypothesis: a line is either unused or used by exactly C(s,2) nodes.
- **332627**: settled. Pagaria proved the complete-graph case (IMRN 2023), and Crowley–Proudfoot proved the general graph version (arXiv:2505.05324, 2025).
- **344134**: settled by the source itself. Fox–Pham–Zhao's Theorems 1.4 and 1.5 prove the Saad–Wolf characterisation.
- **348515**: settled. McGinnis (arXiv:2608.25891, first posted 26 Aug 2026, v4 3 Sep 2026) proves exactly the optimal colourful fractional Helly theorem for d-Leray complexes; it is that paper's Conjecture 1.6.
- **341638**: vacuous as printed, with a complete short argument.
  - The domain of f includes the empty set, so f(∅) has at least D ≥ 2 elements.
  - Condition (iii) with I₂ = ∅ forces f(∅) ⊆ f(I) for every I.
  - Since K > D, the set J* = {j₀} with j₀ ∈ f(∅) has fewer than ⌈K/D⌉ elements, and (iv) then fails. So no good relation exists.
  - The intended M = 2 version conflicts with the authors' own later result (ITW 2021, as summarised in arXiv:2202.12229): the scheme that Conjecture 1 was meant to prove optimal is not optimal for D = M = 2. The ITW 2021 paper itself was not retrieved.

## Finite searches (no counterexample; coverage recorded exactly)

- **335792** (Alishahi–Meunier fair splitting by q-stable sets; q = 3 is open, and Frick 2020 also leaves it undecided). Exact memoised checker, validated on the proved case q = 2 for N ≤ 11.
  - q = 3: every colouring up to reversal for N ≤ 13 (1,818,670 colourings at N = 13); N ≤ 21 with at most 2 classes; N ≤ 14 with at most 3 classes.
  - q = 5: N ≤ 15. q = 6: N ≤ 16.
- **344587** (Tomon's upper-half chain decomposition conjecture). An exact solver realised every dominated sequence for n ≤ 9 (n = 9: 724 sequences). n = 10 has 43,086 sequences, which is beyond the lane caps.
  - Observation: dominance by σ′ is exactly the Gale–Ryser condition for level-occupancy patterns, so the open part is realising those patterns.
- **344586** (Griggs 1988; this predates the 2012 rule). Every one of the 618 dominated sequences for n = 6 is realisable. n = 7 is partial, with no failures.
- **344227** (Fan's signed-circuit 6-cover conjecture). All simple graphs on ≤ 6 vertices with every signature up to switching: 3,563 flow-admissible instances at n = 6 and 119 at n ≤ 5. All have 6-covers. The code reproduces Fan's obstructions for k = 2 and 4 and for odd k.
- **336137** (permanent (1,1)-matrix conjecture; Bartnicki–Grytczuk–Niwczyk 2009 and Wong–Zhu 2011, so pre-2012). All 156 graphs on ≤ 6 vertices pass.
- **336854** (Szabó's tight-star conjecture). The open cases are k = 2 with c ≤ 9, and k ≥ 3.
  - Structural heuristic: by (P4), a triple whose three pairs are all aligned with a far point is collinear. So, given a "line plus bounded end gadgets" structure theorem, the non-aligned pairs cover H(B). That structure theorem is the missing piece.
  - Random path-plus-gadget metrics gave about 2,240 instances with exactly linear co-size (slopes 1 to 6). All are tight k-stars.
- **341639** (D-graph mother-vertex conjecture). Reduction: μ_ext is the number of initial strong components, and μ_int(Gᵀ) is a transversal number of reach-closures.
  - A violation needs a hypergraph whose private-vertex transversal number exceeds (2m + s)/D. Tuza-type bounds rule this out for D ≤ 4 in the natural architecture. It looks possible only for large D, through Alon-type random hypergraphs, and lower bounds there cannot be certified at a checkable size.
  - In about 50,000 random digraphs (D = 2, 3, 4, K ≤ 10), none satisfies the D-graph hypothesis at all.

## Parked without a finite route

- **332504**: necessity direction of a robot-universality characterisation.
- **338235**: "eventual" triviality with an unspecified n_q.
- **339497**: bounded χ for binary matroids.
- **341257**: explicit local moves for every n; the hexagon sibling 341256 was excluded in r131.
- **343527**: asymptotic, linear-size bi-clique.
- **346758**: depends on unknown R₂ of fans. The MathDB paraphrase "pendant edges" is wrong: the source's K̂_m is K₁ ∨ P_m. The formula is consistent with the known values for m ≤ 4.
- **347546**: analytic, ISP-strength.
- **359661**: Cohen–Havet–Lochet–Nisse; deep and structural.

## Remaining leads, ranked by Lean cost

1. **335792, q = 3.** A proof would be significant. The most plausible route is a Z₃-Tucker or alternation argument; my searches suggest the conjecture is true.
2. **344587.** A proof would realise Gale–Ryser level patterns through nested inclusion matchings in the upper half. Lean cost would be high.
3. **341639.** Either prove that D-graphs never exist (which would make the statement vacuous; this is plausible for small D) or build a large-D construction with a certified transversal lower bound.

No Lean packet: there is no endpoint.
