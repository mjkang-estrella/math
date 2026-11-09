# Source, novelty and significance review r2: MathDB 355956 and 355701 (2026-11-01)

This is an independent review, **not** acceptance. Zero credit is claimed, and the root alone accepts. The Lean technical PASS for both IDs (fidelity review r1, parent adjudication r1) was taken as given and not re-audited. No git, child agents, browser tabs, uploads or messages were used, and nothing outside this directory was written. Frozen inputs were hashed before and after: 424 files, aggregate `89410cd1…7b0057`, unchanged. No background jobs remain.

## Verdicts

| ID | Fidelity | Maths (own re-check) | Novelty (bounded) | Significance | Recommendation |
|---|---|---|---|---|---|
| 355956 | FAITHFUL | CORRECT | no prior report found | **PASS** | eligible for root acceptance |
| 355701 | FAITHFUL ("maximal" is ambiguous) | CORRECT | no prior report found | **HOLD** | do not count on present evidence; root adjudicates whether it is routine |

## 355956: Yip's maximal subfield clique conjecture (q = 5^8, d = 3)

**Fidelity.** The MathDB text is verbatim the same as:
- Yip, J. Algebraic Combin. 56 (2022) = arXiv:2101.09652 v2, Conjecture 1.4;
- arXiv:2209.00864 v2 = Algebr. Comb. 6(4) (2023) 901–905, Conjecture 1.1. I read both the arXiv TeX and the published ALCO TeX, and the two are identical in substance.

Asgarli–Yip (arXiv:2106.01522) restates it with a redundant "is a subfield" clause. For (5^8, 3) the only admissible r is 1, so the claim reduces to "F_5 is a maximal clique of GP(5^8,3)".

MathDB's status is "open". Its references field carries a quote reading "solved according to the source", but that quote is about the Peisert analogue, not this conjecture.

**Own re-check** (`scripts/yip_verify.py`, own GF(5^8) code, 1.9 s):
- f is irreducible.
- x − a is a nonzero cube for every a ∈ F_5.
- F_5 ⊕ xF_5 is a 25-clique.
- F_25 and F_625 are not cliques, so F_5 is also a maximal *subfield* clique.
- There are exactly 960 extension vertices, all of degree 8.

None of the extension vertices lies in F_625. GP(5^8,3) restricted to F_625 is GP(625,3), so this agrees with Yip's reported Sage check for n ≤ 5. Theorem 1.2 is not contradicted, because 5 ≤ (8 − 1)² = 49.

**Prior art.** Bodies read:
- 2101.09652;
- 2209.00864 and the ALCO published version;
- 2106.01522;
- Martin–Yip 2403.04312 (PAMS 2024);
- Yip 2304.13213 (DCC 2025).

Keyword scans: 2604.04126, 2503.09914, 2203.16081, 2306.00391, 2110.07176, 2010.01784 and 2505.04061.

OpenAlex lists 3 citers of the ALCO paper; all three were read. It lists 10 citers of the JACO paper; 7 were read or scanned and 3 were not. Live registries and web search are negative. None of these sources notes a failure.

On the contrary, **Yip's DCC 2025 paper (2304.13213) restates [ALCO] as having shown, without qualification, that the largest subfield clique is maximal.** It also calls "ω(GP(q,d)) = |K|" "tempting". The 25-clique found here contradicts that too.

**Significance: PASS.**
- The result refutes in exact scope a journal conjecture that its author's own follow-up announces as "confirmed". A later published paper repeats that claim. It also refutes the explicit ALCO remark-conjecture that the hypothesis q > (n−1)² can be dropped.
- It is not a corollary, and it is not an endpoint or domain correction.
- The source's own exhaustive checks (n ≤ 5, and n = 6 with q ≤ 17) missed it; it first appears at n = 8.
- **Adversarial caveat:** GP* failures in the same paper make a GP failure plausible after the fact, and Theorem 1.2 covers the large-subfield regime. Neither point removes the fact that the unrestricted statement was asserted and claimed as confirmed.

**Paper guidance.**
- Say that Theorem 1.2 stands.
- Say that the "confirms" abstract and the DCC 2025 restatement overstate what was proved.
- Keep the remark-conjecture refutation and the 960 count as remarks, since they are outside the Lean endpoint.

## 355701: Bishop–Kuss–Peet partial-converse conjecture (9_3 counterexample)

**Fidelity.** The conjecture is verbatim the same in arXiv v1 (2022, then under a different title), arXiv v2 (2024) and EJGTA 11(2) 2023, Conjecture 1. Configurations are purely combinatorial, with no connectivity requirement. The context ("Pappus … maximally three, Möbius–Kantor four") indicates that i is the **maximum** size.

I found two source defects:
- The second example is not v3: point 1 lies on 4 lines. It is the source's only witness that the converse of Theorem 6.1 fails.
- The "Young configuration", judged from its figure, is AG(2,3), the Hesse (9_4, 12_3) configuration. It is not v3 either.

**Own re-check** (`scripts/v3_verify.py`, 69 s):
- The counterexample is a 9_3 configuration with 21 triangles. The source's Definition 4.1 gives the same triangle set.
- The minimum number of monochromatic triangles is 1, and the maximum intersecting set has 4 lines.
- Its automorphism group has order 9.
- Enumerating all 73920 labelled 9_3 configurations gives exactly three classes: Pappus (min 0), a second class (max 4, min 0) and the counterexample class (max 4, min 1).

**Prior art.** OpenAlex shows zero citing works. There are no other Peet papers on arXiv, and Peet's GitHub has only the GAP code. Registries and web search are negative.

**Significance: HOLD.**
- **`conjectureInclusion_false` carries no weight.** Under the inclusion-maximal reading, the conjecture is already refuted by the source's *own* example, the connected sum of two Fano planes. That configuration has min 4 and inclusion-maximal intersecting sets of sizes 3, 5 and 6. The disconnected Fano ⊔ Pappus also refutes it.
- **`conjectureMaximum_false`** is the real content, but the counterexample is one of only three classical 9_3 configurations. Orders 7 and 8 cannot refute, so this is the smallest possible order. Running the source's own published GAP procedure on that entry finds it.
- Here the "first test anyone would run" objection is concretely established, unlike the conference-matrix precedent (`conference-significance-adjudication-r2`). The source's evidence base is defective, it has zero citations, and the result has no structural content. Infinitude is trivial through disjoint unions.
- It is still not a written exclusion (known theorem, corollary, endpoint correction or parameter instance). Under the conference-r2 minimum-threshold precedent, a QUALIFIED_PASS limited to the maximum reading is defensible. That call belongs to the root.
- **What would change the verdict:** an infinite family of *connected* counterexamples, or a characterisation at maximum intersecting size 4.

## Registries (live, 2026-11-01 ≈ 17:01 UTC; `/commits/HEAD` only)

- **OpenAI/math:** HEAD is 4eaee875, unchanged. I screened the complete preprint tree by path; the 751 top-level directories have no relevant hit. This is a path-scope screen only, not a body screen.
- **Omega:** HEAD is 3ca0ba6c, which differs from the briefed 87d75734.
  - The delta 87d75734…3ca0ba6c (39 commits, 67 files) has 0 hits.
  - The cached complete D5 and Problems trees contain only the unrelated Asgarli–Yip pseudo-Paley entry (Conjecture 5.9 of 2110.07176). I read its body.
  - Gap: the 83b70a1d…87d75734 compare is capped at 300 files, so for that interval I rely on the root's verification of 87d75734.
- **MathDB/Palomar:** not accessed (inherited 403, not retried).

r1's earlier `openai/math` receipt used `/commits/main`, which the brief forbids, so I did not rely on it.

## Evidence

- `review.json`: verdicts per ID.
- `checks/`:
  - `yip-verify.json`
  - `v3-verify.json`
  - `r1-download-verification.json`: 27 of 27 r1 downloads match their receipts.
  - `registry-path-screen.json`
- `logs/`:
  - `http-receipts.jsonl`: 21 dated receipts with status and sha256, all single-attempt.
  - `web-searches.json`
  - `frozen-before.json` and `frozen-after.json`
  - screen logs and run logs
- `scripts/`: all code, run through `capped.sh` (2 CPUs, 6 GiB, CPU 120 s, wall 140 s).
- `downloads/`: newly fetched eprints and their safe extractions, registry JSON, OpenAlex and arXiv-API listings, EJGTA text and source figures.

Bodies read from r1's downloads were used only after hash verification. Those were 2101.09652, 2106.01522, 2208.06912 v2, 2209.00864, 2403.04312, 2505.04061, the EJGTA PDF, the GAP repo and the Omega bodies. I re-extracted the archives myself into `downloads/eprints/`.
