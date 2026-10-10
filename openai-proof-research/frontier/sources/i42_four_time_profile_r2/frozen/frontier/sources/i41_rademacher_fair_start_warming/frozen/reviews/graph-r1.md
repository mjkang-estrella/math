# Review round 1: proposals/complexity.md, section 1 only

Reviewer scope: this review covers only the new deductions in section 1 (edge and genus budgets for ordinary coloring of K_r-free graphs). Following the user's instruction and AGENTS.md, upstream theorems are taken as true.

**Verdict: ACCEPT WITH CORRECTIONS.** (C1)–(C3) are correctly proved for fixed r≥4. Every exponent and logarithm power checks out. The corrections below concern attribution, the honest size of the improvement, and small proof details. None of them changes a statement.

## 1. Sources checked (pinned revision fd4aeeb2…)

- **Family 184, `build/sections/introduction.tex`, `thm:main`, lines 25–34.** Verbatim: "For every integer r≥4 there are constants C_r>0 and Δ_r≥3 such that every K_r-free graph G of maximum degree Δ≥Δ_r satisfies χ_DP(G) ≤ ⌈C_r Δ/log Δ⌉." Natural logarithms are used. The proposal paraphrases this accurately. Ordinary χ ≤ χ_DP is standard.
  - The same file has `cor:forbidden`, which extends the theorem to every F-free graph. The text notes that its ordinary-coloring version is Conjecture 3.1 of Alon–Krivelevich–Sudakov (1999). This matters for the novelty discussion in §4.
- **Family 170, `build/upper-bound.tex`, `thm:upper`.** It states r(5,t) ≤ C t^4/(log t)^3. Line 163 of the proof explicitly derives r(4,t) ≤ C_4 t^3/(log t)^2 first. Confirmed.
- **Fixed off-diagonal paper, `00-introduction.tex`, `intro:main`.** For s≥6 the upper bound r(s,t) ≤ C_s t^{s-1}/(log t)^{s-2} has a constant and no ε. Confirmed. The ε appears only in the lower bound.
- **Correction (attribution).** For every fixed r≥3, the upper bound R(r,t) ≤ C_r t^{r-1}/(log t)^{r-2} is exactly the 1980 Ajtai–Komlós–Szemerédi theorem. Cite AKS as the primary source for all r, and give the pinned 170 and s≥6 files only as convenient in-repo restatements. As written, the proposal reads as if the in-repo files "supply" the bound. It already says the bound is "classical", so make AKS the citation in dependency 2 itself, not only in the novelty paragraph.

## 2. Independent verification of the proof

**Ramsey to independent sets.** Take t = a N^{1/(r-1)} (log N)^p. Then

A t^{r-1}/(log t)^{r-2} = A a^{r-1} N (log N)^{r-2}/(log t)^{r-2}.

Since log t = (1/(r-1)+o(1)) log N, this is about A a^{r-1} (r-1)^{r-2} N, which is ≤ N for small a. So α ≥ a N^{1/(r-1)} (log N)^p, with p = (r-2)/(r-1). ✔

**Dyadic removal, estimate (1).** In a phase with residual order n∈[N/2^{j+1}, N/2^j], the number of removals is at most (n/2)/α_min + 1 = O((N/2^j)^p/(log(N/2^j))^p) + 1.
- Phases with N/2^j ≥ √N form a geometric sum, O(N^p/(log N)^p).
- Lower phases cost O(N^{p/2}) + O(log N).
- The bounded residual costs O(1).

Since p≥2/3 for r≥4, O(log N) is dominated. So (1) holds. ✔ The bound is existential, and the proposal says so.

**Optimisation.** Write L = log m and D = m^q L^a.
- Low-degree part: D/log D ≍ m^q L^{a-1}, since log D ≍ q·L.
- High-degree part: |H| ≤ 2m/D, so (1) gives O((m/D)^p (log(m/D))^{-p}) ≍ m^{p(1-q)} L^{-p(1+a)}, since log(m/D) ≍ (1-q)L with 1-q>0.
- p(1-q) = (r-2)/(2r-3) = q. ✔ Also p/(1+p) = q. ✔
- Balancing a-1 = -p(1+a) gives a = (1-p)/(1+p) = 1/(2r-3). ✔ This is the proposal's choice.
- Common value: L^{a-1} = L^{-(2r-4)/(2r-3)} = L^{-2q}. ✔ Also p(1+1/(2r-3)) = 2(r-2)/(2r-3) = 2q. ✔
- Monotonicity: x↦(x/log(x+2))^p is eventually increasing, so substituting |H| ≤ 2m/D in (1) is legitimate. Small |H| is absorbed by the "1+" term.

**Small degrees in G[L].** Let Δ' = Δ(G[L]) ≤ D. If Δ' < Δ_r, then χ ≤ Δ_r. Otherwise χ ≤ ⌈C_r Δ'/log Δ'⌉ ≤ ⌈C_r D/log D⌉, because x/log x is increasing for x≥e and Δ_r ≥ 3. ✔ Correction: state these two sentences explicitly instead of "enlarged to cover smaller actual degrees".

**Disjoint palettes:** fine. Isolated vertices and small m are absorbed into C_r. ✔

**(C2).** From k ≥ k_r and (C1), the "1" is absorbed and m^q ≥ c k (log(m+2))^{2q}, so m ≥ c' k^{1/q} log²(m+2). Here 1/q = (2r-3)/(r-2): 5/2, 7/3, 9/4 for r=4,5,6. ✔ The critical-subgraph bound m ≥ k(k-1)/2 gives log m ≥ (1-o(1)) log k. ✔ A subgraph of G is K_r-free and has at most m edges, so applying (C1) to G directly is also fine. The critical subgraph is used only for the logarithm, and that use is correct.

**(C3).** Let J be k-critical with k≥9, so δ(J) ≥ k-1 and v(J) ≥ k ≥ 3.
- The Euler bound e ≤ 3v - 6 + 3g holds for any simple graph embeddable in a surface of Euler genus g, orientable or not, cellular or not. It is applied to J, a subgraph of G.
- Combined with e ≥ (k-1)v/2, this gives (k-7)v ≤ 6g - 12, hence v ≤ 3g - 6 < 3g and e ≤ 3v + 3g ≤ 12g. ✔
- For g=0 there is no J with k≥9 at all, consistent with "nothing to prove". ✔
- Then χ = χ(J) ≤ C(1 + (12g)^q/log^{2q}(12g+2)) ≤ C'(1 + g^q/log^{2q}(g+2)). ✔
- Since q < 1/2, this beats Heawood's O(√g) for every fixed r. Good sanity check: as r→∞, q→1/2.
- The "In particular" genus requirement Ω(k^{1/q} log² k) follows as in (C2), using g ≥ e(J)/12 ≥ k(k-1)/24. ✔ Correction: state that last inequality explicitly, since the log step needs it.

**r range.** r≥4 is forced by `thm:main`. For r=3 the same proof works with Johansson/Molloy/Bernshteyn's Δ/log Δ and gives q=1/3, 2q=2/3, which is exactly Gimbel–Thomassen. That is a good consistency check, and the proposal correctly refuses to claim r=3.

## 3. Failure boundaries and over-claims to guard against

- **Constants.** All constants depend on r. Molloy's bound is uniform in r; this one is not, because `thm:main` has non-explicit C_r and Δ_r. The proposal says this. ✔
- **DP or list coloring of the whole graph is NOT obtained.** The high-degree part is colored with independent sets. The proposal says this. ✔ Suggest adding one line on why: the Ramsey/independence step has no list analogue at this strength.
- **F-free extension.** Via `cor:forbidden` it does not transfer directly, because the independent-set step needs an F-specific Ramsey bound. Do not claim it.
- **No sharpness.** No lower-bound construction is matched. The Ramsey-graph constructions in the companion papers give K_r-free graphs with χ ≈ n^p polylog, but with about n² edges, so they are far from (C2). Keep "no sharpness claim".

## 4. Novelty and size of the improvement (correction required)

The proposal should state the improvement quantitatively against **both** baselines, not only Molloy.

| Baseline | Edge requirement for χ = k |
|---|---|
| (a) Trivial, no degree theorem: critical J has v ≤ 2m/(k-1), then (1) | m ≥ c k^{1/q} log k |
| (b) Molloy 2019 / Johansson in the same decomposition (re-derived: b = -1/(1+p), extra (log log m)^q in C1) | m ≥ c k^{1/q} log² k / log log k |
| (c) This proposal | m ≥ c k^{1/q} log² k |

So the gain over the best derivable pre-upstream bound is **one log log k factor in (C2)**, or (log log)^q in (C1)/(C3). The exponent 1/q and the log² term are already obtainable from Molloy. The proposal mentions (b) but should put this table in the summary. "Changes the controlling parameter" overstates things: the decomposition is a routine adaptation of Gimbel–Thomassen's triangle-free argument. Recommended wording: "routine Gimbel–Thomassen-type transfer of the new Δ/log Δ theorem; removes the log log factor from the Molloy-based analogue".

Literature search: two web searches (Molloy/K_r-free/edges/genus; Gimbel–Thomassen generalisation to K_r-free) found no edge-count or genus statement for K_r-free graphs. The pre-upstream analogue (b) may well appear in the literature (Gimbel–Thomassen's paper itself, Harris arXiv:1604.00438, or work after Alon–Krivelevich–Sudakov 1999). Before finalising, check whether Gimbel–Thomassen (2000) remark on K_r-free graphs, or state the (b)-type bound conditionally on the AKS conjecture. If they do, then (C1)–(C3) are "the known conditional consequence, now unconditional" — still a valid corollary, but the label should say so. Keep the current label ("proved downstream corollary; plausible literature improvement, pending specialist review") and add this conditional-prior-art caveat.

Sources consulted: [Molloy arXiv:1701.09133](https://arxiv.org/abs/1701.09133), [Davies et al. arXiv:2403.03054](https://arxiv.org/abs/2403.03054), [nibble survey arXiv:2106.13733](https://arxiv.org/abs/2106.13733), [Gimbel–Thomassen DOI](https://doi.org/10.1016/S0012-365X(00)00087-X) (not opened in full).

## 5. Concrete changes requested

1. Dependency 2: cite AKS 1980 as the source of R(r,t) ≤ C_r t^{r-1}/(log t)^{r-2} for all r. Keep the in-repo files only as restatements.
2. Replace "enlarged to cover smaller actual degrees" with the explicit two-case argument (Δ' < Δ_r, or monotonicity of x/log x).
3. In (C3)'s "In particular", add g ≥ k(k-1)/24 to justify log g ≍ log k.
4. Add the three-baseline table from §4. Rephrase the novelty paragraph so the gain is clearly one log log k factor over a Molloy-based derivation, and the method is a routine Gimbel–Thomassen-type transfer.
5. Add the caveat that a conditional statement (assuming the AKS 1999 conjecture) may already exist in the literature. Name Gimbel–Thomassen (2000) and Harris as the first places to check.
6. Optional: one sentence noting that `cor:forbidden` does not yield F-free edge bounds without F-specific Ramsey input.

No mathematical errors were found. Once the attribution and novelty wording are fixed, the section is fit to integrate.
