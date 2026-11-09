# r494 — independent source/prior review of MathDB 338290 (arXiv:1801.08029 Conjecture 3.8)

Reviewer: Claude Opus 5.5, solo, no children. Date 2026-10-31 (UTC fetch times in `fetch-log.tsv`).
Scope: ONLY MathDB 338290, the r480 brief `P1-338290-banzhaf-counterexample.md`, and the retained source body.
Zero MathDB requests. No upstream verifier run. No Lean/manuscript work. No acceptance credit.

## Verdict (one line)

**RETIRE — PRIOR.** Conjecture 3.8 is literally false under every reading, and the brief's finite witnesses are correct. But a complete public refutation already exists. The bridge from it is routine, and it covers both readings and strict-majority (proper) quotas. Gafni–Lavi–Tennenholtz, *Worst-case Bounds on Power vs. Proportion in Weighted Voting Games…*, arXiv:2108.09216v1 (2021-08-20) = JAIR 72 (2021) 99–135, DOI 10.1613/jair.1.13136: Theorem 4.1, Example 4.1 and Appendix C. For the absolute reading, the classical equal-weight majority game (Penrose 1946; Dubey–Shapley 1979, cited by the source as [15]) is an even more elementary prior. No credit. Counts unchanged: **9 additional / 39 total / next 40**.

## Gate summary

| Gate | Outcome |
|---|---|
| SOURCE | Exact statement read in the retained v2 body and in v1. The intended reading is ambiguous (symbol β = absolute; word "relative" = normalized). Quota and game class are unrestricted. Not published (no journal-ref, no Crossref hit; not clearance). |
| MATH | Brief's witnesses A and B independently re-derived by hand and by exact enumeration: correct. The general apex-family threshold is correct (k ≥ 7). Brief's minimality claims were not reproduced except in the bounded range m ≤ 6, weights ≤ 7 (0 normalized violations). They are not needed. |
| SUBSTANTIVE | A one-line corollary of a published unboundedness theorem (normalized) or of a textbook computation (absolute). This would be a "public refutation / routine corollary / parameter instance", not a discovery. |
| PRIOR | **FAIL (defeated).** GLT 2021 Thm 4.1 / Ex. 4.1 / App. C give a complete, rigorous counterexample family, published 3.5 years after the conjecture (v1 2018-01-21; v2 2020-02-17). GLT do not cite or mention the conjecture. The chronology is GLT 2021 ≪ our 2026 work, so it is prior relative to any claim of ours. |
| FORMAL-FEASIBILITY | Trivial: witness B is a `decide` over 512 subsets of `Fin 9`. Moot after the PRIOR gate. No implementation done. |

## 1. SOURCE — exact statement and assumptions

Bound input: retained `1801.08029.pdf` (sha256 `ef8f72d4…7f976`, 163312 B, 15 pp., pdfinfo CreationDate 2020-02-17). It is byte-identical to a fresh `https://arxiv.org/pdf/1801.08029v2` fetched today. The retained `.txt` is byte-identical to a fresh `pdftotext -layout` of that PDF. Line numbers below refer to the retained `.txt`.

- **Game (l.36–41, §2.1.1 l.158–159):** players p_1..p_m with weights w_i and "a preassigned quota q". C is winning iff Σ_{p_i∈C} w_i ≥ q. §2.1.1 only says "quota q > 0". There is no majority, properness, integrality or normalisation hypothesis.
- **Critical pair (Def. 1.1, l.43–46):** C ∈ W and C − {p_i} ∉ W. γ_i = number of critical pairs. **β_i = γ_i / 2^{m−1} (l.61)**, β̃_i = γ_i / Σ_j γ_j. l.67: "β̃_i is known as the normalized Banzhaf index. β_i, the absolute Banzhaf index will, however, be our main focus."
- **Conjecture 3.8 (l.375–382):** "In our calculation we have observed that for the relative Banzhaf index β_i the following relation is valid for any voting game. … Conjecture 3.8. Let w_1,…,w_m be a set of positive weights, let w be the maximum of these weights, further let N = Σ_{i=1}^m w_i then the relative Banzhaf indices β_i ≤ 2w/N."
  - The quantifier is over all positive weight vectors and (by "any voting game") all quotas. w is the **maximum** weight, so the same bound applies to every player i, not 2w_i/N.
  - The conjecture is scale-invariant: the game depends only on {C : w(C) ≥ q} and the bound only on w/N. So integer vs real weights is immaterial; integer witnesses are positive-real witnesses.
  - There is no association matrix in the statement. It concerns the plain single-quota index of §1, not β_Φ.
- **Ambiguity:** the symbol is β_i (absolute, l.61), but the word is "relative". In the standard literature "relative" means normalized. For example, Kurz arXiv:1802.00497v3 (`derived/1802.00497v3.layout.txt` l.188–189) writes: "the (relative) Penrose–Banzhaf index is the corresponding efficient version". The §5 tables also sum to 1.0 (l.619, l.655), i.e. the authors' "calculations" were normalized. Equal weights give a further hint: the normalized index 1/m always satisfies 2/m, while the absolute index fails at m = 7 (see §2). **Most plausible intended statement: the normalized index.** The review treats both readings, and both are refuted.
- **EU context (§5, l.566–575):** the experiments use a 3-quota EU game on 18 countries with weight ≥ 7. That context is a multi-quota game, which the conjecture's single weight vector cannot express. The conjecture has no EU restriction and explicitly says "any voting game". The §5 Table 1 data satisfy the bound (max 0.0956 < 2·29/291 ≈ 0.199). No restricted class is stated anywhere, and I do not invent one.
- **Surrounding results:** Prop. 3.1, Lemma 3.2 and Prop. 3.4 are generic bounds. Remark 3.5 says Prop. 3.4 generalises Dubey–Shapley '79 [15]. The source cites Dubey–Shapley [15], Holzman–Lehrer–Linial [21] and Alon–Edelman [2], but derives nothing from them toward 3.8. HLL [21] was not retrieved (INFORMS/JSTOR not attempted) and is not relied on.
- **Versions:** v1 (2018-01-21, `fetched/pdf/1801.08029v1.pdf`, sha `523b1ca4…`) and v2 have whitespace-identical §3 text. That includes Conjecture 3.8. Other v1→v2 changes are title ("indices"→"index"), author-name formatting, keywords and reference renumbering. arXiv abs page (fetched 2026-10-31): no journal-ref. Crossref bibliographic query: no published version found. That is a search, not proof of non-publication. **No published-version change is known.**

## 2. MATH — independent derivation of critical counts

Hand derivation (players: one "big" of weight a, n unit players, quota T, s = number of unit players in a coalition):
- big is critical ⇔ a + s ≥ T and s < T;
- a unit player is critical ⇔ (big ∈ C and s = T − a) or (big ∉ C and s = T).

**Witness A** (3;1,1,1,1), q = 4, N = 7, 2w/N = 6/7, q > N/2.
- Big is critical ⇔ 1 ≤ s ≤ 3, so γ = 4 + 6 + 4 = 14 and β = 14/16 = 7/8 > 6/7 (49 > 48). The absolute reading is refuted.
- Unit players: γ = 1 + C(3,3) = 2 each. Normalized big = 14/22 = 7/11 < 6/7. A does **not** refute the normalized reading (the brief does not claim it does).

**Witness B** (7;1^8), q = 8, N = 15, 2w/N = 14/15, q > N/2.
- Big is critical ⇔ 1 ≤ s ≤ 7, so γ = 2^8 − 2 = 254.
- Unit players: γ = C(7,0) + C(7,7) = 2 each. Total = 254 + 16 = 270.
- β̃_big = 254/270 = 127/135, and 127·15 = 1905 > 1890 = 14·135. β_big = 254/256 = 127/128 > 14/15.
- Coleman's prevent/initiate ratios γ/|W| = γ/|L| = 254/256 also exceed the bound (|W| = |L| = 256).

So **B refutes every candidate meaning of "relative"** checked here.

**Class checks:** A and B are proper and strong (decisive: N odd, q = (N+1)/2), so they are constant-sum weighted majority games. Simple, monotone, no dummies in B. Hence no "proper / strong / strict-majority" restriction rescues the conjecture.

**Apex family** (k;1^{k+1}), q = k+1:
- γ_big = 2^{k+1} − 2 and γ_unit = 2.
- β̃_big > 2k/(2k+1) ⇔ (2^{k+1}−2)(2k+1) > 2k(2^{k+1}−2+2k+2) ⇔ 2^{k+1} > 4k² + 4k + 2.
- It fails at k = 6 (128 < 170) and holds at k = 7 (256 > 226). Induction: 2^{k+2} > 8k²+8k+4 ≥ 4(k+1)²+4(k+1)+2 ⇔ 4k² ≥ 4k + 6 (true for k ≥ 2). So it holds for every k ≥ 7.
- The brief's claim is correct. It is not needed, since one literal finite witness suffices.

**Absolute reading, even simpler:** equal weights 1^m with q = ⌊m/2⌋+1 give β = C(m−1,⌊m/2⌋)/2^{m−1}, against a bound of 2/m. It first fails at m = 7: 20/64 = 5/16 > 2/7 (140 > 128), and fails for all larger m checked (≤ 15). Asymptotically β ~ √(2/(πm)) ≫ 2/m (Penrose square-root behaviour). The normalized index 1/m always satisfies this bound.

The brief's m = 3 absolute witness (8,7,7), q = 8 checks by hand: γ_8 = 3 (coalitions {8}, {8,7}, {8,7′}), so β = 3/4 > 16/22. This is a non-proper quota and is not needed.

**Machine evidence (all exact `Fraction`/`int`, under helper_guard, 512 MiB / CPU 210 s / wall 230 s):**
- `scripts/indep_check.py` → `runs/indep_check.m6w7.r1.txt`. Written from the source definitions, not from the r480 script. It asserts A, B, the equal-weight table m ≤ 15, the apex family k ≤ 14 with the closed-form threshold, properness/strongness, and Coleman variants. Bounded search over m ≤ 6, integer weights ≤ 7 and all quotas found 0 normalized violations. That is evidence only and consistent with the brief's (unverified) "none for m ≤ 8" claim.
- `scripts/prior_check.py` → `runs/prior_check.r1.txt`. The closed form for one big player is checked against brute force on 729 games, then evaluated exactly on the GLT witnesses below (wall 172 s).
- `scripts/prior_proper.py` → `runs/prior_proper.r1.txt`. Strict-majority variant.
- The r480 `banzhaf.py` was **not** executed or trusted.

## 3. PRIOR / SUBSTANTIVE — complete public refutation

**Gafni, Lavi, Tennenholtz (GLT)**, arXiv:2108.09216v1 (sole version, 2021-08-20; arXiv-linked DOI 10.1613/jair.1.13136 = JAIR 72:99–135, 2021-09-23 per Crossref; also IJCAI 2021 pp. 210–216, DOI 10.24963/ijcai.2021/30). Bound file `fetched/pdf/2108.09216v1.pdf` (sha `9195faa8…`). Only the arXiv text was read; the JAIR/IJCAI typeset versions were not fetched.
- **Def. 2.1 (l.250):** a WVG is {A, m, T}, with big players A = {a_1..a_r} ⊂ ℕ, m small players of weight 1, and threshold T ∈ ℕ with 1 ≤ T ≤ m + Σa_j. A coalition wins iff its weight is ≥ T, the same "≥ quota" rule as the source.
- **Def. 2.2 (l.280):** P = Σa_j / (m + Σa_j).
- **Def. 4.1 (l.645):** the absolute Banzhaf index β′ is the expected marginal contribution over uniform subsets of the others, which equals the source's γ_i/2^{m−1}. The normalized index β is β′ divided by the total, which equals the source's β̃_i. The definitions match exactly.
- **Def. 4.2 / Thm 4.1 (l.671–682):** "R̄_{β′}, R̄_β are unbounded", where R̄ is the supremum over WVGs of (Σ_i β_{a_i})/P.
- **Example 4.1 / Appendix C (l.686–711; App. C from l.1673):** r = 1, A = {2k}, m = k^{1.5}, T = (2k + k^{1.5})/2 (k = 4, 16, 36, …). The appendix proves β′_{a1} ≥ 0.95 (Okamoto–Chernoff) and β_{a1} ≥ 0.95/(2k^{1.5}e^{−2√k} + 1) ≥ 0.7, with P = 2k/(2k + k^{1.5}) → 0. I audited the appendix and found no gap:
  - the window |X − k^{1.5}/2| < k ⇔ |X/k^{1.5} − ½| < 1/√k;
  - the Pascal step;
  - 2e^{−2√k} ≤ 0.05 for k ≥ 4;
  - 2k^{1.5}e^{−2√k} decreasing for k ≥ 4.
- **Routine bridge to Conjecture 3.8:** take r = 1 and a_1 = 2k ≥ 1 = the small weight. Then w_max = a_1, and P = a_1/N = w_max/N. Any GLT game with β_{a1} > 2P violates the normalized reading. Separately, any GLT game with β′_{a1} ≥ 0.95 > 2P violates the absolute reading.
  - The appendix bound alone suffices once 0.7 > 2P, i.e. P < 0.35. That holds for k = 16 (A = {32}, m = 64, T = 48, P = 1/3, 2w/N = 2/3).
  - Exact values (`runs/prior_check.r1.txt`):

    | k | β̃_big | 2w/N |
    |---|---|---|
    | 16 | 0.998307864… | 2/3 |
    | 36 | 0.99994 | 1/2 |
    | 1600 (= GLT Ex. 4.1: weights (3200; 1^{64000}), T = 33600) | ≈ 1 − 10^{−6} | 2/21 |

    At k = 1600 the ratio is ≈ 21, i.e. **≈ 10.5× the conjectured bound**. The absolute index also exceeds the bound in every case with k ≥ 16.
- **Quota class:** GLT use T = N/2 exactly, which is not proper because ties exist. The dual quota T = N/2 + 1 is strict-majority and proper. Banzhaf swing counts are duality-invariant, and `runs/prior_proper.r1.txt` confirms identical exact indices at k = 16, 36, 64, 400. So the prior covers proper strict-majority games too. That duality step is my routine bridge, not a GLT sentence. The source's own statement needs no such step, since it allows any q > 0.
- GLT themselves say (l.710–711) that Ex. 4.1 is "in the spirit of Section b of Penrose (1946) and the asymptotic results analysed in Section 7 of Dubey and Shapley (1979)". The phenomenon (one big voter against an ocean of unit voters at a majority quota has power → 1 while its weight share → 0) is therefore classical. Dubey–Shapley 1979 is the source's own reference [15]. Penrose 1946 and Dubey–Shapley §7 were not retrieved; the GLT attribution is recorded, not independently verified.

**Other related works (bounded, not exhaustive):**
- Arnell, Chen, Choi, Marinov, Polina, Prakash, arXiv:2010.08672 (2020-10-16). **Cites the source as [1].** §3.1 (l.340–372) gives the general closed-form normalized Banzhaf index of [>1/2 : a, b, …, b]. Specialised to b = 1/15, m = 8 (= witness B) it gives 254 vs 2 swings. The paper never compares with 2w/N or mentions Conjecture 3.8.
- Brooks–Šarčević–Volić, arXiv:2210.09771v3 (Theory & Decision 2025). Cites the source only for the association-matrix idea (l.1142). Nothing on 3.8.
- Kurz, arXiv:1802.00497v3. Terminology only; no bound of this form found in the parts read (intro, definitions).
- The apex game itself, with its standard Banzhaf computation, is a textbook object (von Neumann–Morgenstern / Felsenthal–Machover). That is reviewer recollection only, not retrieved, and not used as evidence.

**Explicit public refutation of Conjecture 3.8 as such:** none found. Citing-work coverage comes from OpenAlex (2 citers) plus a Semantic Scholar citation list (4 entries; the 4th, "Banzhaf index with unfeasible coalitions"/"…unfeasibilities", 2023, has no arXiv record by title+author search and was not read). A negative search does not establish novelty, and it is irrelevant here, because the GLT theorem already defeats the conjecture through a one-line specialisation.

**SUBSTANTIVE judgement:** the brief's finite witness is correct and tidier than GLT's: 9 players with a proper strict-majority quota, against 65 players for GLT's smallest instance. Even so, it is (i) a parameter instance of the classical apex/one-big-player family, (ii) a direct consequence of a published 2021 unboundedness theorem whose own example violates the bound tenfold, and (iii) for the absolute reading, a textbook equal-weight calculation. Under the campaign rules this is a public refutation or routine corollary, so it is ineligible. The smaller witness is a presentation improvement, not a new mathematical outcome.

## 4. Exact source-refutation decision

- **Literal statement** (symbol β_i = absolute, any q > 0): refuted by witness A, by the equal-weight 7-player majority game, and by GLT (β′ ≥ 0.95 > 2P). Prior: classical plus GLT.
- **Normalized reading** ("relative", most plausible intent): refuted by witness B (and the apex family k ≥ 7) and by GLT Thm 4.1 / Ex. 4.1. Prior: GLT 2021.
- **Coleman-type "relative" variants:** refuted by B. Not separately prior-checked, and irrelevant given the above.
- **Restricted to proper / strict-majority / decisive games:** still refuted (A and B are decisive; GLT is covered via its proper dual).
- **Restricted to the source's EU 3-quota setting:** not a statement of the source. No substitute target is proposed.

## 5. Dependencies, remaining gaps, evidence limits

- Not retrieved: Penrose 1946, Dubey–Shapley 1979 §7, Holzman–Lehrer–Linial 1988, Alon–Edelman 2010, the Felsenthal–Machover book, and the JAIR/IJCAI typeset GLT. The retirement does not depend on them: GLT arXiv v1 Appendix C plus my exact computations suffice.
- Current public proof registries were not checked: MathDB is on HOLD (zero requests) and the other barred routes stayed parked. A missing current-registry check stays **HOLD**, but it cannot rescue eligibility, since the prior is already decisive.
- The Semantic Scholar paper endpoint returned 429; its citation endpoint returned 200 (see failures F01). OpenAlex coverage is partial (2 citers).
- Integrity PASS (`verification-receipt.txt`) is not a math or novelty PASS.

## 6. Recommendation

Retire 338290 as **PRIOR-DEFEATED** (GLT 2021, routine bridge; absolute reading classical). Record the brief's witnesses as correct but non-creditable. Spend no further investment, and allocate no Lean or manuscript work. Counts stay **9 additional / 39 total / next 40**.
