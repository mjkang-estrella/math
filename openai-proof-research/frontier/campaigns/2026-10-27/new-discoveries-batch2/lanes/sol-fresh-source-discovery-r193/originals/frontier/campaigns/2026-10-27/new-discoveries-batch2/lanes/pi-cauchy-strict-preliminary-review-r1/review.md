# Preliminary adversarial review — frozen candidate `root-cauchy-strict-r1`

Lane: `lanes/pi-cauchy-strict-preliminary-review-r1`. 2026-10-28.
Reviewer: Pi GLM-5.3-Flash (thinking=high), solo, no children. Pi standard/default speed only.
Candidate: `lanes/root-cauchy-strict-r1` @ review-freeze.json (six hashes; root commit context 721c6d4700).
Target: **MathDB 325521** = Simon, *Total positivity of a Cauchy kernel* (arXiv:1305.1173; J. Approx. Theory 234 (2018) 238–258), displayed Conjecture (2): for every n ≥ 2, α < 1/n ⇒ K_α ∈ STP_n, where K_α(t,x) = 1/(t² + 2cos(πα)tx + x²) on (0,∞)², all ordered positive tuples, all minors of order ≤ n **strictly** positive. α = 0 and α ∈ {1/2, 1/3, …} cases are known and uncredited (correctly treated as such by the candidate). Simon1412.0132 Theorem 1 / Corollary 1 prove only the **non-strict** TP_n classification; Remark 2(b) explicitly leaves strictness open. Per the brief, the known TP_n result is not a ground for rejection.

Freeze hashes reverified before this review: all six files match `review-freeze.json` exactly (see provenance.json). The candidate is a byte-identical copy of the completed worker proof `pi-cauchy-strict-discovery-r1/PROOF.md` (diff exit 0) plus `ROOT-OBJECTIONS.md`. **I do not inherit the worker's claims**; everything below was re-derived or re-checked independently.

---

## 0. Verdict summary

| Gate | Decision | One-line reason |
|---|---|---|
| SOURCE | **PASS** | Both Simon preprints read in full from the hash-pinned r6 cache; every quoted statement (Theorem 1, Corollary 1, the Gram display, Remark 1, Remark 2(b), g_α mgf, Mellin ratio, Conjecture (2)) found **verbatim**. MathDB refetched live: open, no solutions. Published JAT/Constr. Approx. bodies unread (paywall) — recorded. |
| MATH | **HOLD** | The theorem is true and the proof route is sound — I independently re-derived every load-bearing step — but the frozen text contains **five false displayed statements** (all confirmed wrong, all mechanically repairable; corrected paragraphs supplied in §3 of this review). None affects the truth of the result or the validity of the route. |
| SUBSTANTIVE | **PASS** | No generic Karlin/Pinkus strict-composition or analytic-nondegeneracy theorem upgrades the source's own printed factorization routinely; I exhibit an explicit counterexample killing the most tempting generic shortcut, and show the target is TP/STP-equivalent to strictness of the factor itself. Karlin (1968)/Pinkus (2010) book bodies unread — recorded as residual risk, not as clearance. |
| NOVELTY | **PASS** (bounded) | Fresh 2026-10-28 screens: MathDB live open/empty; Semantic Scholar citation corpora refetched (7 + 1 citers, none resolving); author list live-checked; targeted searches found no resolution. No worldwide-priority claim. |
| FORMAL | not assessed (no PASS) | No Lean artifact exists or was started (correct per brief). Precise formal scope/cost assessed in §6; an alternate proof avoiding reproof of Simon's stable TP theorem was searched for and **not found**. |

**Recommendation to root:** eligible to proceed to final review/integration **after** the five corrections of §3 are applied to a working copy; the frozen candidate stays untouched (credit0 preserved). If the final review adopts the corrected text, discovery-count credit **1** is appropriate. The strongest mathematical falsifier and the strongest surviving objection are in §4–§5.

---

## 1. SOURCE gate — PASS

Verified against the hash-pinned r6 cache (`lanes/root-special-screen-r6/simon-cauchy.html`, sha256 c622382a…7e60496; `simon-stable.html`, sha256 395dc332…172560f), extracted to text and read directly:

1. **Conjecture (2)** (1305.1173): "For every n ≥ 2, one has α < 1/n ⇒ K_α ∈ STP_n." Verbatim match with the candidate's target, and with the live MathDB 325521 statement. Part (c) gives only α ≤ 1/n ∧ 1/(n²−n−6)₊, so the conjecture is genuinely stronger than the printed theorem.
2. **Theorem 1** (1412.0132): "p_α(t,x) is TP_n ⇔ α ∈ {1/2,…,1/n} or α < 1/n." Verbatim. The candidate quotes it correctly and uses only the α < 1/n direction with m ≤ n (legitimate: TP_n ⇒ TP_m).
3. **The printed Gram formula** (1412.0132, proof of Corollary 1, §2.2): K_α(e^{αx}, e^{αy}) = πe^{(1−α)(x+y)}/sin(πα) · ∫_ℝ f_α(e^{x−u})f_α(e^{y−u})e^{−2u}du — **no factor m**, and the source itself concludes (Theorem 1 + Lemma 3.1.1) that the integral kernel is TP_n for α < 1/n. This is the source's own factorization; the candidate's Input A and Lemma 3.1/3.2 build on it.
4. **Mellin fact displayed in the source** (§2.1): ĥ_α(s) = E[Z_α^{−iαs}] = Γ(1+is)/Γ(1+iαs) — exactly the input the candidate's Lemma 3.1 needs (with ξ = −αs). The g_α mgf sin(παs)/(α sin(πs)) is displayed in 1305.1173's Prop 1 proof.
5. **Remark 2(b)** (1412.0132): strict STP_n for α < 1/n explicitly conjectured/open; "the fractional integration kernels I_β are never STP_n". Verbatim as the candidate reports. Remark 1: I_β ∈ TP_n ⇔ β ∈ ℕ or β > n−1.
6. **Zolotarev/Sato series** (candidate's Theorem B): not displayed in either preprint (only referenced to Sato (14.30)–(14.31)); independently verified by me: symbolically against the closed form at α = 1/2 (terms match: k=1 gives x^{−3/2}/(2√π), k=3 gives −x^{−5/2}/(8√π), …), numerically to ~1e−41 (checker Check A), and the convergence for **all** x > 0, all 0 < α < 1 follows from the term ratio ~ α^α x^{−α} k^{α−1} → 0 (contrast the Γ²-series of the source's §2.4, which converges only for α < 1/2 — the single-Γ series is genuinely better behaved).

Access limits recorded in provenance.json: ScienceDirect (JAT 2018, Constr. Approx. 2016) full bodies not read; HAL preprint hal-00820576 (same v1 text) exists; Karlin (1968) and Pinkus (2010) books not accessed. The 1412.0132 arXiv v1 is the only arXiv version, so arXiv-body risk is limited to the (low) possibility that the published Constr. Approx. version differs.

**SOURCE: PASS.**

---

## 2. MATH gate — independent verification, then the five errors

### 2.1 Steps I verified independently (all sound)

- **Lemma 3.1 (Gram/J_α identity).** Re-derived from scratch: (i) change of variables gives ∫ f(e^{x−u})f(e^{y−u})e^{−2u}du = e^{−(x+y)}J_α(x−y) with J_α(d) = ∫₀^∞ v f(e^{d/2}v)f(e^{−d/2}v)dv; (ii) J_α = h∗h~ where h(s) = e^s f_α(e^s) is the log-density, so Ĵ_α(ξ) = |E Z_α^{iξ}|² = sinh(πξ)/(α sinh(πξ/α)) using the source-displayed Γ-ratio and |Γ(1+iu)|² = πu/sinh(πu); (iii) the rescaled logistic density αg_α(αd) has exactly this Fourier transform (substitute s → is in the source's displayed mgf). Both sides continuous and L¹, so equal. Finiteness for **every** d is airtight (h ∈ L¹∩L∞ ⇒ h∗h~ ∈ C₀), via Tonelli — the entry integrals cannot diverge. Numerically confirmed to 1e−41 (checker Check B) at α ∈ {0.3, 0.55, 0.7}. **Lemma 3.1 is correct as written.**
- **Andreief applicability.** Entrywise integrability is supplied by Lemma 3.1 itself; the m-fold domination needs f_α bounded near 0 and ≤ Cz^{−(α+1)} near ∞ (the latter from the series; the former is classical — boundedness of stable densities — see Correction 4). The discrete Cauchy–Binet structure of Andreief is elementary.
- **§6 symmetry reduction.** det-factors are antisymmetric, product symmetric; the m! chambers give ∫_{ℝ^m} = m!·∫_{Ω_m}. Correct (cancels the 1/m!).
- **Lemma 4.1 (strictification).** Correct as written: {D_x > 0} is nonempty (H1 + H3), open, and dense (a nonzero real-analytic function on the connected open chamber has a zero set with empty interior — identity theorem); a **finite** intersection of open dense sets is open dense (elementary, no Baire needed); the integrand is ≥ 0 everywhere and > 0 on a nonempty open set, and w = ∏e^{−2u_j} > 0. Sound.
- **First n stable coefficients:** c_k ≠ 0 for 1 ≤ k ≤ n because 0 < αk < 1 forces sin(παk) ≠ 0. **Repeated Taylor indices:** in the multilinear column expansion, any repeated index k_j = k_l produces two equal columns, hence a zero determinant — exactly as the candidate claims.
- **Corollary A (Input A).** f_α(e^{x−u}) = f_α(e^x e^{−u}) with both coordinates increasing ⇒ TP_n from Theorem 1 by the source's own reduction sentence. Note the source's §2.2 *also* asserts the composed kernel M(x,y) = ∫f f e^{−2u} is TP_n directly; the candidate's usage is doubly source-backed.
- **§7 scope honesty.** α = 0 (Borchardt/Cauchy, source Prop 1), reciprocal α (source Prop 2.1), non-TP above 1/n (source Theorem (b)) — all correctly assigned as known/uncredited, and Conjecture 4 of 1305.1173 (strictness of p_α itself) correctly **not** claimed.
- **Falsifier scan (independent, checker Check E):** all minors strictly positive for α ∈ {0.05, 0.1, 0.15} (n=6), {0.2, 0.3} (n=3) over random and adversarial near-equal tuples (dps 40); negative minors appear exactly above the threshold (found at α=0.6, n=2 and — in the near-zero-column regime predicted by the source's Chebyshev analysis — at α=0.4, n=3). Consistent; no falsifier found. Diagnostics only, never proof.

### 2.2 The five errors (all six root objections adjudicated)

| # | Root objection | Adjudication | Severity |
|---|---|---|---|
| 1 | Extra m in the Lemma 3.2/§6 prefactor exponent | **Confirmed wrong.** Source's own display has e^{(1−α)(x+y)} per entry; det picks up (π/sinπα)^m e^{(1−α)(Σx+Σy)}. Checker Check C: corrected ratio = 1.000000000000; frozen text's ratio = 0.095369 = 1/e^{(1−α)(m−1)(Σx+Σy)}, exactly as predicted. | False identity displayed; **positivity and route unaffected** (prefactor > 0 either way). |
| 2 | Vandermonde factor missing ∏ z_i^α | **Confirmed wrong.** det[z_i^{αk+1}]_{k=1..m} = (∏_i z_i^{1+α})·V(z_1^α,…,z_m^α), not (∏_i z_i)·V(·). Checker Check D: the frozen text's normalized ratio converges to ∏z_i^α = e^{−αΣx_i} (0.8106 resp. 0.5488 — matching e^{−0.21}, e^{−0.6} exactly); corrected ratio → 1. | False identity displayed; **nonvanishing unaffected** (∏z_i^{1+α} ≠ 0). |
| 3 | "|r_k(i)| ≤ C for fixed tuples" | **Confirmed false** for x_i < 0 (z_i > 1 gives exponential growth in k). The tail-domination argument as written is invalid. | Broken bound inside a proof; **repairable** (Correction 3): the super-exponential decay |c_k| ~ exp(−(1−α)k ln k + O(k)) absorbs any fixed exponential growth; two-tier (finitely many small k / geometric tail) argument restores D_x ~ leading·(1+o(1)). Numerically confirmed with a **negative** x_1 present (Check D). |
| 4 | "Locally uniform limit of real-analytic functions is real-analytic" | **Confirmed false as a general principle** (Weierstrass approximation gives counterexamples). The conclusion (f_α real-analytic) is still true. | Wrong justification; **repairable** (Correction 2): f_α(x) = x^{−1}G_α(x^{−α}) with G_α(w) = Σ_{k≥1}c_k w^k entire (|c_k|^{1/k} → 0 by Stirling), or a common holomorphic slit-neighborhood. |
| 5 | Literal Lean absent; Theorem A outside mathlib | **Confirmed.** No artifact; Theorem A (and the series identity, and the Mellin facts) must be reproved from scratch for any endpoint; no new axioms. | Out of scope for this preliminary review; cost assessed in §6. |
| 6 | Generic strict-composition risk | See SUBSTANTIVE gate: **no routine upgrade exists**; explicit counterexample below. | Screened. |

**Additional finding (mine, beyond the root objections):** the §3 integrability sentence "the integrand decays like e^{αu} at −∞ and like e^{(α−1)u} at +∞" is wrong at +∞ as stated: each series term *grows* like e^{(αk+1)u}; the true decay of f_α near 0 is stretched-exponential (much faster than any exponential), which cannot be read off the displayed series. Repair in Correction 4 (one classical citation: boundedness of stable densities, or the Zolotarev small-argument asymptotic). Entrywise finiteness is anyway a byproduct of Lemma 3.1 itself; only the m-fold domination needs the bound. Minor: the −∞ rate is e^{2αu}, not e^{αu} (still integrable).

### 2.3 Strongest mathematical falsifier

A single explicit witness (n, α < 1/n, m ≤ n, 0 < t_1 < … < t_m, 0 < s_1 < … < s_m) with det[K_α(t_i, s_j)] ≤ 0 refutes the theorem. My independent high-precision scan (exact rational kernel entries, dps 40) found none in the admissible range and confirms negatives appear only above 1/n. The proof (after corrections) shows no such witness exists: the chamber integral is a nonnegative analytic-integrand integral, strictly positive on a nonempty open subset of Ω_m.

**MATH: HOLD** — five mandatory corrections (§3), all mechanical; no new mathematical ideas required; theorem statement and proof route independently confirmed.

---

## 3. Corrected proof paragraphs (for root's working copy; the frozen candidate is NOT edited)

**Correction 1 (Lemma 3.2 display and §6 constant).** Replace the Lemma 3.2 display by

    det[ K_α(e^{αx_i}, e^{αy_j}) ]_{i,j=1..m}
      = (π/sin(πα))^m · e^{(1−α)(Σ_i x_i + Σ_j y_j)} · (1/m!) · ∫_{ℝ^m} D_x(u) D_y(u) ∏_{j=1}^m e^{−2u_j} du,

and in §6 set P := (π/sin(πα))^m · e^{(1−α)(Σ_i x_i + Σ_j y_j)} > 0. *Reason:* each entry is (π/sin(πα))·e^{(1−α)(x_i+y_j)}·∫φ_{x_i}ψ_{y_j}dμ (the source's own §2.2 display, verified verbatim), and det[c·a_i·b_j·M_ij] = c^m(∏a_i)(∏b_j)det[M]. No m appears. (Verified exactly against the Cauchy double alternant at α = 1/2, m = 2: ratio 1.000000000000; the frozen text gives 0.095369….)

**Correction 2 (§2, analyticity).** Delete the sentence "f_α is real-analytic on (0,∞) (locally uniform limit of real-analytic functions)" and replace by:

*For 0 < α < 1 set G_α(w) := Σ_{k≥1} c_k w^k for w ∈ ℂ. By Stirling's formula, |c_k| = |Γ(1+αk) sin(παk)|/(πk!) satisfies |c_k|^{1/k} → 0, so G_α is an entire function (infinite radius of convergence). Since f_α(x) = x^{−1} G_α(x^{−α}) for all x > 0 (the series is a power series in x^{−α} times x^{−1}), and w ↦ w^{−1/α} is real-analytic on (0,∞), f_α is real-analytic on (0,∞). Equivalently, the series converges locally uniformly on the slit plane with any branch of the logarithm, giving a holomorphic extension to a common complex neighborhood of every point of (0,∞). Hence u ↦ f_α(e^{x−u}) is real-analytic on ℝ and D_x is real-analytic on the connected open chamber Ω_m.*

**Correction 3 (Lemma 5.1 statement and tail bound).** Replace the display by

    D_x(U+v_1, …, U+v_m) = ( ∏_{k=1}^m c_k ) · ( ∏_{i=1}^m z_i^{1+α} ) · V(z_1^α, …, z_m^α)
                           · ( ∏_{j=1}^m w_j^{1+α} ) · V(w_1^α, …, w_m^α) · e^{(m+αm(m+1)/2)U} · (1+o(1)),

with V(a_1,…,a_m) = ∏_{i<j}(a_j − a_i), z_i = e^{−x_i}, w_j = e^{v_j}; and replace the false bound "|r_k(i)| ≤ C for fixed tuples" by the following tail argument:

*Stirling gives |c_k| = exp(−(1−α)k ln k + O(k)), so for every η > 0 there is k_η with |c_k| ≤ η^k for k > k_η. Fix z_max := max_i z_i and v_max := max_j v_j. (i) At each fixed U ≤ 0 the column sums and the full multilinear expansion converge absolutely, dominated by ∏_j Σ_k |c_k| e^{(αk+1)(U+v_j)} z_max^{αk+1} < ∞ — the fixed exponential growth factor z_max^{αk} (which is unbounded exactly when some x_i < 0, so no k-uniform bound C exists) is absorbed by the k^{−(1−α)k} decay of |c_k|. (ii) Given ε > 0 choose η with C_ε η < ε, where C_ε depends on the finitely many k ≤ k_η; for U ≤ U_0(η) := −(1/α)ln(2ηe^{αv_max}z_max^α) the contribution of all tuples with some k_j > k_η is at most ε e^{(m+αm(m+1)/2)U}, while every remaining tuple with Σ k_j > m(m+1)/2 carries an extra factor e^{αU(Σk_j − m(m+1)/2)} ≤ e^{αU}. Hence D_x(U+v) = e^{(m+αm(m+1)/2)U}(∏_k c_k · D_z · D_w + o(1)).* The leading coefficient is nonzero: ∏_{k≤m} c_k ≠ 0 (0 < αk < 1), z_i, w_j > 0 and z_1^α > … > z_m^α, w_1^α < … < w_m^α, so both Vandermonde factors are nonzero. In particular D_x ≢ 0 on Ω_m. (Numerically: corrected ratio → 1 at (m,α) = (3, 0.3), (4, 0.2) with x_1 = −0.7; the frozen text's coefficient gives ratios → e^{−αΣx_i} ≠ 1.)

**Correction 4 (§3 integrability).** Replace the parenthetical "(valid since ∫|φ_iψ_j|dμ < ∞: the integrand decays like e^{αu} at −∞ and like e^{(α−1)u} at +∞)" by:

*(valid since ∫|φ_iψ_j|dμ < ∞: for u → −∞ the series gives |f_α(z)| ≤ Σ_k |c_k| z^{−αk−1} ≤ C z^{−(α+1)} for z ≥ 1, so the integrand is O(e^{2αu}); for u → +∞, z = e^{x−u} → 0 and f_α is bounded near 0 — classical: all stable densities are bounded (equivalently, the Zolotarev small-argument asymptotic f_α(x) = O(x^{−β}e^{−γx^{−α/(1−α)}}) as x↓0) — so the integrand is O(e^{−2u}). The m-fold product is dominated coordinatewise, so Andreief's hypothesis ∫_{ℝ^m} |D_x D_y| ∏e^{−2u_j} du < ∞ holds. Note entrywise finiteness is already a byproduct of Lemma 3.1 (Tonelli + h∗h~ ∈ C₀).)*

Everything else in PROOF.md stands as written.

---

## 4. SUBSTANTIVE gate — could a generic theorem make this routine? **PASS**

The brief demands inspection of actual accessible primary bodies and an explicit bridge, not inference from an open label. Findings:

1. **Exact reduction chain (my independent observation).** From Lemma 3.1 + the algebra check, K_α(e^{αx}, e^{αy}) = (π/sinπα)·e^{−α(x+y)}·J_α(x−y) with J_α(d) = sin(πα)/(2π(cosh(αd)+cos(πα))) = α·g_α(αd), g_α being the *generalized logistic density whose PF∞ characterization is Proposition 1 of 1305.1173 itself*. Since t ↦ e^{αx} is an increasing bijection, and row/column rescalings and argument rescalings preserve TP_n/STP_n, the conjecture is **equivalent** to: g_α ∈ SPF_n (strict Pólya frequency of order n, in Simon's own notation). So the target is exactly the strict upgrade of a PF_n classification — there is no shorter object to hit.
2. **Generic strict composition formulas do not apply.** The strict basic composition formula requires *both* factors STP_n. In the source's printed factorization the factor A(x,u) = f_α(e^{x−u}) is known TP_n (Theorem 1) but its **strictness is equivalent to the target itself** (A(x,u) = f_α(e^x e^{−u}); via the same rescaling equivalences, STP_n of A ⟺ STP_n of J_α(x−y) ⟺ the conjecture). Applying a strict composition theorem would therefore beg the question. Accessible statements of the basic composition formula (Belton–Guillot–Khare–Putinar, arXiv:2006.16213/2110.08206, §2; Khare's TN-note) confirm the TP-only conclusion; the source's own Remark 1 records that strict variants fail for its factors. **Karlin (1968) and Pinkus (2010) book bodies were not accessible to me — recorded candidly; this residual risk is documented, not cleared.**
3. **The most tempting generic shortcut is provably void.** A theorem of the shape "f ∈ PF_n with nonvanishing Fourier transform (equivalently, linearly independent translates) ⇒ f(x−y) STP_n" does **not exist**: take f = e^{−|x|}, which is PF∞ (Laplace distribution is a Gaussian variance mixture, Schoenberg) and has f̂(ξ) = 2/(1+ξ²) ≠ 0 everywhere, yet det[e^{−|x_i−y_j|}] = e^{−5}e^{−5} − e^{−4}e^{−6} = 0 **exactly** at (x_1−y_1, x_1−y_2, x_2−y_2, x_2−y_1) = (5, 4, 5, 6), a valid ordered configuration (checker Check F). The culprit — exact cancellation on the linear pieces of log f — is precisely what the candidate's Lemma 5.1 rules out for g_α via the nonvanishing of the first m series coefficients. Any applicable generic theorem would need hypotheses specific to this exponential-sum structure, i.e., would *contain* Lemma 5.1.
4. **The source's own remark does not cover this route.** 1412.0132 Remark 2(b) says the *additive* fractional-integration factorization (through I_β, which has support zeros) "cannot help" for strictness. The *multiplicative Gram* factorization ∫f_αf_αe^{−2u} printed in the source's §2.2 is a different object with strictly positive entries, and the source did not push it to strictness. The candidate completes exactly that route; it contradicts nothing in the source.
5. **The leading-layer technique is the source's own.** The source's §2.3/§2.4 proofs (Theorem 2, only-if part) use the same mechanism as Lemma 5.1 — multilinear expansion of a determinant of a sum, leading term from pairwise-distinct orders, permutation-sum collapse into a product of two determinants, positivity of ∏ sin(πjρ). So the *technique* is not new; what is new is its use to prove a **positive** nondegeneracy statement (D_x ≢ 0) feeding a strictification lemma, rather than a contradiction. This lowers the "genius bar" but does not make the outcome a routine corollary of a printed theorem: no printed theorem states or implies D_x ≢ 0, and the whole point of Conjecture (2) is that no printed route reached strictness.
6. Checked also: preserver-classification paper 2006.16213 (postcomposition operators; inapplicable), hyperdeterminantal TP (2412.03000/SIGMA 2025; different object), spectral-Darboux strictification 2607.02778 (Bessel/PF sequences; does not cover Cauchy/stable kernels) — consistent with the worker's screen, which I re-examined rather than inherited.

**SUBSTANTIVE: PASS** — the upgrade from the source's own printed TP factorization to strictness requires exactly the candidate's nondegeneracy input; no generic black box supplies it.

---

## 5. NOVELTY gate — bounded fresh screens, 2026-10-28 (this lane) — **PASS**

- **MathDB 325521 refetched live** (https://mathdb.com/api/posts/325521): `status: "open"`, `solutions: []`, `comments: []`, `model_attempts: []`. Empty status not treated as novelty evidence by itself.
- **Semantic Scholar, fresh queries this lane:** DOI:10.1016/j.jat.2014.05.014 → 7 citing papers (2608.28376, 2607.02828, 2205.15742, 1412.0132 ×2 records, 1604.05267, 1207.6464) — none resolves the strict conjecture (titles/abstract level; the two 2026 items are on line restrictions of charge potentials and a Weil quadratic-form dictionary). arXiv:1412.0132 → 1 citation (1604.05267), obtained on the third attempt after two 429 rate-limit responses (backed off; no retry storm); matches the worker's dump.
- **Author corpus (live):** https://pro.univ-lille.fr/thomas-simon/publications — #40 is *Total positivity in stable semigroups* (Constr. Approx. 2016); no later total-positivity paper; no retraction/resolution. Kwaśnicki–Simon arXiv:1910.07752 checked (bell-shaped functions characterization; unrelated — abstract read). Simon–Bosch 1411.3369 (Bondesson conjecture) unrelated.
- **Registries:** MaRDI item Q2016141 (no resolution field); zbMATH snippet for the JAT paper records 4 citations, none flagged as resolving; no MathSciNet access (subscription) — recorded.
- **Targeted web searches** (multiple phrasings: conjecture + "resolved", strict PF + stable, strict composition formula statements): nothing resolving; nothing even restating Conjecture (2) with a proof.
- **Published journal bodies:** JAT 234 (2018) 238–258 and Constr. Approx. 44 (2016) 103–120 full bodies **not read** (paywalls); publisher-indexed snippets still display the conjecture and the TP classification unchanged. Access limit recorded; no clearance inferred from abstracts.
- First-batch 30 outcomes and ledger: none touches Cauchy/stable kernels or strict TP (prior-campaign-context.json read).

**NOVELTY: PASS** within the bounded protocol; no worldwide-priority claim is made or certified.

---

## 6. FORMAL scope/cost (assessment only; nothing started)

A literal Lean endpoint (lean4/mathlib, only Propext/Classical.choice/Quot.sound) requires, with no residual bridges:

1. **Theorem A** (Simon's TP_n classification): local limit theorem for the log-Beta-product densities (Fourier estimates via Stirling, dominated convergence), the reduction through Karlin's Theorem 1.2.1, and TP_n of (y−x)₊^{1/α−2} (Karlin 3.2.1/10.1.1 — itself to be reproved). Dominant cost: **months**. Unavoidable in the Gram route (D_x ≥ 0 comes from it).
2. **Theorem B**: the Zolotarev series plus the proof that it *equals* the stable density (Mellin inversion against e^{−λ^α} — must be proven, not assumed), and its absolute local-uniform convergence.
3. **Mellin/Fourier facts**: Γ(1+is)/Γ(1+iαs), |Γ(1+iu)|² = πu/sinh(πu), Fourier uniqueness on L¹.
4. Andreief + Fubini over ℝ^m; 5. identity theorem/analytic zero sets; 6. the corrected Lemma 5.1 asymptotics with the Correction-3 tail bound; 7. bookkeeping m ≤ n, αm < 1.

**Alternate direct proof avoiding Theorem A: searched, not found.** In log coordinates the target is STP_n of the explicit rational-exponential kernel J_α(x−y) ∝ e^{−αd}/(1 + 2cos(πα)e^{−αd} + e^{−2αd}); a direct proof of det[J_α(x_i−y_j)] ≥ 0 would itself be a PF_n statement for J_α equivalent to Theorem A (rescaling equivalence chain of §4.1), and partial fractions 1/((t+e^{iπα}x)(t+e^{−iπα}x)) lead to complex Cauchy kernels whose combination does not preserve positivity. So the worker's months-scale estimate stands, dominated by items 1–2. No formal work was started — correct per the brief (no huge formalization before eligibility).

---

## 7. Exact remaining gaps (post-repair)

1. **Theorem A consumed as a black box** — the proof's only substantive external input; must be reproduced in full for any formal endpoint, and its *published* (Constr. Approx.) text was never read by anyone in this campaign (paywall). Mitigation: the statement is verbatim-identical in arXiv v1 HTML, the MathDB record, and the publisher snippet; risk is low but nonzero.
2. **Karlin (1968) / Pinkus (2010) book bodies unread** — the nonexistence of a covering strict-composition theorem rests on accessible secondary statements + the §4 counterexample, not on a full book scan. Residual: a book theorem with exactly the needed nondegeneracy hypothesis could exist; it would *contain* Lemma 5.1 and would have to be cited, not used as a black box without reading.
3. **Zolotarev/Sato series identity** rests on Sato (14.30) (book not accessible here); repaired in-review by the α = 1/2 closed-form match and the Mellin-inversion route that a formalization must anyway take.
4. The two corrections to displayed identities (m-prefactor, ∏z_i^α) must be propagated into any paper/formal text derived from the frozen candidate.

---

## 8. Provenance, diagnostics, integrity

See `provenance.json` in this lane: all URLs, hashes, dates, rate-limit events, and access limits. Independent diagnostics: `scripts/check_review.py` + `scripts/check_review_log.txt` (checks A–F above; the frozen candidate was not modified). Freeze hashes reverified after writing this review — see provenance.json `freeze_hashes_after`.

**No acceptance, no count, no paper, no packet, no external actions.** Two sibling tasks (Mittag preliminary review; short-thread parity research) were not polled or read.
