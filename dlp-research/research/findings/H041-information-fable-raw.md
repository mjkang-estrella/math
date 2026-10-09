# H041 adaptive information — raw Factory Fable report

Unaccepted proposer report; several scope and cost claims require independent review.
Provider usage footer is an unverified local estimate, not research evidence.
Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h041-adaptive-information-fable-20261008-r1`

# H041 independent ideation: constructive adaptive information acquisition

**Role.** Factory `claude-fable-5.1`, read-only. Read RESEARCH_LOOP.md, RESEARCH_TEAM.md, STATE.md (live H040/H039 sections and history), H040 information/geometry/tangent dispositions and briefs, H040 and H036 Factory raw reports, H039 information disposition, H038 bounded-recovery graphs, H019 information disposition, H013 MCL disposition, H003 noisy-recovery disposition, plus keyword sweeps across findings. No H041 proposal files exist in the tree, so none were read. No runs of solver code, imports, edits, children or commits. One read-only `curl | pdftotext` was used for a primary source (below).

**Verdict: no new operation emerges from this lens.** Verified improvement remains NONE; exponent 1/2 unchanged. I examined six adaptive-acquisition operations. One is a genuinely changed operation with a clean, narrow paper falsifier; one is a small constructive repair of the H040 signed-membership issue with no gain; the rest reduce to recorded gates. I am not submitting cards, and I am not asserting a universal exclusion.

## Primary read

Kohel–Shparlinski, *Exponential sums and group generators for elliptic curves over finite fields*, Section 3, fresh read via `curl ... | pdftotext` (FetchUrl rejected the PDF as binary; the shell read succeeded). Theorem 1: for ω an unramified group character and ψ∘f an Artin–Schreier character of a nonconstant f ∈ F_q(E), |S(ω,ψ,f)| ≤ Σ m_i deg(P_i) q^{1/2} over the polar divisor, hence inequality (3) |S| ≤ 2 deg(f) q^{1/2}; Corollary 1 transfers the same bound to any subgroup H (their q is our p). This is the only attributed technical claim below; the Kummer-character analogue I use for Legendre-type features is standard Weil/Bombieri, not freshly read.

## Operation 1 (changed operation, rejected on paper): second-moment "autocorrelation lock" through public dilations

**Public function and query rule.** Fix a cheap feature f: E → C, |f| ≤ 1 (bits of x, Legendre of x, e(ux(P)/p), or a bounded product). For chosen c ∈ F_q^* and uniform d, compute both Q + [d]G = [k+d]G and [c]Q + [d]G = [ck+d]G, and estimate

$$A_k(c) := \mathbb{E}_d\, f(Q+[d]G)\,\overline{f([c]Q+[d]G)} = R_F\big((c-1)k\big),\qquad R_F(\tau)=\mathbb{E}_n F(n)\overline{F(n+\tau)} .$$

This is a different statistic from every recorded decoder: it never estimates a scalar character phase, so the H040 calibration/confidence invoice does not apply. It is a membership test of (c−1)k in the "peak set" T_F = {τ ≠ 0 : |R_F(τ)| ≥ ε}, at cost ε^{-2} samples per c. Complete decoder: sweep c (or a random subset), detect a peak, recover k = τ/(c−1) for each candidate τ ∈ T_F, verify by one scalar multiplication. Potential gain under the idealized model: q·ε^{-2}/|T_F| total, beating √q iff |T_F|·ε² > √q, needing a public sequence with many high autocorrelation peaks at known lags (T_F is public and precomputable only if it can be found without a full q-length FFT).

**Why it fails (cheapest decisive falsifier, done).** For f with additive Fourier expansion f = Σ_u f̂(u) ψ_u∘x, the lag-τ autocorrelation is Σ_{u,v} f̂(u)f̂(v)·(1/q)Σ_P ψ(u x(P) + v x(P+T)) with T = [τ]G ≠ O. For (u,v) ≠ (0,0) the function u·x + v·x∘τ_T has poles only at O and/or −T, which cannot cancel, so it is nonconstant of degree ≤ 4; Corollary 1 gives |·| ≤ 8√p/q per term. Hence |R_F(τ)| ≤ 8·L1(f)²·√p/q for every τ ≠ 0 up to the DC term: no peaks, and with L1(bit) = O(log² p) (H019 lemma) the peak set is empty for the whole bounded-degree, bounded-L1 class. For Kummer-type f = χ(g(P)) the lag-τ sum degenerates only if g·(g∘τ_T) is a square in F_p(E), which requires the zero/pole set of g to be invariant under translation by T, i.e., T ∈ E[deg g]; in a prime-order group with deg g < q that forces T = O. So this is a narrow, checkable negative for pair statistics of bounded-degree features in prime-order groups, not a generic lower bound. Higher moments f(P)f(P+T₁)f(P+T₂) face the same divisor-invariance obstruction; I did not formalize them. No experiment is warranted.

## Operation 2 (remark, no gain): oriented interval bisection repairing H040's signed membership

H040 correctly withdrew the bisection because ∏_{j∈J}(x(Q−[a]G) − x([j]G)) = 0 tests k−a ∈ J ∪ (−J). The repair is a shift placement rule, not a new polynomial: once the prior interval has length ≤ q/2, anchor the test at its left endpoint. With prior k ∈ [u, u+2L] and J = [1, L], a hit at shift a = u means k ∈ ([u−L,u−1] ∪ [u+1,u+L]) ∩ [u,u+2L] = [u+1,u+L]; a miss means k ∈ {u} ∪ [u+L+1,u+2L]. The mirror set lies outside the prior, so one sign-blind test per level orients. Handle k = a by a direct equality check with O. Only the first level (prior = all of Z/q) needs one extra test to break the ± symmetry.

Full cost: Σ_i Õ(√(q/2^i)) ≈ 2.41·√q sqrt-Vélu/resultant evaluations (BDLS, root-read in H019) plus polylog factors, memory Õ(√q) at the first level, deterministic. This matches the H040 Opus count but now with a valid recovery invariant. It loses to BSGS and rho by polylog and constant factors; nothing about the exponent changes. I record it only so the open "a repaired search would need sign/orientation" item is closed concretely.

## Operations considered and not carded

| Operation | Why not a card |
|---|---|
| Kushilevitz–Mansour-style adaptive heavy-coefficient search on g(d) = f([k+d]G), then HNP/lattice decoding of the recovered phases | Adaptivity only manages queries; the signal is still |c_a(F)| ≤ 2 deg(f)·L1·√p/q (fresh KS read), so the same b < 1/4 gate as H003/H040. No named feature passes; H019 A1 shows adaptivity cannot beat channel capacity in the narrow oracle model. |
| Detectable-scalar-property self-reduction: random derived instances [c]Q + [d]G, detect a public property Π of the scalar (interval, coset, small-x, smoothness), decode | General ledger C_Π/ρ_Π + D_Π. Interval: √T·(q/T) ≥ √q. Coset: needs the character phase (H013). Small-x: the table of small-x points lacks logs, so building it is BSGS. Smoothness: undetectable from the point. Each collapses to H039's parked table/rho hybrid or to BSGS. |
| Reading k mod ℓ from the action of "the endomorphism sending G to Q" on E[ℓ] | Same obstruction as the H040 tangent screen: [k] and [k+q] agree on ⟨G⟩ but differ on E[ℓ]; (G,Q) does not determine the torsion action. Not resubmitted. |
| Learned window decoder h(f([k+d₁]G),…,f([k+d_w]G)) → bits of k, trained on known n | Equivalent to the H019 C2 small-circuit hypothesis; the only non-generic training prior is algebraic, which returns to characters. Excluded by the brief as inverse-table retraining in effect. |
| Window fingerprints / DP arrival patterns as compressed tame-wild match keys | Memory-per-entry saving only; H013 block-fingerprint and H033 retrieval records already cover it. |

## Missing operation, stated once

Every adaptive acquisition rule I can write reduces to evaluating translation-invariant algebra (addition formulas, summation polynomials, pair/autocorrelation statistics) on points whose only non-invariant datum is the position itself. First-order character correlations are bounded by the fresh KS read; second-order pair statistics are bounded by the same theorem via the divisor argument above. A new mechanism would need a public statistic of the window that is not translation-invariant and not a character phase, with a decoder cheaper than √(1/density). I do not have one, and I am not claiming none exists.

**Status for root.** No candidate admitted; no experiment proposed. Access note: FetchUrl cannot read PDFs; the primary source was read through a read-only shell pipe with no file written. Provider/model actually run: Factory `claude-fable-5.1`.

---
*Factory usage — local bridge. This turn: 1,021,211 tokens · ≈1,233,527 Factory credits. Saved session total: 1,021,211 tokens · ≈1,233,527 Factory credits (including recorded subagents). Credits are a local estimate, not a dollar charge.*
