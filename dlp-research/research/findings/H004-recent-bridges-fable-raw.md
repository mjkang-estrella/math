Root caution: unverified proposer report. Several universal exclusions, degree/field
estimates, and the final character/sample-size inference need independent review;
they are NOT accepted research findings or new impossibility theorems.

# H005 recent-result bridge round (Fable, r2): final report

**Outcome: no survivor.** I evaluated four concrete routes drawn from recent primary algebraic/algorithmic results, each with an explicit procedure on (G, Q), the exact theorem and hypotheses, a cost accounting and the decisive failure point. None reduces complete classical work below the matched √q baseline, and none merits a funded experiment. I also record one cross-cutting source-backed ceiling that tightens the H003 character bound, and a scan of 2024–2026 literature that found no new classical ECDLP result for ordinary prime-field prime-order curves.

Scope compliance: read-only. No edits, experiments, scratch arithmetic, children or provider calls. I read `RESEARCH_LOOP.md`, `STATE.md`, the H001/H002 cards and registers, `H003-lift-section-development.md`, `H004-practical-initial-proposals.md`; I did not read any H005 proposals. Public PDFs were downloaded to `/tmp/ecdlp_src/` (outside the repo) for text extraction; eprint.iacr.org PDFs are Cloudflare-blocked from this host, so I used the authors' mirrors or the HTML/abstract pages. Local `curl` needed `-k` because the host CA bundle is broken; nothing was uploaded.

Notation: E/F_p ordinary, #E(F_p) = q prime, G generates, Q = kG, π = Frobenius, O = End(E) with E(F_p) = E[π−1] ≅ O/(π−1) ≅ Z/q.

---

## Card 1. Higher-dimensional isogeny interpolation applied to the unknown scalar endomorphism

**Source (retrieved).** D. Robert, *Breaking SIDH in polynomial time*, Eurocrypt 2023, https://eprint.iacr.org/2022/1038 (mirror text read). Theorem 1.1, verbatim hypotheses: given coprime N_A > N_B with known factorisations, a decomposition N_A − N_B = a₁²+a₂²+a₃²+a₄², an N_B-isogeny φ_B: E₀ → E_B over F_Q, **E₀[N_A] ⊂ E₀(F_Q) with a basis (P₁, P₂) and the images φ_B(P₁), φ_B(P₂)**; then Eval returns φ_B(P) for any P in Õ(ℓ_A⁸ log N_A) F_Q-operations (ℓ_A = largest prime of N_A); ComputeKernel recovers Ker φ_B if additionally Ker φ_B ⊂ E₀[N_B](F_Q) with a known basis. Remark 1.2: N_A² > N_B suffices via the dual. The "embedding lemma": any N-isogeny embeds in an N'-isogeny of dimension 8g for any N' > N. Companion: Robert, https://eprint.iacr.org/2022/1704 gives polynomial-time End(E) for ordinary E given the factorisation of Δ_π.

**Procedure on (G, Q) (my bridge attempt).** Treat the unknown map as φ = [k] (degree k²), or as the minimal-degree α ∈ k + (π−1)O (which acts as k on E(F_p)), or as the kernel isogeny E² → E²/⟨(G,Q)⟩ (the H002 V1 object). Apply Theorem 1.1 to reconstruct φ as an evaluable 8-dimensional isogeny, evaluate it on E[ℓ] for small ℓ, read k mod ℓ by small DLPs, CRT.

**Where it fails (checkable, three independent reasons).**
1. Input format. Theorem 1.1 needs φ on a **basis of full N-torsion**. ECDLP supplies φ(G) for one point of a cyclic group. E[N] has N² points, so E[N] ⊄ E(F_p) for every N > 1 when #E(F_p) = q is prime. Over F_{p^m} the full N-torsion requires π^m ≡ 1 on E[N]; for a random curve m is of order N. We also cannot compute [k]P₁ without k, so the images are unavailable in any case.
2. Degree. deg[k] ≈ q²; the minimal degree in the coset k + (π−1)O is heuristically Θ(q·|Δ_O|^{1/2}) ≈ q^{3/2} for |Δ_O| ≈ p. Either way N_A > deg (or N_A² > deg) forces N_A ≳ q, smooth, with rational full torsion: a field of size roughly p^{Θ(q)}.
3. Even with End(E) known (2022/1704), every endomorphism acts on E(F_p) as a scalar λ(α) = α mod (π−1), computable ring-theoretically (π ↦ 1). Evaluating α buys nothing: finding α with λ(α) = k is the DLP restated. This also re-confirms the H002 A3 verdict without rebranding it.

**Cost.** Not applicable; no executable instance exists. **Unsupported assumption:** none left to test. **Falsifier:** the hypothesis table above is decisive at zero compute; do not fund.

---

## Card 2. Structured-factor-base index calculus over F_p (multiplicative subgroup / auxiliary-isogeny kernel coset)

I independently rederived this before locating the source: factor base F = {P : x(P) ∈ μ_h} for a subgroup μ_h ⊂ F_p^*, so membership is x^h = 1 (a sparse constraint), and a 2-decomposition test for all x₁ in a known-log list against μ_h can be done by a Lucas-sequence resultant modulo F_{L₁}(X) in Õ(|L₁| log h) without enumerating μ_h.

**Source (retrieved).** Petit–Kosters–Messeng, *Algebraic approaches for the ECDLP over prime fields*, PKC 2016, https://christophe.petit.web.ulb.be/files/16PKC_primeECDLP.pdf. This is exactly their framework: factor base {(x,y) : L(x) = 0} with L a composition of low-degree maps L_j; instance 1 takes L_j(x) = x^{p_j} with Π p_j ≈ p^{1/m} a smooth divisor of p−1 (roots = a subgroup/coset of F_p^*); instance 2 (general p) uses an auxiliary curve E'/F_p with a smooth subgroup H of order ≈ p^{1/m} and L_j = x-maps of Vélu isogenies, Lemma 1 giving exactly Π p_j roots. Algorithm 1 and cost: P(p,m) + m!·p/(deg L)^{m−1}·T(E,m,L) + (deg L)^ω; beats p^{1/2} only if the decomposition system is solved in T ≪ p^{1/2−1/m} when (deg L)^m ≈ m!·p. The authors state: "The complexity of our algorithms remains an open problem … at the moment all attacks are outperformed by generic discrete logarithm algorithms for practically relevant parameters."
Follow-ups: Amadori–Pintore–Sala 2018 (https://eprint.iacr.org/2017/609); Kudo–Yokota–Takahashi–Yasuda, CANS 2018, https://doi.org/10.1007/978-3-030-00434-7_19 (hybrid + symmetries; "a limitation of our acceleration in both theory and practice"); Yokoyama–Yasuda–Takahashi–Kogure, JMC 2020, https://doi.org/10.1515/jmc-2019-0029: under stated statistical assumptions on summation polynomials, a Gröbner lower bound proving the naive (interval) index calculus "cannot be more efficient than generic methods"; Huang–Kosters–Petit–Yeo–Yun, *Quasi-subfield polynomials*, JMC 2020, https://doi.org/10.1515/jmc-2015-0049: multiplicative/additive subgroups are argued (statistically) not to yield quasi-subfield polynomials beating generic bounds; existence remains open and the construction is for F_{q^n} with n' < n, so it degenerates for n = 1.

**My sharpening (inference, not from the sources).** For m = 2 the algebraic join above costs Õ(|L₁| log h) per target, i.e. the same as testing each candidate directly (one exponentiation or one hash); algebraic joins never beat hashing for 2-decompositions, so the per-relation cost is ≥ p/|F| and the birthday over F gives total ≥ Õ(p/√|F|) ≥ Õ(√p). For m ≥ 3 the gain must come entirely from solving the chained system faster than its Bézout count ≈ (2^{m−1})^m·m!·p; this is the open gap, and Yokoyama et al. close it negatively for intervals under their assumptions.

**Cost.** Setup P(p,m) (auxiliary smooth-order curve: ≈ p^{1/m} random trials per PKM Table 1); relation phase as above; linear algebra (deg L)^ω with deg L ≈ p^{1/m}. **Unsupported assumption:** a dedicated solver for the smooth-chain system at p^{o(1)}·poly. **Falsifier:** already published (Kudo et al. experiments and complexity analysis). Not worth a new run; a 60-second toy Gröbner timing could not change the asymptotic verdict.

---

## Card 3. Representation technique transferred from F_{p²} to F_p

**Source (retrieved).** Delaplace–May, *Can we beat the square root bound for ECDLP over F_{p²} via representation?*, NuTMiC 2019 / JMC 2020, https://eprint.iacr.org/2019/800, https://doi.org/10.1515/jmc-2019-0025. Lemma 3.1: k has ≥ p−1 representations k = k₁ + k₂ with (k₁,k₂) ∈ S₁×S₂; they keep only points whose x lies in the subfield F_p (density 1/p), giving lists of expected size p^{1/2}; ECDLP reduces to a Zero-Join problem (pairs (A×B) with f(x₁,y₁,x₂,y₂) = 0, |A|·|B| = p^{3/2}); bivariate multi-evaluation gives p^{1.314}, inferior to rho's O(p); they state the list computation "is yet too costly". No follow-up improving the Zero-Join step surfaced in my search.

**Procedure on (G, Q) (my transfer).** Split k = k₁ + k₂ over S₁×S₂ with |S₁||S₂| = qR, apply a coordinate filter of density 1/R, build L = {k₁G : filter} and L' = {Q − k₂G : filter}, join.

**Where it fails (inference).** Over F_p there is no subfield; the filter must be a coordinate condition such as x ∈ [0, p/R). Generating the filtered known-log lists costs ≥ |S₁| + |S₂| ≥ 2√(qR) ≥ 2√q tests, because the filter cannot be inverted on scalars. Generating filter-passing points directly (choose x, solve for y) loses the scalar label, which turns the method into unknown-log factor-base index calculus, i.e. Card 2 with an interval (the case Yokoyama et al. bound). The Zero-Join speedups act only after the lists exist. **Cost:** ≥ 2√q before any join. **Unsupported assumption:** an invertible coordinate filter. **Falsifier:** the inequality above; nothing to run.

---

## Card 4. "Minors solve ECDLP" (recent primary claim, 2018–2023)

**Source (retrieved).** Abdullah–Mahalanobis, arXiv:2310.04132 (Oct 2023), https://arxiv.org/abs/2310.04132; earlier Mahalanobis–Mallick–Abdullah INDOCRYPT 2018 and JGCC 2021 (https://arxiv.org/abs/2005.05039). Theorem 2.1: d = 3n' points of E lie on a degree-n' plane curve not containing E iff they sum to O. Theorem 2.2: with d + l random points n_iP and −n_jQ, the left kernel K of the (d+l)×C(n'+2,2) monomial-evaluation matrix has dimension l, and a kernel vector with exactly l zeros exhibits d points summing to O, hence Σn_i − m·Σn_j ≡ 0 gives m. Theorem 3.1: zero minors of the dense l×l block A correspond to such vectors. They search polynomial-size minor families ("almost principal minors", O(l^{2n+1}) for n deviations), report ≈1 kernel on average for binary fields of 28–47 bits, and conjecture "initial minors" exist ("can yield to a polynomial time algorithm").

**Assessment (my counting, not in the source).** Each l-subset of the 2l points determines a unique candidate m (ratio of the two scalar sums); a zero minor merely certifies one subset. Testing a minor (≈ l^ω field ops) is therefore a more expensive version of computing the candidate m and checking mG = Q (O(log q) group ops). Random 2l points have C(2l,l)/p ≈ 4^l/(p√l) zero-sum l-subsets, abundant for l ≈ 3 log₂ p, but a fixed family of F minors contains one with expected count F/p. Their regime: l ≈ 3·46 to 9·46 (they list 414 rows at 2^46), so l⁵ ≈ 2^{43} and l⁷ ≈ 2^{61} versus p ≈ 2^{40}–2^{47}. This exactly matches their tables: two deviations (l⁵ family) suffice up to ~44 bits and then fail, three deviations (l⁷) suffice to 47 bits. Asymptotically kernels needed ≈ p/l^{2n+1}, exponential, with per-kernel cost polynomial: total work ≫ √q. The approach is a disguised exhaustive search over candidate m, and over F_p it is dominated by rho.

**Cost.** Per kernel: O((d+l)·C(n'+2,2)·ω) linear algebra plus l^{2n+1} minor tests, each l^ω; kernels ≈ max(1, p/l^{2n+1}). **Unsupported assumption:** the "initial minors" conjecture, which (if true) would only let one detect that *some* zero minor exists, not locate the subset. **Falsifier:** their own Tables 1–2 and the 2-vs-3-deviation transition already exhibit the predicted exponential growth; a local reproduction at 20–30 bits with fixed deviation count would show kernel count ≈ p/l^{2n+1}, but I recommend not spending even that.

---

## Cross-cutting ceiling (tightens H003, source-backed)

**Source (retrieved).** Kohel–Shparlinski, *On exponential sums and group generators for elliptic curves over finite fields*, ANTS 2000, https://www.i2m.univ-amu.fr/perso/david.kohel/pub/character.pdf. Theorem 1: for any nontrivial character ω of the group E(F_q), additive character ψ of F_q, and f ∈ F_q(E) with poles only at O, |Σ_{P∈E(F_q)} ω(P)ψ(f(P))| ≤ 2 deg(f)·q^{1/2}. Theorem 2: for any interval I and character ω of order m, |T(I,f,ω) − N(m−1)|I|/(mq)| ≤ 2(1+deg f)(1+log p)q^{1/2}. Related: Lange–Shparlinski, *Certain exponential sums and random walks on elliptic curves*, Canad. J. Math. 2005; Kim–Tibouchi, *Equidistribution among cosets of elliptic curve points in intervals*, JMC 2020, https://doi.org/10.1515/jmc-2019-0020.

**Consequence (my inference).** For prime-order E(F_p), group characters are ω_a(nG) = e(an/q), so Theorem 1 says every scalar-frequency Fourier coefficient of every fixed bounded-degree coordinate feature ψ∘f has normalised amplitude ≤ 2 deg(f)/√q, for all frequencies at once, not only the EDS/Kronecker features of H003. Any orientation or correlation scheme using such a feature with bias ε on a window of L scalars needs L ≳ ε^{-2} samples while ε ≲ deg(f)·√p/L, forcing L ≳ p. Compact high-degree features (degree ≳ ε√q) are not excluded by this, which is consistent with the loop's standing caveat; but it rules out the whole class of fixed low-degree coordinate statistics with one theorem, so future proposals in that class can be rejected without new experiments.

---

## 2024–2026 scan (what I looked for and did not find)

Searches for new classical ECDLP algorithms, summation-polynomial/point-decomposition advances, lifting/p-adic routes, Zero-Join follow-ups and preprocessing/multi-target improvements returned no primary classical result for ordinary prime-field prime-order curves newer than the 2018–2020 items above. Recent hits were quantum resource estimates (arXiv 2607.13816, arXiv 2604.02311, eprint 2026/280), curve-construction work (eprint 2025/1751, "very strong" curves, no new attack) and the 2023 minors preprint (Card 4). Sparse-polynomial root-finding advances (Bi–Cheng–Rojas line) do not bridge: ECDLP has no monomial structure analogous to x^n in F_p^*.

## Five-item summary for STATE

1. Best supported work: unchanged, classical √q with known automorphism constants and charged preprocessing/memory/multi-target.
2. Verified improvement: **NONE**; this round adds four reasoned rejections and one general ceiling.
3. Hypothesis tested: that a recent primary algebraic/combinatorial result admits an executable ECDLP bridge. Rejected for Kani/Robert interpolation (hypotheses unsatisfiable by ECDLP input), PKM-type structured factor bases (open complexity, negative bounds, algebraic joins no better than hashing), representation technique (list generation ≥ 2√q or collapses to index calculus), and the minors method (exhaustive search in disguise, counting matches their tables).
4. Evidence: primary theorem statements quoted with URLs above; my inferences are labelled.
5. Next conclusion-changing step: none from this lens. Reopening would require a coordinate feature of degree ≳ √q that is nonetheless compactly evaluable and provably biased, or a decomposition solver beating the Bézout count for PKM chains; neither has a source. No experiment is proposed or funded.
