# H013 MCL bound review — raw, qualified by root disposition

2026-10-08. Claude Opus5.5 completed new independent review. This raw report
contains claims requiring scope corrections; see H013-mcl-disposition.md.
No numerical experiment or validated attack gain.

# Review of H013-MCL: the q^(-1/12) bound and prior art

**Verdict:**
- The q^(-1/12) bound is correct, with conditions I list below.
- It is not new. It is the ν=1 case of a published Ahmadi–Shparlinski bilinear bound.
- It only covers bounded-degree algebraic features, and it does not rule out the correlation size the card needs.
- **Verified gain: NONE.**

I worked read-only: no edits, no experiments, no installations, no subagents.

## 1. Re-deriving the bound

**Setup.** E is over F_p with p ≥ 5, and G has prime order q. ψ is a nontrivial additive character of F_p. F(n) = ψ(x(nG)). χ is a character of Z_q^*. S = Σ_{n∈Z_q^*} χ(n)F(n).

1. **Shift identity.** For 1 ≤ v ≤ V < q, the map n ↦ nv is a bijection of Z_q^*. So S = χ(v)·Σ_n χ(n)F(nv), and F(nv) = ψ((x∘[v])(nG)). Correct.
2. **Averaging and Cauchy.** V|S| ≤ Σ_n |Σ_v χ(v)F(nv)| ≤ √q·(Σ_{v,v'} |Σ_n F(nv)·conj(F(nv'))|)^{1/2}.
   - The diagonal contributes V(q−1).
   - Each off-diagonal pair contributes |Σ_{P≠O} ψ(h(P))|, where h = x∘[v] − x∘[v'].
3. **Conjugates and normalization.** These are harmless.
   - The card defines c_χ with conj(χ), and S uses χ. Swapping χ for conj(χ) keeps the order m.
   - The argument only uses |χ(v)| = 1 and multiplicativity. So the bound holds uniformly over every χ, trivial character included. For χ₀ it reduces to a plain O(√p) sum, which is a good sanity check.
   - If f is merely bounded instead of unimodular, the diagonal becomes V·Σ|f|².
4. **Small v gives a nonconstant h, and the Artin–Schreier exception is ruled out.** Take 1 ≤ v < v' ≤ V with V² ≪ p.
   - h is nonconstant because deg(x∘[v']) = 2v'² > 2v² = deg(x∘[v]).
   - The poles of h lie on E[v] ∪ E[v'], each of order exactly 2.
   - At a common pole T, the local expansion has leading coefficient (v⁻² − v'⁻²)z⁻². This is nonzero mod p because 0 < v < v' < p.
   - Every pole order is 2 < p, so h cannot have the form g^p − g + c.
   - Since q is prime and greater than V, the only F_p-rational pole on ⟨G⟩ is O, and the sum excludes O.
5. **Weil bound.** I recomputed it with Riemann–Hurwitz on y^p − y = h over a genus-1 curve.
   - Each nontrivial character sum is at most (deg h + r)√p, where r is the number of geometric poles.
   - That gives at most 3(v² + v'²)√p ≤ 6V²√p, which is within the 2·deg·√p ≤ 8V²√p the card uses.
   - **Caveat:** I did not read the Kohel–Shparlinski primary paper. The constant comes from my own computation.
6. **Result.** |S|² ≤ q²/V + 8qV²√p.
   - The optimum is V³ = q/(8√p). When q ≈ p this is V ≈ q^{1/6}/2, giving |S|² ≤ 4q^{11/6}, so |S|/(q−1) ≲ 2q^{-1/12}. The arithmetic checks out.
   - **This depends on q ≈ p.** With a cofactor, q ~ p/h and the exponent gets worse. The bound needs q ≥ 8√p just to give V ≥ 1.
   - Hölder with a 2k-th moment does not help. I get q^{-1/(4(k+2))}, so k=1 is optimal for this method.
7. **Fourier-ℓ¹ dependence.** For f = Φ∘x, the a=0 Fourier term vanishes for nontrivial χ, so |c_χ| ≤ ‖Φ̂‖_{ℓ¹, a≠0}·2q^{-1/12}.
   - For an arbitrary Boolean Φ, ‖Φ̂‖_{ℓ¹} can be as large as ~√p, and then the bound is vacuous.
   - The ℓ¹ norm of integer-representation bits has to be computed; it cannot be assumed small.
   - y-dependent or higher-degree rational h of degree d scale the off-diagonal by d.
   - Multi-view products with a multiplier u push the degree to ~u²V², so the bound collapses once u exceeds roughly q^{1/12}.
8. **The odd-character null holds exactly.** x(−nG) = x(nG) gives S = χ(−1)S. Also, (q−1)/m odd already forces m even, so the condition is self-consistent.

## 2. Prior art: the bound is a known corollary

Ahmadi–Shparlinski (arXiv 1302.4210v3, Lemma 2) quotes their earlier result, Proc. Edinb. Math. Soc. 53 (2010), Theorem 2.1:

- **Statement.** For an ordinary E, G of order T, and |α|, |β| ≤ 1:
  U = Σ_{a∈A, b∈B} α_a β_b ψ(x(abG)) ≪ (#A)^{1−1/2ν}·(#B)^{1−1/(ν+2)}·T^{(ν+1)/(ν(ν+2))}·p^{1/(4(ν+2))}·(log p)^{1/(ν+2)}.
- **Specialization.** Set α = β = χ and A = B = Z_T^*. Multiplicativity gives U = (T−1)S exactly.
- **Result.** The exponent simplifies to |S| ≪ T^{1−1/(2(ν+2))}·p^{1/(4(ν+2))}·log^{1/(ν+2)}. With ν=1 and T ≈ p, that is q^{11/12} log^{1/3} q, which is the same q^{-1/12}.
- **Hypotheses.** Prime-order curves over F_p with q ≥ 5 have #E ≠ p+1, so they are ordinary and the lemma applies.
- **Related.** Lange–Shparlinski, Canad. J. Math. 57 (2005) studies sums over multiples z_sG of a set that is permuted under multiplication. That is the same averaging device.

**Consequence:** the card's "ceiling" should be relabelled as known, citing Ahmadi–Shparlinski 2010 and Lange–Shparlinski 2005. The record should not count it as a new structural fact. The card already says "I have not established novelty", which fits this.

## 3. Scope limits

- **The bound covers bounded-degree algebraic features only.** For arbitrary f, no unconditional bound is possible: f = χ∘log reaches |c_χ| = 1. So the question is entirely computational, and this bound says nothing about learned, table-based or non-algebraic features.
- **It does not exclude the target.** At 256 bits, 2q^{-1/12} ≈ 2^{-20}, which is above the 2^{-38} the card needs. Square-root cancellation (~q^{-1/2}) is what one would heuristically expect for algebraic f, but it is not proven.
- **The character values are elements of F_q, not complex numbers.** c^{(q−1)/m} mod q lands in μ_m(F_q). Rounding to a "nearest root of unity" first needs a fixed map μ_m(F_q) → μ_m(C), which is itself a discrete log in the order-m subgroup.
  - That costs either a table with m entries or Pohlig–Hellman at roughly √(largest prime factor of m) per evaluation.
  - It is paid on all N_t samples and in calibration.
  - The map only has to be consistent, not canonical. But for m = q^δ its memory or time is exponent-level and must go into W.
- **Two raw assertions I do not accept as proven.**
  - *"A perfect order-2 oracle is useless."* Through affine maps the oracle reduces to linear Legendre-PRF key recovery. The best attacks I found are still about √p: Beullens–Beyne–Udovenko–Vitto, and Kaluđerović–Kleinjung–Kostić (ePrint 2020/098) at O(√(p log log p)). These are algorithm upper bounds, not lower bounds.
  - *"Every method falls into three types."* The classification of subgroups of Aff(Z_q) is correct group theory: a subgroup either contains all translations or fixes a point. But it only covers exact equivariant self-reductions. It says nothing about methods outside that class.

## 4. Sources I could not check

- **Lange–Shparlinski 2005:** full text is paywalled. I saw only metadata and abstract-level descriptions.
- **Ahmadi–Shparlinski 2010:** I did not read the primary. I relied on the restatement as Lemma 2 in the 2013 arXiv paper, and checked that paper's bibliography entry.
- **Kohel–Shparlinski 2000:** primary not read.
- **Kaluđerović–Kleinjung–Kostić:** I saw only the abstract via search results.
- **Bhakta 2025 and Shparlinski–Stange:** not checked.

My search did not turn up a paper treating exactly Σχ(n)ψ(x(nG)) as a stand-alone object. That absence is not evidence of novelty, and the bound itself is covered by Ahmadi–Shparlinski as shown above.

## 5. Recommendation

1. Keep H013-MCL as speculative, with verified gain NONE.
2. Relabel the ceiling as a known corollary, with the conditions above: q ≈ p, V² ≪ p, bounded rational degree, and the ℓ¹ factor.
3. Add the cost of evaluating the complex character to W.
4. Keep the oracle-uselessness and three-types claims marked as unproven.
5. The proposed FFT grid (12 curves at 2^12–2^18) is still unauthorized, and this review does not justify it.

Sources:
- [Ahmadi–Shparlinski, Exponential Sums over Points of Elliptic Curves (arXiv 1302.4210)](https://arxiv.org/pdf/1302.4210)
- [Lange–Shparlinski, Canad. J. Math. 2005](https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/certain-exponential-sums-and-random-walks-on-elliptic-curves/060B1D110572EACEB6EC6F41EC0AB1CA)
- [Ahmadi–Shparlinski 2010 (ResearchGate record)](https://www.researchgate.net/publication/231909576_Bilinear_character_sums_and_sum-product_problems_on_elliptic_curves)
- [Kaluđerović–Kleinjung–Kostić, ePrint 2020/098](https://eprint.iacr.org/2020/098)
- [Shparlinski open problems](https://web.maths.unsw.edu.au/~igorshparlinski/CharSumProjects.pdf)
