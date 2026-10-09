# H036 independent Factory Fable proposals

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h035-independent-information-fable-20261008-r1`

Completed with no pending children. Raw testimony retained; root qualifications
are separate. Unverified source memories, cost estimates and provider usage
figures are not accepted as calibrated research evidence.

# H036 candidate pool: independent coordinate/algebraic ideation (read-only)

**Role and scope.** Independent initial proposer, Factory `claude-fable-5.1`. Read RESEARCH_LOOP.md, RESEARCH_TEAM.md, STATE.md (first ~860 lines, the live H033–H035 sections), and the H013–H033 dispositions bearing on coordinate/algebraic mechanisms (H013 coordinate/algebra/group-action/MCL, H017 information/anchor, H019 x-only baseline, single-query resultant, information, H020 structured, H021 representation, H022 final scopes, H023 fixed-difference walk, H024 algebraic raw, H026 algebraic scope, H027 Legendre backend and polarized quotient, H029 arithmetic, H030 automorphism), plus keyword sweeps across all findings. **H035 findings were not opened.** No code, imports, edits, children, experiments. **No external source was fetched this session**; every outside citation below is either (a) a primary read already recorded by root/reviewers in the named finding, or (b) explicitly marked *memory*. Verified improvement remains **NONE**; the ordinary square-root reference is unchanged by anything here.

## 0. Why the lens is nearly saturated: five exact closures the record already implies

Stating these once avoids re-proposing dead variants. Each is elementary and I checked it; none is a universal impossibility theorem for ECDLP, only for the named operator class.

1. **Homomorphic images.** Z/q has no nontrivial homomorphism into any group of exponent coprime to q. Every "k mod ℓ", descent map, Tate/Weil pairing with ℓ-torsion, Kummer map, or F_p-valued additive projection is trivial for ℓ ≠ q; an exact character of k valued in a field needs μ_q ⊂ F_{p^r}, r = ord_q(p) (MOV barrier; H024 "targets with order divisible by q"). A Lang-isogeny eigenfunction h with h(P+G) = ζh(P) is exactly this: h^q descends along 1−π, so h lives over F_{p^r}.
2. **Label tracking.** Any non-group map on F_p (x ↦ x+1 across E and its twist, power maps, digit maps) destroys the (a,b) label chain. Such maps can only serve as *features* feeding a decoder, never as walk steps. So the walk side is confined to group operations, where the arithmetic ledgers of H019/H023/H027/H035 apply.
3. **Bounded-degree, bounded-L1 features are closed** by Kohel–Shparlinski (root/Sol-read in H026) with the homomorphic-transport lemma (dilations/isogenies don't raise the effective degree). Escapes are only (i) large-L1 predicates, (ii) non-group maps, (iii) multiplicative scalar characters, where the recorded ceiling is q^{-1/12} (Ahmadi–Shparlinski, root-read in H013).
4. **Interval products tie √.** Single-query ∏_{n∈I}(x_Q − x(nG)) costs Õ(√|I|) (H019 resultant) and BGS-type matrix factorials also tie √N (H005, H020, H026-product-recurrence). New exact remark below (Card 2) shows the structural hypothesis that could feed BGS is impossible globally.
5. **No cheap non-trivial endomorphism on generic ordinary curves.** If End(E) = O has discriminant D, every ψ ∈ O∖Z has deg ψ = N(ψ) ≥ |D|/4 (minimise a² + ab·tr + b²N over a with b ≠ 0). For random curves |D| ≈ |t²−4p| ≈ 4p up to a small square conductor, so deg ψ ≳ p. This makes H014's "a cheap endomorphism acting as λ would reopen it" exact: only small-|D| (special/GLV) curves have one. Card 3 pushes on the one loophole (smooth-degree ψ via class-group relations).

---

## Card 1 — Height-bounded (Farey) factor base for summation-polynomial decomposition

**Operator (public input only).** F_H = {P ∈ E(F_p) : x(P) ≡ N/D (mod p), gcd(N,D)=1, |N|,|D| ≤ H}. Membership test: half-extended Euclid (rational reconstruction) on x, O(log p) word ops. |F_H| ≈ (12/π²)H²·½ ≈ 0.61 H² (coprime pairs, half with f(x) square; distinct mod p when 2H² < p). Decompose R = Q + rG as P₁+P₂ (m=2) or P₁+P₂+P₃ (m=3) by clearing denominators in S₃/S₄: x_i = N_i/D_i gives a polynomial bihomogeneous of degree 2 in each (N_i, D_i) pair, with 2m unknowns each ≤ H = B^{1/2}, B := |F_H|. Linear algebra on B unknowns as in PKM.

**Hoped source of gain.** Same cost skeleton as PKM: P + m!·p/B^{m−1}·T + B^ω (PKM §3.3, root-read, H003/H012 records), beating √p iff a decomposition costs T < p^{1/2−1/m}. The hope was that the height set, unlike an interval, is closed under x ↦ −x and x ↦ 1/x and is a *box in (N,D)-space*, which might give a better-shaped small-root lattice than Semaev's affine interval.

**Applicability.** Any ordinary prime-order curve, any p. Not a special-curve hypothesis.

**Prior-art distinction.** Semaev 2004 (interval base), PKM 2016 (interval and multiplicative-subgroup bases; root-read), APS 2017, CSR/Coppersmith screens in H012/H013 (Jochemsz–May §2 Sol-read), H026 C1 character bases. A height-bounded base does not appear in the record or, to my memory, in the literature (memory; not checked).

**Unsupported assumption.** That the bihomogeneous lattice gives a strictly better sufficient condition than the affine one at equal volume.

**Complete accounting.** Setup: none beyond Euclid per candidate. Memory: B points plus relation matrix. Per attempt: one Euclid per factor-base candidate x, one small-root call per target, verification kG = Q. Failed attempts: expected m!·p/B^{m−1} per useful relation, as PKM.

**Why reject (paper, checked).** The box volume is identical: ∏ bounds = H^{2m} = B^m, exactly the interval base's B^m. At the first Coppersmith/Howgrave-Graham level for m=2 the monomial-weight products also coincide (affine x₁^i x₂^j, i,j ≤ 2: Σ(i+j) = 18 → B^18; bihomogeneous: 9 monomials × H⁴ = B^18). Homogenising adds a projective scaling freedom but no determinant advantage; the symmetries x ↦ −x, 1/x are not symmetries of S₃. So the small-root threshold is the same as the interval base and the PKM threshold T < p^{1/2−1/m} stays unmet (naive bivariate heuristics need roughly B² < p^{1/4}, i.e. B ≲ p^{1/8} ≪ p^{1/2}). Membership is also slightly dearer (Euclid vs. comparison).

**Cheapest decisive falsifier.** None needed; the equal-determinant computation above is the falsifier. If someone disputes it, a paper lattice-determinant comparison at one more shift level (no run) settles it.

---

## Card 2 — "Elliptic Pochhammer" interval membership via P-recursive (holonomic) structure

**Operator.** Single query D_I(α) = ∏_{n∈I}(α − x(nG)) at α = x(Q); zero iff k ∈ ±I; bisect I. If n ↦ x(nG) satisfied a recurrence Σ_{i≤r} c_i(n) W_{n+i} = 0 with c_i ∈ F_p[n] of degree d, the product sequence could be fed to a Bostan–Gaudry–Schost matrix-factorial evaluator.

**Hoped source of gain.** Sub-√|I| membership per level would give sub-√q total by bisection. (Over C, ∏ σ(w+nz) is a ratio of elliptic gamma functions, memory; the finite-field analogue is what the record calls the "elliptic factorial".)

**Applicability.** Any curve.

**Prior-art distinction.** H019 resultant evaluator (Õ(√|I|), Bernstein–De Feo–Leroux–Smith root/Astra-read), H002 card 4, H020 card 2 (BGS lands at √q), H024 "needs a factorial-type advance". New here: an exact statement about the *hypothesis itself*.

**Why reject (new exact argument plus known tie).**
- *Global exclusion.* Suppose the recurrence holds for all n ∈ Z with deg c_i < p. Fix m mod q. As n ranges over n ≡ m (mod q), W_{n+i} = W_{m+i} is constant while n mod p ranges over all of F_p (gcd(p,q)=1). Hence the polynomial Σ_i W_{m+i} c_i(X) vanishes on F_p, so it is zero; reading off each coefficient degree j gives a *constant-coefficient* recurrence Σ_i c_{i,j} W_{m+i} = 0 for all m. By H017's lemma (minimal polynomial divides X^q − 1; nonconstant part has degree ≥ ord_q(p)), r ≥ ord_q(p). So no useful global P-recursive structure exists; coefficient degree below p buys nothing.
- *Local (interval) version is tautological or useless.* On [0,L) with L < p, a recurrence with (r+1)(d+1) > L coefficients always exists by interpolation; a nontrivial one needs (r+1)(d+1) ≪ L, and even then BGS costs Õ(r^ω √(Ld)) ≥ √L per level, so the exponent is unchanged (consistent with H005/H020).
- The polynomial special case is the classical "n! mod p faster than √n" barrier (Strassen; Shub–Smale context, memory), so progress here would be a result about factorials, not about curves.

**Cheapest falsifier.** None needed. Optional (not admitted, not recommended): on a q ≈ 2^{12} curve, rank-test the (r,d) ≤ (8,8) interval recurrence system on 2(r+1)(d+1) terms; expected full rank. It cannot change the exponent even if it failed.

---

## Card 3 — Smooth-degree endomorphisms from class-group relations as cheap large-order multipliers

**Operator.** Compute O = End(E) and its class group relations among small split primes l_i (paid, subexponential L_{|D|}(1/2), Hafner–McCurley / Bisson–Sutherland style, memory). A relation ∏ l_i^{e_i} = (ψ) yields ψ ∈ O with N(ψ) = ∏ ℓ_i^{e_i}, evaluable as a chain of Σ|e_i| rational ℓ_i-isogenies (Vélu O(ℓ), or sqrt-Vélu Õ(√ℓ); BDLS, root-read in H019 for the resultant lemmas only, cost tables from memory). ψ acts on E(F_p) as a public scalar λ_ψ of generically large multiplicative order. Use ψ as a step in a multiplicative walk, or as the coset step in the H013 MCL coset-BSGS backend, replacing a generic [λ]P (≈ log q doublings + ½ log q additions ≈ 2600M at 256 bits with 5M+S/6M units).

**Hoped source of gain.** A multiplier of large order costing less than one generic scalar multiplication; this is precisely the loophole H014 flagged. Does not fold the group (only units fold), so no exponent change is claimed; the gain would be a constant in backends that need many large multipliers.

**Applicability.** Ordinary curves with computable End(E); needs factoring t²−4p (paid, usually feasible at 256 bits).

**Prior-art distinction.** GLV/GLS use *small-|D|* endomorphisms (special curves). Isogeny-volcano walks (H005) move between curves; here the cycle returns to E. Class-group relation methods compute End(E) (Bisson–Sutherland, memory) but, to my knowledge, are not used to manufacture multipliers for DLP backends.

**Unsupported assumption.** That a relation with small Σ|e_i| and small ℓ_i exists and that Σ_i |e_i|·C(ℓ_i) < cost of [λ]P.

**Complete accounting and why reject.** By closure 5, N(ψ) ≥ |D|/4 ≈ p, so Σ|e_i| log ℓ_i ≥ log p − 2 ≈ 254 bits. Cost ≈ Σ|e_i|·C(ℓ_i) with C(ℓ) ≥ ~ℓ (Vélu) or ≳ √ℓ·polylog (sqrt-Vélu). Two regimes:
- *Tiny ℓ (3-smooth):* ≈ 160 degree-3 steps × ~(6M+S) ≈ 1100M, which *would* beat 2600M by ~2×. But N(ψ) = 3^t needs ord([l₃]) | t ≤ ~170 in a class group of size h ≈ √|D| ≈ 2^{128}; probability negligible for a random curve. Not available.
- *Smooth with ℓ_max ≈ 2^{12}:* heuristically ~560 split primes give relations with entries in {0,±1} and ~23 nonzero entries. Cost ≈ 23 × C(2^{12}); even at an optimistic sqrt-Vélu C ≈ 10³ M that is ≳ 2·10⁴ M, ≥ 8× worse than generic [λ]P.
Interpolating between regimes does not cross below the generic cost because the relation-lattice heuristic (entries ~h^{1/s}) forces total degree ≳ p while small ℓ_i require long chains. Plus the multiplier-walk premise itself is unsupported (H027 walk review: squaring/tripling-heavy walks mix worse; H030 missing trajectory law). Preprocessing L_{|D|}(1/2) is affordable relative to √q but buys a slower step. Memory: O(s) ideal classes plus kernel polynomials of the chain.

**Cheapest decisive falsifier.** Paper only: exhibit any ordinary prime-order curve family with a relation satisfying Σ|e_i|·C(ℓ_i) < 2600M under the recorded units; by the norm bound this requires ord([l_i]) small for tiny ℓ_i, i.e., a *small class group*, i.e., small |D| — a special curve. No run.

---

## Seeds considered and deduplicated (not re-proposed)

| Seed | Disposition |
|---|---|
| Pure multiplicative Kummer-line walk (x-only, {2,3} multipliers, no fruitless cycles, no jump table) | Arithmetic already fatal: x-only doubling 2M+2S+I (H023), tripling ≈22M+4S batched (H027) vs 5M+S; mixed/doubling walks are H027 Card 1 (Teske-type, not new). |
| Multiplicative BSGS k = ±m/n, lists x(nQ), x(mG) | Ratio-set density 6/π² makes it ~40% worse than signed BSGS; baseline variant. |
| F_{p²} trace / twist-mixed factor bases; (E,E′,E′) S₃ triples | H020 card 4, H021 trace card, H012 twist argument. |
| Power-residue / Legendre features of EDS, φ, y-sign | H003, H022, H024 Card A; collapse to ψ_ℓ characters. |
| Interval indicator (elliptic-log sign) via sparse coordinate Fourier | Flat spectrum by Kohel–Shparlinski (H026); only the small-circuit hypothesis (H019 C2) remains. |
| Linear complexity over F_q of x̃(nG) mod q | Equivalent to low-degree polynomial agreement, H017 card 2. |
| Cross-ratio / two-view predicates | Low-degree single view after substitution; KS-closed. |
| p-adic / Z/p² lifts, dual numbers | Hom(Z/q, Z/p) = 0; H026 C5, H002 lift review. |
| Isogeny-pushed factor bases F_φ, "isogeny smoothing" | Degree only rises; decomposition probability unchanged. |
| Horizontal-isogeny class walks, MOV, GHS/genus-2 covers, polarized surfaces, ray class | H005, H013 GLUE, H021, H026 C2, H027. |

## Sources and access

No fetches this session. Record-read primaries relied on: PKM §3.3 (root), Jochemsz–May §2 (Sol), Kohel–Shparlinski Thm 1 (Sol/Fable), Ahmadi–Shparlinski Lemma 2 (root), BDLS Lemmas 4.3/4.9/Thm 4.11 (root/Astra), Bernstein–Lange–Schwabe negation ledger (Grok). Memory-only and flagged: elliptic gamma/Pochhammer closed form; Strassen/Shub–Smale factorial barrier; Bisson–Sutherland and Hafner–McCurley; BDLS sqrt-Vélu concrete cost tables; Teske's mixed-walk constants; GLV/GLS. If root wants any of these promoted, the cheapest check is BDLS Table costs for ℓ ≈ 2^{12}; it cannot rescue Card 3 but would tighten its constant.

## Recommendation

No card has a credible full-work or exponent premise; **no experiment, implementation, or Lean work is justified** by this wave. The contributions worth retaining as negative evidence are the three exact remarks: (i) the equal-determinant equivalence of height-bounded and interval factor bases; (ii) global impossibility of P-recursive structure for n ↦ x(nG) (CRT reduction to H017's constant-coefficient bound), tightening H024's "factorial-type advance" note; (iii) the norm bound deg ψ ≥ |D|/4 with the smooth-relation cost analysis, making H014's endomorphism loophole explicit and closing it for generic ordinary curves. The coordinate/algebraic lens appears saturated at the operator level; remaining openings in the record (multiplicative-character window 1/12 < β < 1/4; small-circuit interval predicates) are analytic or complexity-theoretic, not new executable operators.

---
*Factory usage — local bridge. This turn: 1,399,544 tokens · ≈2,535,674 Factory credits. Saved session total: 1,399,544 tokens · ≈2,535,674 Factory credits (including recorded subagents). Credits are a local estimate, not a dollar charge.*
