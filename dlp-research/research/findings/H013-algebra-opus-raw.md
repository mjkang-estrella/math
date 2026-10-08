# H013 algebraic literature proposal — raw, not adopted wholesale

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h013-algebra-literature-opus-20261008-r1`.
Provider claudeAgent/claude-opus-5-5, terminal completed, no pending children.
Root flags unsupported polytope thresholds, generic runtime/transfer exclusions,
heuristic yields, and fractional MITM split arithmetic for independent review.
Unverified-source items are retained as such. No experiment was run.

# H013 independent ideation: lens "post-PKM algorithmic developments", read-only

**Result: none of these cards supports a verified or credible gain. Improvement stays NONE.**

I made no edits, ran no numerical experiments, installed nothing and launched no subagents. I didn't read any other H013 proposal. The one file I downloaded was the APS post-print, a single PDF saved to `/tmp/h013src` (outside the repo). I converted it to text with the system `pdftotext` and read it.

Before the cards, one baseline correction that matters for every card here:

**Shared-table MITM index-calculus reference.** Take B = |factor base| ≈ q^{1/m} with yield about 1 per query, and B queries. The left table of sums of ℓ factor-base points does not depend on R, so it can be built once:
- Cost is about B^ℓ + B·B^{m−ℓ}, minimised at ℓ = (m+1)/2.
- Generic index calculus therefore costs about q^{1/2+1/(2m)}, plus O(mB²) for linear algebra.
- An algebraic per-query solver still needs cost below B^{m/2−1} to win (for m = 5 that is B^{1.5}, matching the existing gate).
- But the amortised generic comparator is B^{(m−1)/2}, not B^{m/2}. A credible solver must beat it by a factor of B^{1/2}.
- APS's "single relation" variant (below) is the target-free version of this same accounting.

---

## Card 1 — LO-PKM: factor base reduced to scalar orbits through a ladder

**Operation**
- Unknown-log base: W = {w : x(w) ∈ u+μ_U}, using the PKM power-chain domain. Only U = |W| logs λ_w are unknown.
- Enlarged factor base: F = {[c]w : w ∈ W, c ∈ [0,2^n)}.
- Each query takes a labelled R = aG+bQ and solves R = Σ_{i≤m} ±[c_i]w_i.
- The system has, per point:
  - domain power-chain gates for x(w_i);
  - n x-only projective ladder steps (Brier–Joye-type differential add/double with difference x(w_i));
  - a conditional swap controlled by a bit variable with b² = b;
  - one Rabinowitsch variable so the final Z is nonzero.
- An S3 chain then combines the m ladder outputs and ends at r = x(R).

**Recovering labels and relations**
- From any algebraic solution, recompute each [c_i]w_i explicitly and check that the signed sum equals R. Raw chain solutions are never trusted.
- Each verified solution gives the row Σ ε_i c_i λ_{w_i} = a + bk.
- U+1 independent rows plus sparse linear algebra give k. Then check kG = Q.

**Expected gain: none established, and probably neutral.**
- Yield is about U^m 2^{nm} 2^m/(m! q). Setting it to about 1 fixes 2^{nm}.
- With unknowns U, total ≈ U·C_dec + mU².
- Literal baselines both lose:
  - enumerate the bits and solve W algebraically: 2^{nm}·C_PKM(U);
  - generic shared-table MITM: q^{1/2+1/(2m)}.
- Under the most optimistic factorisation, C_dec ≈ C_PKM(U)·2^{nm/2} (algebra on W, square root on the bits). The win condition becomes C_PKM(U) < U^{m/2−1}.
- That is exactly PKM's condition, τ < m/2 − 1. Orbits reduce the number of unknowns but do not relax the exponent.
- At fixed U the problem is a generic multi-base representation problem, so the best case is a constant factor. That constant still has to beat negation rho, √(πq/4), and the order-6 automorphism constant where j = 0 applies.
- The only real benefit is that the size of the algebraic domain becomes independent of q, which makes small tests easier. That is a testing convenience, not a gain.

**Costs that must be charged:** generating and certifying the domain (as in PC4), lifting points and signs, ladder gates (about 6n auxiliary variables per point), every failed or capped solve, the verification scalar multiplications, rank failures, and the U² linear-algebra memory.

**Prior art and distinction**
- Orbit-reduced factor bases are known: automorphism/Frobenius orbits (Gaudry; Faugère–Gaudry–Huot–Renault symmetries).
- SAT and Gröbner solving of decomposition systems is known (Galbraith–Gebregiyorgis 2014/806; WDSat 2019/313). Those works use binary Weil descent, not scalar-bit orbits.
- Labelled factor bases with a single relation: APS (below).
- What's distinct here is coupling unknown-log coordinate domains with known-scalar ladder orbits.

**Main unsupported assumption:** a solver whose cost is super-multiplicatively better than C_PKM(U)·2^{nm/2}. No mechanism for this was identified. MITM over the bits does not separate, because the W-algebra couples both halves.

**Cheapest decisive falsifier (on paper):** show that any split of the variables into halves forces generic list sizes (U2^n)^{m/2}. If someone wants an experiment instead, the decisive one is to measure the solver at fixed U while varying n. If cost grows by at least 2^{nm/2}, the card is dead. I did not run this.

---

## Card 2 — CSR: lattice small-root (Coppersmith-type) decomposition producer

**Operation**
- Factor base: interval x ∈ [0,B).
- Each query: R labelled; treat S_{m+1}(x_1..x_m, r) ≡ 0 (mod p) as a modular polynomial with small unknowns.
- Run the Jochemsz–May shift-polynomial lattice, LLL, then resultants or Gröbner on the integer outputs.
- Lift the small roots, check signs and the actual group sum, and record the row.
- Labels as in standard PKM. Each query costs polylog(p), but every query whose roots fall outside the box is a paid failure.

**Expected gain: none; the exponents don't fit.**
- Per-query yield is about B^m/p. Total ≈ B·p/B^m, so a win needs B^{m−1} > √p, i.e. β > 1/(2(m−1)) with B = p^β.
- The small-root regime needs a weighted product of the box sizes below p^{δ}.
- Even the optimistic linear-case benchmark (B^m < p) fits. But S_{m+1} has degree 2^{m−1} in each variable.
- My heuristic polytope estimate is β ≲ 1/(m·2^{m−1}):
  - m = 2: about 1/4 against the 1/2 needed;
  - m = 3: about 1/12 against 1/4;
  - larger m is worse.
- For m = 2, the required B ≥ √p puts about one or more roots in the box, which is outside any known Coppersmith regime.
- Linearising S3 in (e₁, e₂) gives about B^{12} < p, which is worse still.
- S3-chain auxiliary variables are full-size, so the chain encoding doesn't help.

**Prior art:** Jochemsz–May (Asiacrypt 2006); Feng–Nitaj–Pan 2024/1330 (the bound equals a Newton-polytope volume). My search found no source applying these to summation polynomials. That is a missing-source report, not a novelty claim.

**Main unsupported assumption:** δ_m > m/(2(m−1)) for the actual S_{m+1} polytope.

**Cheapest decisive falsifier:** compute the exact Jochemsz–May / Feng–Nitaj–Pan polytope bound for S3 and S4. This is a paper calculation. I estimated it but did not compute it from the source.

---

## Card 3 — GLUE: transfer into a genus-2 or genus-3 Jacobian through computable gluing isogenies

**Operation**
- Odd q means E has no rational 2-torsion, so its cubic is irreducible.
- Choose E′ whose 2-torsion is Galois-isomorphic to E's. On E[2] every isomorphism is an isometry; exclude the ones induced by isomorphisms of curves.
- Glue E×E′ into J(C) for a genus-2 curve C over F_p (Howe–Leprévost–Poonen / Kani). Then Φ(P,0) can be computed in O(1) field operations.
- Solve the DLP for Φ(G,0), Φ(Q,0), which lies in a subgroup of order q of J(C)(F_p), whose order is q·#E′.
- Pulling back through the dual isogeny gives labels. Verify kG = Q.

**Expected gain: none.**
- Index calculus on a genus-g curve over F_p costs Õ(p^{2−2/g}) with double large primes: Õ(p) for g = 2 and Õ(p^{4/3}) for g = 3.
- Diem's algorithm for plane quartics is Õ(p).
- All of these are at least p, far above √q.
- For growing g, L_{p^g}(1/2) is superpolynomial in p.
- No known Jacobian index calculus exploits the fact that the target lies in an elliptic factor.

**Prior art:** Kani, HLP, Frey–Rück-style transfer. The distinction is only that 2022+ algorithms make the gluing efficient. The gluing is not the bottleneck.

**Main unsupported assumption:** genus-g index calculus that is sensitive to a split-Jacobian target subgroup.

**Cheapest decisive falsifier:** substitute the exponents above. This already decides it, so the card is rejected on paper.

---

## Bridges screened out (not carded, with reasons)

- **Bi–Cheng–Rojas sparse root detection.** Cost is q^{(t−2)/(t−1)} for t-nomials. Every relation encoding has t ≥ 3, so the cost is at least √(domain). Folding the grid by CRT just reproduces the B₁×B₂ grid (same territory as H009/H010). They also prove NP-hardness when t grows.
- **√élu / Bostan–Gaudry–Schost box products.** These give an exact membership or decomposition predicate in Õ(H^{m/2}). That equals MITM and loses polylog factors to BSGS.
- **Modular composition and fast bivariate resultants.** Any method that materialises the degree-B^{⌈m/2⌉} elimination polynomial already pays the MITM output size.
- **Isogeny-transported factor bases.** φ is a bijection on rational points with a computable inverse ([ℓ⁻¹]φ̂), so these are equivalent instances with no shared unknowns.
- **Smooth-norm endomorphism chains.** These do evaluate non-scalar endomorphisms in polylog time, which contradicts the rejected "degree means cost" claim. But on E(F_p), π acts as 1, so their eigenvalues are known scalars. Canonicalising a large orbit costs d per step, as in H002 A3.
- **Factor bases from twist subgroups (smooth #E^t).** Those x-values belong to twist points, so relations force the twist part to be zero.
- **Cheon-type use of q−1 structure.** Needs the auxiliary input k^dG, which is disallowed advice.
- **Higher-dimensional interpolation.** Already covered in H004.

## Sources

**Inspected:**
- [Amadori–Pintore–Sala post-print](https://iris.unitn.it/handle/11572/202653) (ePrint 2017/609 returned 403). Mechanism checked: randomly labelled factor base, one relation from S_m on unstructured V, total qm^m T/s^m. They write that they "do not claim" a gain under r^{1/2} and leave T unestimated.
- [Bi–Cheng–Rojas, arXiv 1204.1113](https://arxiv.org/abs/1204.1113): abstract-level only.
- [Galbraith–Gebregiyorgis 2014/806](https://eprint.iacr.org/2014/806) and [WDSat 2019/313](https://eprint.iacr.org/2019/313): abstract-level only.
- [Gaudry–Thomé–Thériault–Diem 2004/153](https://eprint.iacr.org/2004/153) and [Diem slides](https://cr.yp.to/conferences/2005-ecc/www.cacr.math.uwaterloo.ca/conferences/2005/ecc2005/diem.pdf). The genus-3 exponent 4/3 is confirmed. The general formula 2−2/g has **not** been verified against the paper.
- [Jochemsz–May](https://www.iacr.org/archive/asiacrypt2006/42840270/42840270.pdf) and [Feng–Nitaj–Pan 2024/1330](https://eprint.iacr.org/2024/1330): metadata only. Their exact theorems were not read.

**Missing or recalled but unverified:** Kani 1997 and Howe–Leprévost–Poonen gluing statements; Diem's plane-curve exponent; Enge–Gaudry L(1/2); the Bostan–Gaudry–Schost and √élu complexity statements; the Semaev 2015/310 full text.

## Five-item wave report

1. **Best supported work:** unchanged, the classical square-root reference with negation/automorphism constants. Generic shared-table index calculus is q^{1/2+1/(2m)}.
2. **Verified improvement:** NONE.
3. **Hypothesis from this lens:** LO-PKM (Card 1). It is neutral under the most optimistic factorisation.
4. **Evidence:** CSR and GLUE are rejected by exponent arithmetic. LO-PKM is reduced to PKM's τ < m/2 − 1 condition. I ran no tests.
5. **Next decisive step:** compute the exact S3/S4 polytope bound for CSR, and look for a bit-separation argument for LO-PKM (or show none exists). Neither needs an engine.
