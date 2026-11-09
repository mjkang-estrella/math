# Selected candidate notes (fresh-corpus-r3)

The primary candidate, 324342, has its own dossier in `conference/PROOF.md`. Below are the other targets that got primary-body reading and concrete proof or counterexample attempts.

## 323834 / 323832: Broadhurst third-category conjectures (Elder, arXiv:1207.5811v1)

**Primary statements (§8.5, p. 32).**

- **Conjecture 3 (cyclotomic; MathDB 323832).** Let p < q < r be odd primes with A(pqr) = 1, and let w be least with r ≡ ±w (mod pq). Suppose p ≢ 1 (mod w). Then w > p, q > p² − p, q ≡ ±1 (mod p) and w ≡ ±1 (mod p). Moreover, if w ≡ 1 (mod p) then q ≢ ±1 (mod wp).
- **Conjecture 5 (pseudocyclotomic; MathDB 323834).** The same, for "relatively prime positive integers" p < q < r with Φ̃_{p,q,r} flat. The "Moreover" clause is weakened to q ≢ 1 (mod wp).
- **Author's remark.** The Φ̃_{p,q,r} "have not" been computed, so "there could still be a small counterexample … such a counterexample would be very informative."

**Exact search.** Script: `pseudocyclotomic/pseudo.py`.

- Φ̃_{p,q,r} is computed exactly by the product formula (12): four multiplications by (1 − x^e) and four exact power-series divisions by (1 − x^e).
- It matches sympy's Φ_n for n = 105, 609, 3·11·41 and 5·7·11, and reproduces the source's A(3·7·29) = 2 and the flatness of (3,11,41) and (5,29,499).
- By Elder §6.4 periodicity (pseudocyclotomic analogue of Kaplan), the height depends only on ±r mod pq for r > q. So one r per class w covers every r.

**Results.**

| Range searched | Violations | Log |
|---|---|---|
| Odd p ≤ 15, all coprime q ≤ 60, every class w | 0 | `search_odd_p15_q60.log` |
| Odd p ≤ 7, q ≤ 150 | 0 | `search_odd_p7_q150.log` |
| Even p ∈ {4,…,12}, q ≤ 50 | 0 | `search_even4_p12_q50.log` |

Prime triples are included through periodicity. So neither conjecture fails in these ranges for p ≥ 3. **Status: parked.** No structural route to a proof was found. The flatness classification is a long-open problem; Conjecture 1 in the same section is unresolved.

**Degenerate literal refutation of Conjecture 5 at p = 2 (ordinary proof; not formalized).**

*Identity.* By formula (11) and order-independence, for odd coprime q < r:

  Φ̃_{2,q,r}(x) = Φ̃_{q,r}(x²)/Φ̃_{q,r}(x) = (x^{qr}+1)(x+1)/((x^q+1)(x^r+1)) = Φ̃_{q,r}(−x).

The sign changes cancel because qr, q, r and 1 are all odd. Binary Φ̃_{q,r} is flat for coprime q, r (the Lam–Leung argument does not use primality). So every Φ̃_{2,q,r} is flat.

*Applying the conjecture at p = 2.*

- w is odd, since it is coprime to 2q. So "p ≢ 1 (mod w)" ⇔ w ∤ 1 ⇔ w ≥ 3.
- The conclusions w > 2, q > 2, q odd and w odd then all hold automatically.
- w ≡ 1 (mod 2) always, so the "Moreover" clause demands q ≢ 1 (mod 2w).

*Conclusion.* Conjecture 5 holds at p = 2 exactly when q ≢ 1 (mod 2w), and fails for the infinite family q ≡ 1 (mod 2w). The smallest example is (p,q,r) = (2,7,17) with w = 3; the code confirmed flatness numerically.

*Credit assessment.* This is literally inside the stated domain ("relatively prime positive integers"). But it is the even/degenerate edge of a generalization of an odd-prime conjecture, and it reduces to the trivial identity above. I classify it as a domain-edge refutation with likely **zero credit** under the campaign standard.

*Lean.* Not built. Doing so would need a list-based polynomial checker for the degree-96 identity Φ̃·den = num plus a flatness bridge. That is feasible, but was not prioritized given the credit assessment.

## 324570: Arratia–DeSalvo pair-sampling discrepancy

**Sources read.** arXiv:1211.6486 v1 and v2, and the published Adv. Appl. Probab. 47 (2015) 292–305 (Cambridge PDF).

**Primary statement.** ℓ₀ := sup_p D(p) over all discrete p, where D(p) = d_TV(M1(p), M2(p)). Conjecture 1 asks for ℓ₀ < 1, and it remains a conjecture in the 2015 published version. OpenAlex reports 0 citing works.

**Theorem (ordinary, new as far as checked).** For every distribution p on a finite or countable set,

  D(p) ≤ 1 − c₀,   c₀ = ∫₀^∞ u e^{−u−u²/2} du = 1 − √(2π) e^{1/2} Φ̄(1) = 0.34432…

Hence ℓ₀ ≤ 0.65568 < 1.

**Proof.**

1. Let f₂ = Σ p_j². Then P(X=i) = p_i²/f₂.
2. By (3) of the source, P(Y=i) = p_i² Σ_k (k+1)! e_k(p_{−i}), where e_k is the k-th elementary symmetric sum of the other colors' probabilities.
3. Since ∫₀^∞ t^{k+1} e^{−t} dt = (k+1)!, Tonelli's theorem gives Σ_k (k+1)! e_k(p_{−i}) = ∫₀^∞ t e^{−t} ∏_{j≠i}(1 + p_j t) dt. The product converges because Σ p_j < ∞.
4. Since Σ_j p_j = 1, we have e^{−t} = e^{−p_i t} ∏_{j≠i} e^{−p_j t}.
5. For x ≥ 0, log(1+x) − x ≥ −x²/2. Hence ∏_{j≠i}(1 + p_j t) e^{−p_j t} ≥ e^{−t² f₂/2}.
6. Combining 3–5: P(Y=i) ≥ p_i² ∫₀^∞ t e^{−p_i t − f₂ t²/2} dt.
7. Substitute t = u/√f₂ and use p_i ≤ √f₂, which holds because p_i² ≤ f₂. This gives P(Y=i) ≥ (p_i²/f₂) ∫₀^∞ u e^{−u−u²/2} du = c₀ P(X=i).
8. Therefore Σ_i min(P(X=i), P(Y=i)) ≥ c₀, and D(p) = 1 − Σ_i min(·,·) ≤ 1 − c₀. ∎

**Scope versus the MathDB literal.**

- The MathDB record asserts that "the global maximum exists, equals the supremum of the finite-support maxima, and is strictly less than 1".
- The source has no C_n, C_∞ or C notation, and no attainment claim. MathDB's "max over P_{Z+}" paraphrases ℓ₀ = sup.
- The source expects ℓ₀ = sup_c ℓ(c) ≈ 0.1832, approached only as the support size n → ∞ by spreading distributions. Attainment by a countable distribution is therefore doubtful, and neither proved nor disproved here.
- The "C_∞ = C" part is soft. Continuity of D under ℓ¹ approximation is sketched in source §8 and is not written out here.

**Status: partial, no credit.** It proves the source's Conjecture 1 (strict bound below 1), not the literal attainment and equality. No Lean.

## 324701: Hartke–Liu–Petříčková Conjecture 1.1 (fractional powers)

**Primary statement (arXiv:1212.3898v1).** Iradmusa's Conjecture 1 says: for connected G with Δ(G) ≥ 3 and 1 < m < n, χ(G^{m/n}) = ω(G^{m/n}). Conjecture 1.1 says this holds except when G = C₃□K₂. The source proves the case m even (Theorem 1), and the counterexample C₃□K₂ with m = 3, n = 5 (Proposition 5.2).

**Exact search.** Script: `fracpower/fracpow.py`.

- G^{m/n} is the m-th power of the n-subdivision.
- The clique number is computed exactly with networkx.
- ω-colourability is decided by CaDiCaL 2.1.2 (the Lean toolchain binary) on a direct CNF encoding, with a maximum clique pre-coloured to break symmetry.

**Results (m = 3).** Two ranges were searched:

- All 1,253 atlas graphs (≤ 7 vertices) that are connected with Δ ≥ 3, for n = 4..7.
- All 5 connected cubic graphs on 8 vertices and all 19 on 10 vertices, for n = 4..7.

The only failure found is the prism C₃□K₂ at n = 5, reproducing the source.

**Results (m = 5).** The run on the atlas graphs, n = 6..11, is reported in `fracpower/` (see SUMMARY.md).

**Status: parked.** No second exceptional graph was found. The universal positive direction for odd m is beyond reach here.
