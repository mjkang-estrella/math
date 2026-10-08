# H027 algebraic construction proposals (raw)

Status: RAW proposals under separate review, not accepted universal barriers. Root flags the unmarked-surface torsor/uniqueness claims, baseline k=1 action normalization, generic embedding-degree estimate, and free-oracle backend conclusion. Source access was abstracts only; memory statements remain unverified. No downgrade of earlier hypotheses or numerical test authorized from this report.

Provider: claudeAgent; model: claude-opus-5-5.
TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h027-algebraic-constructions-opus-20261008-r1
Completed and read 2026-10-08.

# H027 proposals from the target-dependent invariants lens: two constructions, both ending at the square-root bound

I found no construction that beats square root. Best supported complexity is still the generic square-root work with the known automorphism constants, and verified complete-work gain is NONE.

I worked read-only: no edits, experiments, probe imports, children or commits. I did not read the other H027 proposals. Of `hypotheses/H027-constructive-candidates.md` I saw only a keyword grep (role briefs and one native trace-dual line), so I could avoid duplicating that role.

**What I read**
- **Workspace:** `RESEARCH_LOOP.md`, `RESEARCH_TEAM.md`, the head of `STATE.md`, and a keyword skim of the rest.
- **Findings:**
  - H026: algebraic scope reconciliation, information–algebraic scope, and the algebraic Opus raw report.
  - H025: bridge scope corrections.
  - H024: algebraic mechanisms raw report.
  - H002: marked-surface disposition, and the raw review grepped for its polarization points.
  - Keyword sweeps across all findings for Kani, gluing, Prym, Kummer, elliptic nets, Xedni, canonical lift, Coppersmith, Cheon and a few dozen other terms.
- **External, read this session (abstracts only):**
  - Castryck–Sotáková–Vercauteren, ePrint 2020/151. The PDF returned 403, so its theorem hypotheses below are **from memory**.
  - Beullens–Beyne–Udovenko–Vitto, ePrint 2019/1357.

---

## Card A: a principally polarized surface attached to the target, A_Q (construction, ends at a √q problem)

This adds something to H002 V1 and H026 C2. Those records treat the cyclic quotient E²/⟨(G,Q)⟩, which is (1,q)-polarized. Here is a principally polarized version that depends only on Q and is defined over F_p.

**Construction (paper; needs independent review)**

1. **Setting.** q = #E(F_p) is prime and q ≈ p, so q ∤ p−1. Frobenius acts on E[q] with eigenvalues 1 and p, which are distinct mod q. Let ⟨G⟩ be the 1-eigenline, which is ker(π−1). Let ⟨H⟩ be the p-eigenline, which is ker(π̂−1). H lives in F_{p^r} with r = ord_q(p), generically about q.
2. **The kernel.** Define K_Q = ⟨(G,Q)⟩ ⊕ {T ∈ ⟨H⟩² : e_q(G,T₁)·e_q(Q,T₂) = 1}. Writing Q = kG, the second part is ⟨(−kH, H)⟩.
   - K_Q is π-stable, so it is an F_p-rational subgroup scheme.
   - It has order q² and is maximal isotropic for the product Weil pairing.
   - It is defined from Q **by pairings alone**; k is not needed.
3. **The surface.** A_Q := E²/K_Q is a principally polarized abelian surface over F_p.
   - Its symmetries are k ↦ −k (via (P,R)↦(P,−R)) and k ↦ 1/k (via the swap), which matches C2's {±k^{±1}}.
   - The K_Q construction itself is new relative to the records.
4. **Small isogenies move k by a Möbius map.** Take γ = [[a,−b],[b,a]] ∈ M₂(ℤ) with a²+b² = ℓ.
   - γ acts on the G-plane and the H-plane by the same matrix mod q, so γ(K_k) = K_{γ·k}, where γ·k = (ak+b)/(a−bk).
   - Hence A_{γ·k} ≅ A_k / Φ_k(ker γ) is an (ℓ,ℓ)-neighbour of A_k.
   - In the coordinate 1+ki ∈ F_q[i]^*/F_q^*, γ acts by multiplication. So {A_k} is a torsor under the cyclic torus T of order q∓1 (the sign depends on whether −1 is a square mod q), with fixed points k = ±i.
5. **The cheap invariants carry no information about k.** As O_K-varieties, A_k ≅ E ⊗ M_k. The Steinitz class is det M_k = (𝔮₁𝔮₂)⁻¹ = (q)⁻¹, which is principal. The local determinant at q is q⁻¹·unit, independent of k. So the unpolarized class, the Steinitz class and the abelian (determinant/spinor-type) genus invariants are all constant in k. The information sits only in the non-abelian Hermitian class.

**Public-Q operations and recovery**
- Compute A_Q, compute A_G (that is, k=1), then find t ∈ T with t·A_G = A_Q by walking (ℓ,ℓ)-isogenies.
- Read k from t = [1+ki]. Verify kG = Q.

**Why there seemed to be a gain.** The construction converts an F_p object into F_q-projective structure. Characters of T are genuinely arithmetic mod q, which no low-degree F_p function provides.

**Applicability.** Every ordinary prime-field curve of prime order q ≠ p, over the full range.

**Baseline versus predicted complete work.** The baseline is ≈0.886√q group operations (rho with negation). Predicted gain: NONE.
- Inverting the T-action is a group-action inversion problem on a cyclic group of size ≈q. Rho or meet-in-the-middle costs ≈√q, and each step is a genus-2 (ℓ,ℓ)-isogeny, which is far dearer than a curve addition.
- Computing A_Q is a (q,q)-isogeny whose kernel's H-part is defined over F_{p^r} with r ≈ q. I know of no method below about √q for it, even for the rational cyclic part (√élu analogue; from memory).

**Costs.**
- **Setup and memory:** the same as one √q-scale isogeny computation plus a rho over T.
- **Failure modes:** degenerate k = 0, ∞ or ±i, and the fact that only a finite set of k gives A_k ≅ E².
- **Advice:** none.

**Prior art.**
- Kani/Robert principal-polarization conventions, through the H026 records (Astra read Robert). Kani's (ℓ,ℓ) lemma and the Hermitian-lattice description of surfaces isogenous to E² are **from memory**.
- The CSIDH/GAIP √ bound is **from memory**.

**Unsupported premise.** A cheap invariant of A_Q that is *not* T-equivariant, together with a sub-√q way to compute A_Q. Neither is supplied.

**Cheapest decisive falsifier.** A paper check by a reviewer of the three lemmas: π-stability and isotropy of K_Q, γK_k = K_{γk}, and constancy of the determinant/Steinitz class.
- If all three hold, inversion is a group-action inversion problem on a cyclic group of size ≈q.
- That kills any gain unless someone supplies a non-equivariant invariant.
- A toy numeric check is possible only on small-embedding-degree curves, and those would verify the algebra, not any gain. I do not recommend it.

---

## Card B: a torus genus character χ_q(1+k²) feeding a Legendre-PRF backend (high risk; fails even if the character were free)

**The object.** The quadratic character of T, evaluated on the element relating A_G and A_Q, equals χ_q(1+k²). I checked both cases: q ≡ 1 mod 4, where the norm of 1+kι is (1+kι)(1−kι), and q ≡ 3 mod 4, where T = F_{q²}^*/F_q^*. It is invariant under ±k^{±1}, so it is a well-defined genus-type invariant of A_Q.

**Self-reduction (exact, case q ≡ 1 mod 4).** Querying the target cQ + aG gives χ(1+(ck+a)²) = χ(k+x)·χ(k+y), where x = (a−ι)/c and y = (a+ι)/c.
- For any x ≠ y, choose c = 2ι/(y−x) and a = cx+ι.
- Fixing x₀ then gives the whole Legendre-PRF sequence L_k(x) = χ(k+x), up to one unknown sign.

**Public-Q operations and recovery**
- Make M oracle calls on shifted and scaled targets.
- Run Legendre-PRF key recovery for k, guessing the sign bit.
- Verify kG = Q.

**Why there seemed to be a gain.** Records H003/H018 list cheap characters of the log as a backend route. This card names a concrete algebraic source for one.

**Baseline versus predicted complete work.** Predicted gain: NONE, **even with a free oracle**.
- The ePrint 2019/1357 abstract (read) gives O(p log²p / M²) Legendre evaluations, but only for M ≤ (p log²p)^{1/4}. The best stated point is about √q·log q, which is not below square root.
- I know of no classical attack below √q with unlimited cheap queries (memory). Note that this mainly constrains the H003/H018 Legendre backend itself, not just this card.

**Second barrier.** As I remember Castryck–Sotáková–Vercauteren, they read a genus character attached to an odd prime m from Tate pairings on rational m-torsion, needing μ_m ⊂ F_p (memory; the PDF was not accessible). Here m = q and μ_q ⊄ F_p. So the analogue lives in F_{p^r} with r ≈ q, which is MOV-sized.

**Costs.** Each query needs A_{cQ+aG}, which is √q-scale. Advice: none.

**Unsupported premises.**
- (i) An F_p-rational extraction of χ_q(1+k²).
- (ii) A sub-√q Legendre key recovery with unlimited queries.

Premise (ii) alone is decisive.

**Cheapest decisive falsifier.** A full-text read of BBUV and Kaluđerović–Kleinjung–Kostić (memory citation) for the M > p^{1/4} regime. If nothing there beats √q, retire this card and also downgrade the H003/H018 Legendre-backend route.

---

## Attempts that came close but failed (check these before reopening anything nearby)

- **Generalized Jacobian with a target modulus (Q)−(O).** Because gcd(q, p−1) = 1, the q-th-root torsion lift is computable. But the resulting quasi-character is τ(Q) = A^k·(Miller value f_{k,G}), which is the H002 φ / EDS normalization with two unknowns. Using two moduli gives a Miller ratio, which is still unknown.
- **π−1 as a free degree-q isogeny in a Kani/Robert representation.** F = [[π−1, −k],[k, π̂−1]] has F*F = (q+k²)I. Its images on the rational half are public: (O,Q) and (−Q,(t−2)G). But the H-line images need kH, which is fixed only by e(G,kH) = e(Q,H) in μ_q ⊂ F_{p^r}. The degree also depends on the integer lift of k, and M-torsion images need k mod M. It is circular.
- **Near-anomaly, p − q = t − 1 small.** [p] acts as [t−1] on E(F_p), but q is a p-adic unit, so the lift error stays of order p. Torsion lifts have elliptic log 0, which repeats H003 and H026.
- **Rational points of A_Q.** The dual isogeny maps a rational point W ∈ A_Q(F_p) to a multiple of (G,Q). That is a restatement; it extracts nothing.
- **Many target-multiple rays {u(aQ+bG)} in a BSGS.** The expected cost under a Poisson heuristic is s/√C(s,2)·√(πq/8): about 1.253√q for s=2, falling toward 0.886√q as s grows, and never below it. This is Bernstein–Lange grumpy-giants territory and already covered by the W/H025 controls. No gain is claimed.

**Design note (heuristic, not an impossibility claim).** An invariant valued in F_p cannot be polynomial in k ∈ F_q, because the characteristics differ. The only bridges to structure mod q found here are q-torsion (pairings into F_{p^r}) and torus or Hecke equivariance, and equivariance alone reduces to a √-size group-action inversion. A future card in this lens needs a non-equivariant, F_p-rational readout of q-structure.

## Wave report

- **Best supported complexity:** square-root reference unchanged.
- **Verified improvement:** NONE.
- **Hypotheses tested:** Cards A and B.
- **Evidence:** paper constructions plus two primary abstracts; no runs.
- **Next decisive step:** an independent review of Card A's three lemmas, and the BBUV/KKK full-text check for unlimited-query Legendre recovery. Admit no experiment.

Sources: [ePrint 2020/151](https://eprint.iacr.org/2020/151) (abstract only), [ePrint 2019/1357](https://eprint.iacr.org/2019/1357) (abstract only).
