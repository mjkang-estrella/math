# H026 algebraic ideation — raw, not accepted wholesale

TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h026-algebraic-bridges-opus-20261008-r1

Root triage: broad rejections, invariant uniqueness, conductor applicability,
and claimed necessity of q evaluations are unverified. The dual-number phrase
'only computable lift has zero tangent' is overbroad: arbitrary tangent lifts
can be chosen; compatibility with an unknown scalar is the missing condition.
Separate independent scope audits are required before adopting these negatives.
No experiment is admitted from this raw response.

# H026 independent ideation (coordinate-aware bridges): scoped no-survivor

I found no mechanism that survives. I examined five mechanisms that the records don't already cover and killed all five on paper. Each kill comes with its cost ledger and the condition that would reopen it. Some other directions turned out to repeat existing records, and I list those so they don't come back. The best supported complexity is still square-root (the usual rho/BSGS constants with negation), and verified full-work improvement is NONE.

I made no edits, ran no experiments or probes, started no child agents and made no commits. I didn't read any other H026 proposal.

## What I read

- **Workspace:** `RESEARCH_LOOP.md`, `RESEARCH_TEAM.md`, the head and tail of `STATE.md`, and the titles of every H/W record. I read in full or in large part: H019-single-query-resultant, H025-bridge-scope-corrections, H022-final-mechanism-scopes, H021-representation-scope, H015-primary-bridges-disposition, H013-coordinate-cards, H004-compact-algebra / recent-bridges dispositions, H013-algebra-disposition, H020-structured-disposition, H013-collision-baseline and H003-lift-section-disposition. I also searched the records for keywords on about 60 topics to check for duplicates.
- **Recent primary sources, abstracts only:**
  - The arXiv API listing for "discrete logarithm" + "elliptic", sorted to Oct 2026. Every classical item since Jan 2026 is already in the records (2607.09814, plus 2606.12144 and ICN 2026 via H009/H020) or has no classical ECDLP algorithm: 2601.09904 is on distortion maps, 2509.04941 on high-rank curves, 2610.07351 on ELFs. The rest are quantum.
  - Robert, ePrint 2022/1068, and Page–Robert, ePrint 2023/1766.
- **Searches:** two broad web searches found no 2025–26 prime-field point-decomposition solver.
- **Cited from memory, not verified:** the Brumer–McGuinness conductor-count heuristic, the costs of dimension-2 prime-degree isogenies (Cosset–Robert, DJRV), sparsity of Couveignes–Lercier multiplication, and the costs of superelliptic point counting.

## Cards

### C1. Counting decompositions via point counts on cyclic covers (rejected on paper)

**Public-Q computation:**
- Factor base F = {P : x(P)/α ∈ (F_p*)^n}, so |F| ≈ 2p/n.
- For the target combination R = aG + bQ, count N(R) = #{P : P ∈ F and R−P ∈ F} with the character expansion N(R) = n⁻² Σ_{j1,j2} Σ_P χ^{j1}(x(P)/α)·χ^{j2}(x(R−P)/α).
- Each inner sum is a point count on the cyclic n-cover z^n = h of E, of genus ≈ 4(n−1). Equivalently, N(R) comes from one point count on the fibre product, which has degree n².
- Exact recovery: halve F with an extra character until a single decomposition remains (O(log q) oracle calls), then verify. Then do linear algebra over the unknown factor-base logs.

**Hoped-for gain:** the count costs polylog per R, compared with |F|-scale BSGS-type testing (H019).

**Kill (independent of how fast point counting is):** the expansion has n^m terms with n ≈ p/|F|. Even if every character sum cost O(1):
- Total ≳ (#R)·n^m + |F|², where #R ≈ |F|·m!·q/|F|^m.
- Balancing gives |F| = q^{(m+1)/(2m+1)} and total work ≥ q^{2(m+1)/(2m+1)} > q for every m.
- The single-cover version needs a cover of degree (q/|F|)^m. Every known general point-counting method costs at least that much.

**Unsupported assumption:** a point-count algorithm costing far less than the cover's genus, for these specific covers.

**Cheapest falsifier:** the ledger inequality above (already done). It reopens only with a sub-genus count for these covers, together with its full cost.

### C2. Polarized quotient (E×E)/⟨(G,Q)⟩ as a k-invariant (rejected; the recent-result use)

**Mechanism:**
- K_k = ⟨(G,Q)⟩ is a rational cyclic subgroup of E² of order q.
- Without a polarization, all quotients are isomorphic: GL₂(ℤ) maps onto ±SL₂(F_q), which acts transitively on the lines of E(F_p)².
- With the product polarization, the class of the quotient determines k up to the finite group {±k, ±k⁻¹}. So, unlike isogeny or class-group transport (which commute with [k] and never mix G and Q), this is a real non-equivariant function of k.

**Kill:**
- (a) Computing it needs a prime-degree-q isogeny in dimension 2 from an explicit kernel generator. Known methods cost Õ(√q) to Õ(q) (memory citation). Robert 2022/1068 itself says building the polylog representation from a kernel goes through Vélu at Õ(N). So one evaluation is already BSGS-scale.
- (b) The invariants live in F_p and are a function of k ∈ F_q with no algebraic or homomorphic structure. Inverting them needs about q evaluations, or a paid table of comparable size. F_q-valued data such as 1+k² would need q-level objects, meaning extensions of degree ord_q(p).

**Falsifier:** exhibit an invariant with exploitable structure in k plus a sub-√q way to compute it. Neither exists.

### C3. Hecke / Eichler–Shimura relations with known coefficients a_ℓ (rejected for ordinary generic targets)

**Mechanism:** reduce a modular parametrization X₀(N) → Ẽ modulo p. Hecke correspondences then give relations Σφ(z_i) = a_ℓ·φ(z) whose coefficients are known.

**Kill:**
- A generic j mod p needs a lift with conductor around p^{6/5} (curve counts grow like X^{5/6}; heuristic, from memory). The modular-symbol space and the modular degree are then larger than p.
- Putting Q into the relations needs a preimage on X₀(N), whose degree is the modular degree.
- Small-conductor reductions are exactly the special curves we exclude.

**Falsifier:** that conductor/degree count. It reopens only with a degree-independent parametrization.

### C4. Index functional on the Couveignes–Lercier basis (extends H013's Lang card; no new cost route)

**Identity:** with ω_j = u_{O,jG}(b), each bit of k equals Tr_{F_{p^q}/F_p}(c_bit · u_{O,Q}(b)), where c_bit is built from the dual basis.

- Equivalently, it is ((1−π)_*(C·u_{O,Q}))(−G), a sum over the E(F_p)-orbit of b.
- A sanity check holds: Tr(ω_j) is constant in j, because the pushforward has at most a simple pole at O.
- C has degree about q, since a generic element of the degree-q extension needs L(dO) with d ≥ q. This adds to H013's construction cost; it doesn't compress it.

**Falsifier:** show some c_bit is represented by a function of degree o(q).

### C5. Dual-number tangent linearization, E(F_p[ε]) (rejected; sharper than the H003 analogue)

**Idea:** the ε-part scales by k, since [k]*ω = kω, so [k](G, v) = (Q, kv).

**Kill:** the constant section F_p ⊂ F_p[ε] splits reduction canonically, even for anomalous curves. Starting from Q alone, the only computable lift has ε-part 0. This is why Smart's attack needs ℤ/p², not F_p[ε].

## Comparator note (needs your check)

This applies to future decomposition cards. If H013's constant-yield assumption (B^m ≈ q) is dropped, tabulating all (m−1)-sums over a smaller unknown-log base gives:

- B = q^{1/(2m−3)}
- time and memory q^{(m−1)/(2m−3)}

That is q^{2/3}, q^{3/5}, q^{4/7}, … for m = 3, 4, 5, compared with H013's q^{(m+1)/(2m)}. It is generic, always above √q and tends to it with m!-type constants. The point is only that a dedicated decomposition solver must beat this tighter figure.

## Screened duplicates

| Direction | Already covered by |
|---|---|
| Translation-folded elliptic codes / Cheng | H006 |
| ECFFT 2-isogeny towers | PKM16 factor bases (H002 Card 2 / H004) |
| μ_d binomial and sparse-gcd elimination | YYTK / BCR (H004 / H009); my eigenvalue reformulation is the same system |
| Class-group action (Clapoti), Kani interpolation | Equivariant or missing torsion images (H004) |
| Multivariate multipoint evaluation as a join | Still needs a compressed (m−1)-sum (H020 gate) |
| Point counts / characters as a hash of Q | H017 / H019 / H004 |

Taken together, the non-equivariant relation routes split two ways (a design map, not an impossibility proof):

- **Landing sets with known logs** (intervals or progressions) reduce to BSGS/√élu, as in H019.
- **Algebraic factor bases with unknown logs** need m ≥ 5 and a decomposition solver costing q^{o(1)}. That is PKM's open T(E,m,L), and it remains the single unfilled primitive.

## Wave report

- **Best supported complexity:** square-root, with known constants and tradeoffs.
- **Verified improvement:** NONE.
- **Hypotheses tested:** C1–C5.
- **Evidence:** paper ledgers only, with no experiments. All five were rejected or found to add no new cost route; the duplicates are listed above.
- **Next decisive step:** none recommended from this lens. A future proposal should be admitted only if it supplies an explicit m ≥ 5 decomposition solver with a paid toy-size cost curve that beats q^{(m−1)/(2m−3)}.

Sources:
- [Robert, ePrint 2022/1068](https://eprint.iacr.org/2022/1068)
- [Page–Robert, ePrint 2023/1766](https://eprint.iacr.org/2023/1766)
- [arXiv 2601.09904](https://arxiv.org/abs/2601.09904), [arXiv 2509.04941](https://arxiv.org/abs/2509.04941), [arXiv 2610.07351](https://arxiv.org/abs/2610.07351) (abstracts only)
- Search results, not used as evidence: [ePrint 2017/609](https://eprint.iacr.org/2017/609.pdf), [ePrint 2017/1262](https://eprint.iacr.org/2017/1262.pdf), [ePrint 2015/1022](https://eprint.iacr.org/2015/1022.pdf), [ePrint 2025/015](https://eprint.iacr.org/2025/015), [ePrint 2024/1923](https://eprint.iacr.org/2024/1923.pdf), [PKM16](https://christophe.petit.web.ulb.be/files/16PKC_primeECDLP.pdf), [arXiv 1501.07019](https://arxiv.org/pdf/1501.07019)
