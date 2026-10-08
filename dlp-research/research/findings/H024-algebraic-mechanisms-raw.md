# Raw H024 Claude Opus report — UNREVIEWED

TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h024-algebraic-mechanisms-opus-20261008-r1

Not accepted claims; preserve uncertainty and check scope before integration.

**Verdict: no surviving mechanism with a real reason to expect an exponent gain. Verified improvement stays NONE.** Some mechanisms do lead to a precise missing primitive (listed below), but none has a positive reason to work.

This pass produced one bounded card. It is a new exact identity that closes a gap left open by H003, plus one narrow open window. A second idea folds into existing records. I worked read-only: no edits, runs, child agents or commits.

**Sources.** In the repo I read README, RESEARCH_LOOP, RESEARCH_TEAM, STATE, and these records: H002 EDS normalization and marked surface, H003 EDS character collapse, literature scope/reconciliation and orbit invariants, H013 MCL raw report, H015 bridges, H018 information raw report, H019 single-query resultant, H021 representation scope, list reduction and public-signal reviews, and H022 subset screen. I also keyword-searched all findings and hypotheses. I read **no external sources** this session. Every outside citation below is from memory and needs a primary read before anything is accepted.

## Card A — power-residue characters of Lauter–Stange's φ

**Setting.** φ is the accepted H002 normalization: φ(nP) = φ(P)^{n²}·W_P(n), defined because gcd(q, p−1) = 1 (H021). H003 handled only the quadratic character. This card covers every order.

**Identity 1 (σ-function equation).** Combine φ(nP) = φ(P)^{n²}·W_P(n) with the standard ψ_{n+m}ψ_{n−m}/(ψ_n²ψ_m²) = x(mP) − x(nP). For R, S, R±S ≠ O this gives:

  φ(R+S)·φ(R−S) = φ(R)²·φ(S)²·(x(S) − x(R)).

So φ behaves like a Weierstrass σ-function on E(F_p).

**Identity 2 (collapse for every order).** Take a prime ℓ dividing p−1, and let χ_ℓ be a character of order ℓ. Set T = [ℓ^{-1} mod q]S. Then φ(ℓT) = φ(T)^{ℓ²}·ψ_ℓ(T), and χ_ℓ kills the φ(T)^{ℓ²} factor:

  χ_ℓ(φ(S)) = χ_ℓ(ψ_ℓ([ℓ^{-1}]S)).

- At ℓ = 2 this is exactly H003's χ(2y([2^{-1}]R)).
- For a composite order d, use the smallest m with d | m².
- I first expected odd ℓ to escape H003's collapse via a long product along the halving orbit (because 4 is invertible mod ℓ). That expectation is wrong: dilation by m = ℓ collapses it anyway.

**Consequence (scoped negative).** ψ_ℓ has simple zeros on E[ℓ]∖O and pole order ℓ²−1, so it is not a proper power. Chen's bound, as already applied in H003, then caps every additive or multiplicative-character coefficient of F_ℓ = χ_ℓ∘φ at about 2ℓ²√p/q. This rules out every order ℓ ≲ p^{1/4}. In particular it rules out the H003 sufficient regime (coefficient ≥ q^{-1/12}) whenever ℓ ≲ q^{5/24}. These are paper derivations and need independent checking. The collapse may already be known from Shparlinski–Stange, which I have not checked.

**Open window.** Primes ℓ dividing p−1 with ℓ > p^{1/4}:
- F_ℓ is compact to evaluate: O(log ℓ + log p) field operations.
- It lies beyond the Weil-type ceiling, so nothing in the repo excludes it.
- **Bridge if it held:** a coefficient of size q^{-β} feeds the existing H003 Fourier/HNP backend or the MCL coset-BSGS backend (about q^{1/4} if an order near √q were usable). Recovery is exact by scalar check.

**Evidence against.** Identity 1 gives a rigorous partial uniformity. For each m ≠ 0:

  |E_n F(n+m)·F(n−m)·F̄(n)²| ≤ (4√p + O(1))/q,

because the inner sum is a complete character sum of x(M) − x(·), which has degree 2 and is not an ℓ-th power. This controls only the anti-diagonal of the Gowers U² average. It does **not** bound the largest Fourier coefficient. Under a pseudo-randomness heuristic the coefficients are about q^{-1/2}, which would mean no gain.

**Missing assumption.** Some structure that concentrates the spectrum for large ℓ. I have no positive reason to believe it exists; my prior is low.

**Cheapest falsifier (optional, never run).** On toy curves with a prime ℓ ≈ p^{1/3} dividing p−1, compute F_ℓ at all q points and the full additive and multiplicative-character transforms. Use at least 3 sizes with q ≤ 2^16 to stay near 1M events. Kill the card if the maximum coefficient tracks a random μ_ℓ-valued baseline of about √(log q / q).

## Folded into existing records — diamond-operator characters

ECDLP (up to sign) is the diamond operator ⟨k⟩ on the fiber of X₁(q) → X₀(q). Subcovers through X₂(q), Mazur's Shimura cover (from memory), would give χ_n(k).

- **Exact degree bound.** Fix E. A rational function realizing χ_n∘log exactly on E(F_p)∖O takes n values on q−1 points, so its degree is at least about (q−1)/n.
- **The base value carries nothing.** At (E, E(F_p)) the q-isogeny is π−1, so E′ ≅ E and the X₀ Kummer value is a fiber constant with no information about k.
- **Merges with:** H018's Nebentypus route and the H013 MCL card.

## Seeds rejected

| Seed | Reason |
|---|---|
| Vélu sums with kernel E(F_p) via π−1 | Compact, but invariant under translation by G, so zero information about k. Prime order means there are no proper sub-kernels. |
| Interval products ("elliptic factorial") with bisection | Already in H019 / H002 card 4 at Õ(√L) per level. W(k) is exactly the second-order product of x(G) − x(jG), and φ(Q) = φ(G)^{k²}·W_G(k) is a masked evaluation of it: two unknowns. Beating √L would need a factorial-type advance (Strassen; Shub–Smale context, from memory). |
| Kedlaya–Umans / algebraic multipoint evaluation; ECFFT | The intermediate objects already have size n² (H019 three-list case). ECFFT saves only log factors and needs auxiliary subgroups of smooth order. |
| Targets with order divisible by q | F_{p^r}* with r = ord_q(p): pairing route. Additive F_q: is the DLP itself. Ray-class or conductor-q² class groups: H021's missing conversion. Jacobians of covers: ambient group size p^g. |
| F_p*-logarithms of φ | A subexponential L(Q) still leaves k² inside the masking term. Matches Lauter–Stange's equivalences (from memory). |
| Collinearity-determinant 3-lists; CDH-style operations; Legendre/power-residue PRF backends; dual-number lifts | Already covered: SP3/H021, H018 N2, H013, H003/H010. |

**Next decisive step.** First, an independent check of Identities 1–2 and the Chen scoping. Second, a primary-source read of Shparlinski–Stange and Lauter–Stange to settle prior art for the collapse. Only after that, and only if the coordinator wants it, the toy spectrum falsifier above.
