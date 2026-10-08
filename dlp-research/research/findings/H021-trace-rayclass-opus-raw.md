Raw Claude Opus review — not endorsed. Task node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h021-trace-rayclass-review-opus-20261008-r1

## Card 4 (trace / Weil restriction): the rejection stands, but its numbers are wrong

I only read the H020 Factory card 4 and the H012-PC4 disposition, plus arXiv 2407.14450v1 for the second part. I made no edits, ran nothing and committed nothing. Verified improvement stays **NONE**.

**What is correct.**
- Tr(R) = R + πR maps E(F_{p²}) onto E(F_p). Restricted to E(F_p) it is doubling, which is a bijection because q is odd.
- The kernel is the twist part, of odd order q′ = 2p+2−q.
- E(F_p) ∩ ker Tr = E[2](F_p) = 0, so E(F_{p²}) = E(F_p) ⊕ ker Tr.
- The q-part of log R is therefore ½·log_G(Tr R).
- The card leaves out a factor of 2. Applying Tr to R₀ = R₁ + R₂ gives **2R₀** = Tr R₁ + Tr R₂, not R₀. This is harmless but should be written correctly.

**Error 1: the "2 equations, 2 unknowns" system solves the ambient relation, not the trace relation.**
- **Ambient relation** R₁ + R₂ = R₀ in E(F_{p²}): Weil restriction of S3 gives 2 equations over F_p in t₁, t₂, with bidegree ≤ (2,2).
  - There are about p²/2 pairs and the group has size about qq′ ≈ p², so a random R₀ has O(1) solutions.
  - Each attempt costs polylog. This part is correct.
- **Trace relation** Tr R₁ + Tr R₂ = 2R₀: this only says R₁ + R₂ lies in a coset of ker Tr, which has size q′.
  - The expected number of solutions is about (p²/2)·q′/(qq′) ≈ p/2.
  - So it is one equation over F_p in (t₁, t₂). Its solutions form a curve, not O(1) points.
- The ambient relation implies the trace relation, but not the reverse.

**Error 2: with the full factor base, the trace relation is trivial.**
- Pick t₁, set S₂ = 2R₀ − Tr R(t₁), then solve the one-variable equation x(Tr R(t)) = x(S₂).
  - This equation has constant degree after squaring away √N(f(c+wt)).
  - It succeeds with constant probability, assuming the image Tr(F) is a constant fraction of the group (not proven).
- So the Weil system adds nothing.
- The unknowns are the logs of Tr(F)/±, which is at most (q+1)/2 values. Its actual size and whether the relations reach full rank are both **unproven**.
- In effect the factor base is most of E(F_p), which is the generic setting.

**Error 3: the restricted base (|T| = m) rates.**

| Route | Success per attempt | Cost per attempt | Total |
|---|---|---|---|
| Ambient 2×2 solve, both tᵢ ∈ T | m²/p² | polylog | p²/m + m² → **p^{4/3}** at m = p^{2/3} |
| Trace: enumerate t₁ ∈ T, solve for t₂, test t₂ ∈ T | m/p | polylog | ≈ **p** relation work + m² linear algebra |
| Trace: hash table of Tr R(T), m lookups per R₀ | m²/q expected hits | m | ≈ **p** |

The card's "m²/p per attempt at polylog cost" takes the trace relation's solution count and pairs it with the ambient relation's solving cost. **No stated algorithm reaches p/m + m².** That formula is also not a lower bound for anything. It is the cost shape of an index-calculus run that needs about m relations and m² linear algebra, under heuristics that card 4 does not establish: the image size, equidistribution of Tr R(t) over T, and rank.

**Corrected algorithm.** The best honest version is trace-based relation collection with a hash table. It costs about q (≈ p) group operations plus about m² sparse linear algebra, plus heuristic rank, and it loses to √q by a factor of about √p.

**Missing primitive.** To reach p/m + m², you would need a polylog oracle that, given R₀, finds (t₁, t₂) ∈ T² with Tr R(t₁) + Tr R(t₂) = R₀, or certifies that none exists, for a structured T of size m.
- For an algebraic T (the zero set of a degree-m polynomial g, such as a multiplicative subgroup), this is a restricted summation-polynomial solve costing at least poly(m). That is exactly H012-PC4 / Petit–Kosters–Messeng territory.
- Composing with the trace only raises the degree.
- Even with this oracle, p^{2/3} > √q, so the card gives no route either way.

**Cheap falsifier.** No experiment is needed; the counting above is a proof. If a toy check is wanted: for p ≈ 10³ and fixed R₀, count pairs (t₁, t₂) ∈ F_p² that satisfy the trace relation versus the ambient relation. The prediction is about p/2 versus O(1).

The Gaudry 2009 / Diem n=2 citation comes from memory in the card, and I did not re-verify it here.

## H021 marked-point ray-class lead: yes, it hides the whole DLP in this instance

**Source.** Arpin, Castryck, Komada Eriksen, Lorenzon, Vercauteren, arXiv 2407.14450v1. I read the abstract and the HTML of §3.5 and §4 through a summarising fetch tool, so I have no verbatim PDF quotes.
- §4 reduces generalized vectorization to plain cl_O vectorization "potentially at the cost of a discrete logarithm computation", via Weil pairings.
- The same section says equality testing on these orbits is the obstacle.
- §3.5 ("cyclic torsion"): when O/𝔪 is cyclic, every group isomorphism O/𝔪 → E[𝔪] is automatically an O-module isomorphism.

**Hypotheses check.**
- O = End(E) ⊇ Z[π]. Computing it is a paid cost. My memory, not re-checked: Kohel / Bisson–Sutherland, roughly subexponential in p.
- N(π−1) = #E(F_p) = q is prime, so 𝔪 = (π−1) is a degree-1 prime and O/𝔪 ≅ F_q.
- q is coprime to the conductor: q | v with t²−4p = v²d would need q² < 4p, which is impossible.
- 𝔪 is coprime to p unless the curve is anomalous (q = p), which is already solved by Smart's attack.
- q is generically split; it can ramify only if q divides the field discriminant d_K, so this needs a separate check.
- E[𝔪] = ker(π−1) = E(F_p), so a level structure is the same as a choice of generator.
- O^* = {±1} gives the quotient (Z/q)^*/±1. For j = 0 or 1728 the quotient is by μ₄ or μ₆, matching the known automorphism constants.

**The conversion already contains the hard part.**
- (E,G) and (E,Q) sit on the same curve, so plain vectorization is trivial (𝔞 = O).
- The connecting class lies in ker(Cl(𝔪) → Cl) ≅ (O/𝔪)^*/O^* ≅ F_q^*/±1. It is the class of a principal (α) with α ≡ k mod 𝔪, and α acts on E(F_p) as [k].
- So in this instance, ray-class vectorization is polynomial-time equivalent to the ECDLP given O:
  - Knowing k, CRT builds α directly.
  - Any representative ideal with its residue data reveals k.
- Principalization cost is irrelevant. My memory says it is L_{|d|}(1/2) (Hafner–McCurley / Buchmann), not re-checked. The bottleneck is turning the public Q into any ideal representative, and that map is a computable inverse Φ⁻¹: E(F_p) → O/𝔪, which is the DLP itself.

**Equivariance falsifier (scoped).** E(F_p) is cyclic, so every endomorphism acts on it as a scalar. Any construction built only from End-actions and isogeny transport of the marked point therefore commutes with [k]. It cannot tell (E,G) from (E,[k]G) except through a comparison step that is itself the DLP.

This does **not** rule out all ray-class methods. A k-sensitive invariant would have to go through the other eigenspace E[𝔪̄], whose points are defined over F_{p^{k′}} where k′ is the embedding degree. That is the card 3 / R2 wall, and modular-unit evaluations at level Γ₁(q) cost at least about q.

## Survivors, errors, next gate

- **Survivors:**
  - The trace surjectivity and splitting lemma, recorded as a correct lemma.
  - Card 4's rejection, now justified by the corrected counts (≈ p trace collection or p^{4/3} ambient, both above √q).
  - The ray-class lead, only in the narrow form "find a poly-time, k-sensitive map from (E,Q) to (O/𝔪)^* that is not an End-equivariant construction."
- **Errors to record:**
  - The trace relation is 1 equation, not 2.
  - The card's "m²/p at polylog cost" does not exist; the achievable rates are m²/p² ambient or m/p trace.
  - p/m + m² is neither achieved nor a lower bound.
  - The missing factor 2 in 2R₀.
  - The image size and rank of the trace factor base are unproven.
  - The ray-class target conversion is equivalent to the DLP.
- **Next gate (paper only):**
  - Card 4 reopens only if someone supplies a restricted 2-decomposition solver that runs below poly(m), the same open requirement as H012-PC4.
  - The ray-class lead reopens only if someone supplies an explicit map Ψ(E,Q) that does not go through E[𝔪̄]. A small-q table check (does Ψ(E,[k]G) depend on k as a character?) would then falsify or keep it.
  - No infrastructure is needed for either.
