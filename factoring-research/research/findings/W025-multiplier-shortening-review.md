# W025 review: computed common multiplier for root-chart carries

2026-10-08 local / 2026-10-09 UTC. **Accept W025 §1–§3 as correct upper bounds for a representation that preserves coverage, the nonzero filter, and the localization interface. Repair the comparison: the headline gain is measured against a weak baseline. In the advertised thin regime, an elementary precision truncation with no integer program gives a strictly shorter carry, N^(39/120) rather than N^(47/120). With singleton v-charts and V≤H^(1/2), the univariate W025 bound is dominated by truncation or a truncation-plus-multiplier hybrid throughout its stated domain. The domination is polynomial when V≤H^(1/2−δ), including the headline case V≈1. Verified new complete factoring improvement: NONE.**

The scope is the frozen [verbatim brief](W025-multiplier-shortening-review-evidence/task-brief.md), W025.md at SHA-256 `54eefe45…155826`, and the hashes and read scope in [input-hashes.sha256](W025-multiplier-shortening-review-evidence/input-hashes.sha256) and [read-scope.json](W025-multiplier-shortening-review-evidence/read-scope.json). W022 A/A2/A3, the W024 sign filter and prime schedule, and W020's extractor are imported at their accepted interfaces. They were not re-audited. One frozen certificate was run (§7). The parent continues the constructive work. This review prices only the univariate singleton case; the parent is pricing the bivariate case separately.

## 1. Pigeonhole existence and constructive acquisition: accepted

Points j·d_ν/Q mod 1 for j=0,…,B lie in [0,1)^|J|. Each coordinate is cut into K_ν half-open intervals, which gives B boxes, so two of the points share a box. Their index difference c lies in [1,B]. Each coordinate difference lies in (−1/K_ν, 1/K_ν) and equals c·d_ν/Q−k_ν, so |e_ν|<Q/K_ν. For positive integers, the largest integer below Q/K equals ceil(Q/K)−1, which equals floor((Q−1)/K). This is exactly (1). For empty J we have B=1 and c=1. If K_ν≥Q, only e_ν=0 is allowed; existence still holds, but then B≥Q and the fallback is triggered.

(1) together with 1≤c≤B is a system Ax≤b in |J|+1 integer variables. Its data length is O(|J|·log(QB)). Lenstra's paper states polynomial solvability for fixed n with data length n·m·log(a+2). It also states explicitly that when the set is nonempty, "our algorithm actually produces an element x ∈ K∩Z^n" ([retrieved PDF](W025-multiplier-shortening-review-evidence/sources/lenstra1983.pdf), extracted text lines 36–60 and 351–353). The polynomial's degree is exponential in n, so the dimension 3 used in §3, or any fixed degree-bounded dimension, contributes only a constant. Per chart the cost is poly(log N) bit work, and it is alpha-independent. No shortest-vector oracle is used. The lower bound c≥1 correctly excludes the c=0 / k=±1 lattice vector. The proofs in Lenstra's paper were not audited.

Narrow prior art: this is a weighted (anisotropic sup-norm) good simultaneous Diophantine approximation with a bounded denominator. Lagarias (SIAM J. Comput. 14, 1985, 196–209) observes in his abstract that Lenstra's result gives polynomial-time sup-norm best approximations in fixed dimension ([Crossref metadata](W025-multiplier-shortening-review-evidence/sources/lagarias-crossref.json); only the abstract was read). Dirichlet's pigeonhole is classical. No novelty claim.

## 2. Valuation normalization: accepted, and necessary in practice

B<Q gives 0<c<ℓ^L, so v=ν_ℓ(c)<L and Q'=ℓ^(L−v)≥ℓ. Since r divides both c and Q, it divides each active e_ν, and e'_ν=c'd_ν−Q'k_ν. For inactive ν, the centered value e'_ν≡c'd_ν (mod Q') has |e'_ν|≤Q'/2. Hence P≡c'R (mod Q').

- Active terms satisfy |e'_ν|w_ν/Q'=|e_ν|w_ν/Q<w_ν/K_ν≤T.
- Inactive terms satisfy |e'_ν|w_ν≤Q'T/2.
- The ratio c'/Q'=c/Q.

From S≡σR (mod Q) we get c'S≡σc'R≡σP (mod Q'), because Q'|Q. Every true scaled sum is therefore represented, with |τ|≤cW/Q+D·T≤BW/Q+DT. (2) holds with either floor or ceiling.

The problem is not hypothetical. In certificate case K1, which is a genuine W022 chart, the least feasible multiplier is c=18=2·3². Without stripping, every exponent would be ≡0 (mod ℓ) and the W024 filter would delete everything. The resulting Q'=ℓ (K4) and ℓ-power multipliers (K3) are legal. The low precision only lengthens τ, and that is already counted through cW/Q.

## 3. Concrete univariate quartic: every inequality checks

Assume Z≥2 and 1≤A≤Z².

- **T bounds.** T=ceil(cuberoot(A·Z⁷)) is computed by exact integer search. A·Z⁷≤Z⁹ gives T≤Z³, and A≥1 gives T≥Z^(7/3)≥Z².
- **B bounds.** Coefficients 0–2 are inactive. Coefficient 4 is active because T≤Z³<Z⁴. If T=Z³, coefficient 3 has K₃=1, so its constraint is vacuous and its term is ≤Q'T/2. Both quotients Z³/T and Z⁴/T are ≥1, so K_i≤2Z^i/T and B≤4Z⁷/T². Then BW/Q≤BA≤4AZ⁷/T²≤4T.
- **Height of P.** The lower three terms total at most (Q'/2)(1+Z+Z²)≤Q'Z²≤Q'T, using 1+Z≤Z² for Z≥2. The two upper terms are each <Q'T. So |P|≤3Q'T, and every covered |τ|≤4T+3T=7T.
- **Edge Z=1.** This edge is excluded by the brief but is harmless: there T=1 and the same conclusion holds.
- **B<Q.** This is not automatic. A sufficient public condition is 4Z³<Q, since B≤4Z⁷/T²≤4Z³. With xlo=0 and Z≤max(1,U_s/H_s)≤m_s^(3/5), it holds once m_s>4⁵. Small m_s, and certificate case K5 (Q=9, Z=4, B=30), take the fallback.

**Domain repair (optional).** For Z²<A≤Z⁴, the formula above does not establish (3). Use T=ceil(sqrt(A·Z⁴)) with J⊆{4} instead. Then B≤2Z⁴/T≤2Z, BA≤2T, |P|≤2Q'T and |τ|≤4T. This gives carry O(A^(1/2)·Z²)≤O(A+Z⁴), and it is continuous with the first regime at A=Z².

## 4. Exponent arithmetic: correct, with one interpretation note

All displayed powers check:

- Z≈M^(3/5), A≈N^(1/2)·M^(−3/2), T=O(N^(1/6)·M^(9/10)), B=O(N^(−1/3)·M^(12/5)).
- At M=N^(1/4): A=N^(1/8), Z=N^(3/20), T=N^(47/120), B=N^(4/15)<N^(1/2).
- Occurrences: the old N^(17/20) becomes N^(77/120).
- The general-V insertion V^(−7/3) is correct when A≤Z²≈M^(6/5)/V², B<Q and H>2V (the last is sufficient for singleton charts per W022). Lower strata need their own A_s and Z_s.

The thin W≈sqrt(MN) scale implicitly assumes Up≈Vq, i.e. q/p≈M. At M=N^(1/4) this means p≈N^(3/8). Rho-type or deterministic √p-type factor finding is then about N^(3/16), which confirms the brief's own statement that this regime gives no factoring gain.

## 5. Main finding: the weak baseline, and a dominating elementary representation

W025 treats the degree-3 and degree-4 coefficients as generic residues mod Q. They are not. Every W022 coefficient carries H^(i+j) (W022 §3). After substituting a singleton y, the coefficient of x^i is ≡0 (mod ℓ^(min(i·a, 2h))), where H=ℓ^a. The certificate checks this divisibility in K1 and K2. In K2 (h=4, H⁴=Q) the quartic coefficient vanishes outright, so W022's 15QZ⁴ envelope was itself loose there.

**Truncation representation (no integer program).** For a level j≤2h, keep only the coefficients with i·a<j, centered mod ℓ^j. Then S≡σR (mod Q) implies S=σP_j+ℓ^j·τ with

```
|τ| ≤ (W + (ℓ^j/2)·Σ_{i·a<j} Z^i) / ℓ^j.
```

At the constant term, P_j≡r₀ (mod ℓ), and ℓ divides ℓ^j. The W024 residue ε_σ, nonzero exponents, true-leaf retention exactly when p≢1 (mod ℓ), and E=(p−1)(vq−u) are all unchanged. There is no multiplier, no new root, and one modulus per stratum. This is W025 with c=Q/ℓ^j normalized to c'=1, Q'=ℓ^j. In K1 and K2, c_struct=Q/H³ is in fact a feasible ILP point. The W025 integer program contains these choices, but its pigeonhole bound does not capture them.

At j=3a (Q'=H³), in the thin regime, the carry is O(W/H³+Z²)=O(N^(1/2)·M^(−7/10)+M^(6/5)). At M=N^(1/4) this is **N^(39/120)**, against W025's N^(47/120). Occurrences become **N^(69/120)**, against N^(77/120).

**Hybrid representation.** Take Q₁=H⁴, so the quartic term vanishes. Apply W025 §1–§2 modulo Q₁ to coefficient 3 only, with A₁=ceil(W/Q₁) and T=ceil(sqrt(A₁·Z³)). If Z≤A₁≤Z³, this gives B≤2Z³/T, |P|≤2Q₁'T and |τ|≤4T.

**Domination claim.** This compares exponents up to fixed-ℓ constants, using top-stratum geometry Q≈H⁵ and Z≈H^(3/2)/V. If V≤H^(1/2), then across W025's whole domain 1≤A≤Z²:

- For A≥H^(1/2)/V, the hybrid is valid. Its ratio to W025 is A^(1/6)·H^(−3/4)·V^(5/6)≤H^(−1/4)·V^(1/2)≤1.
- Otherwise truncation at level 3 gives O(Z²), which is ≤Z^(7/3)≤W025's bound.

For H^(1/2)<V<H/2, W025 can win in part of its domain. Repair: compute every public option (all O(log Q) truncation levels, plus the multiplier on the surviving top coefficients) and use the minimum. A two-parameter search over the multiplier cap and T is monotone in both and costs O(log²) Lenstra calls per chart.

**Remaining gap to the true frontier.** Within a common-carry box, every option still pays at least c·W/Q per point. The per-point genuine width totals O(M+W/M)=N^(45/120) (W022 §1). So the best option found here (N^(69/120)) still pads by about N^(1/5) in this regime. No lower bound for other representations is claimed.

## 6. Interfaces: filter, alpha, localization, sharing

- **Sign filter.** For all x and all τ in the interval, E'≡c'·ε_σ (mod ℓ), because P≡c'r₀ (mod ℓ) and ℓ divides Q'. This was checked across full intervals, including the τ endpoints ±7T.
- **True leaf.** E'=c'(p−1)(vq−u) is nonzero exactly when p≢1 (mod ℓ).
- **W020.** W020 accepts arbitrary nonzero integer exponents with the original uniform alpha, and c' is public and alpha-independent, so the ≤2 expected-trial composition is unchanged once an evaluator exists.
- **Widths.** Exponent widths grow by only log B bits.
- **Restrictions.** Child boxes may keep the same c', P and Q'. Recomputing them for tighter children is optional and must be paid for.
- **Lost sharing.** Each chart now has its own c' multiplying the linear part u+Nv, its own Q', and different coefficients. Any evaluator that shares the α^(u+Nv) progression or a coefficient array across charts loses that sharing. Truncation keeps c'=1 and one modulus per stratum, which is another point in its favor.

## 7. Frozen certificate (single run)

The [predictions](W025-multiplier-shortening-review-evidence/certificate/predictions.md) (`c7e6fde8…`) and the [code](W025-multiplier-shortening-review-evidence/certificate/w025_cert.py) (`2101a89d…`) were frozen before the run. The run used python3 -I with a 60 s timeout and finished in 0.025 s, using 2,152 of 20,000 charged events. Status: completed, **0 violations, all predictions P1–P8 held** ([output](W025-multiplier-shortening-review-evidence/certificate/run-output.json)).

| Case | Setup | Outcome |
|---|---|---|
| K1 | ℓ=3, h=5, v=−1, signed singleton y=−1 | c=18, Q'=6561; max τ 2077 ≤ 7T=28042; truncation bound 1286 (observed 652); true leaf retained |
| K2 | ℓ=5, h=4, v=+1 | c=2; quartic coefficient ≡0; 7T=14658 vs truncation bound 617 |
| K3 | synthetic | forced c=9, Q'=81 |
| K4 | synthetic | c=3, Q'=ℓ=3 |
| K5 | fallback test | B=30≥Q=9, fallback taken |

The search is a literal bounded one. It certifies only the identities and existence for these cases. It is not a Lenstra implementation and says nothing about asymptotics.

## Disposition

**Accepted:** §1–§3 as correct, constructive, polylog-per-chart upper bounds, with the normalization and filter interfaces intact.

**Repaired:**
- The comparison baseline: the min-over-options rule in §5.
- The domain extension for Z²<A≤Z⁴ in §3.
- The headline: the best univariate supplied representation in the thin M=N^(1/4) regime is precision truncation, with carry N^(39/120) and occurrences N^(69/120). W025's multiplier is not needed there.

**Counterexamples** to stronger readings:
- The "generic coefficient" frontier, refuted by K1/K2 c_struct feasibility and the domination argument in §5.
- c coprime to ℓ (K1).

**No counterexample** to the stated W025 bounds was found. The next useful object is still a paid shared product evaluator over the truncated boxes. The bivariate version should use the H^(i+j) total-degree valuations before any pigeonhole. **Verified complete factoring improvement: NONE.**

Only this report and its evidence directory were written. There was no delegation, install, commit, or change to the solver, Lean, STATE, registry or task files.

At handoff, all frozen inputs on which the review depends still matched their hashes, and so did the frozen certificate code and predictions. Two files had changed concurrently and were not substituted: docs/SPECIFICATION.md, which was read only for the contract, and Factoring/RootCharts.lean, which was hashed but not used. The [delivery manifest](W025-multiplier-shortening-review-evidence/delivery-manifest.sha256) fixes the final evidence.
