# Analytic discovery r133: full author-proof nominee (family 088, bounded-facet scope)

Author: Myeongjin Kang (no affiliation). Original exposition CC BY 4.0; original code MIT.
Runner provenance: Factory Droid / claude-opus-5-5 / high. Upstream pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
(stipulated true). This report assigns no gate, verdict, priority or count.

## Nominee (frozen 2026-10-20T17:21:32Z; FROZEN-THEOREM.md, sha256 86e1f30e…d354)

**Theorem.** Every convex polytope K ⊂ R^4 with non-empty interior and at most 6 facets satisfies
V_4(ΠK) <= (160/3) V_4(K)^3, with equality if and only if K is a simplex.

This is Brannen's conjectured reverse projection inequality, which is open for 4 <= n <= 8 in general, restricted
to the class of 4-polytopes with at most n + 2 = 6 facets. FHLX's counterexamples for n >= 9 lie in exactly this
class. Scope is limited to that class: nothing is claimed for general bodies in R^4, for 7 or more facets, or for
n = 5..8. The full proof is in proof.md.

## Proof architecture

1. **Exact reduction (credited, routine).** Lemma 1 is the equality form of FHLX Prop. 4.1. Lemma 2 is the Gale
   normalisation. Lemma 3 combines coarea with the Gamma–Dirichlet representation. Lemma 4 is the normal form.
   Together they give P_4(K)/c_4 = Ψ(α, b) := (1 + D(b)/10) E exp(-W^+/α - W^-/(2-α)) with W = Σ b_j E_j,
   α ∈ (0,2) and b ∈ R^4 \ {0}. b ≠ 0 holds because distinct facets have distinct normals. This is r132's R1–R4 and
   (★), now written with complete proofs, including continuity of the density versions and attainment of the
   maximum at t*.
2. **New: convex-order comparison.** W has a log-concave density, so its conditional positive and negative parts are
   IFR and hence HNBUE. A self-contained Laplace bound, E e^{-sX} <= 1/(1 + s E X), compares each part with an
   exponential of the same mean.
3. **New: scale-free reduction.** After the comparison, the slack splits into two brackets, and the scale enters
   affinely. Taking the worst α reduces (★) to the algebraic inequality
   (S)_n: D(b) P(W>0)^2 <= (n+1) E W^+, for b and -b (Proposition B).
4. **New: exact certificate for (S)_4.** For each of the ten sign patterns, partial fractions in ordered variables
   give 5 E W^+ - D p^2 = T/Den^2 with T ∈ Q[x, y]. Every coefficient of T is non-negative (minimum 2). A positive
   monomial in the always-positive variables gives strictness. certificate.py checks this exactly in under a second.

## Validation (author-run; artifact checks, not gates)

- certificate.py (exact): all 10 patterns PASS. It includes exact partial-fraction identity checks at random rational
  points, a negative control (it rejects (S)_5 for pattern (4,1,0)) and a Monte Carlo sanity check.
- geometry_control.py (float): for 40 random 6-facet 4-polytopes, the directly computed P_4 (vertex enumeration,
  recursive face volumes, zonotope volume) equals the reduction formula at t* to 1e-10. The value at t* dominates a
  400-point grid in t, Minkowski's formula checks to 1e-15, max P_4/c_4 = 0.99989 < 1, and a random simplex gives
  160/3.

## Limits and what is unpaid

- (S)_n is false for n >= 5. Near b = (-1, ε, ..., ε) the ratio tends to 2(n-1)^2/(n(n+1)) > 1. So this proof does
  not extend to n = 5..8 as stated. The obstruction is the separation of the two brackets. The unseparated
  condition, together with the box constraint b ∈ [-α, 2-α]^n, appeared numerically <= 1 for n <= 8. That is
  unproved: it would need the linearised inequality (r132 Gap 2) plus a box-face analysis.
- Polytopes in R^4 with 7 or more facets have a Gale space of dimension >= 3 (bivariate knots). Not treated.
- Classical facts (F1)–(F8) are cited without rereading primaries. Saroglou 2011, Brannen 1996/2005 and Chen et al.
  2026 were not read. See reading-limits.md. Novelty is project- and search-limited; no worldwide-priority claim is
  made.
- Late reads after the freeze: the Petty companion (introduction and consequences). No overlap was found.
- Process deviation: history-search hit lists were briefly written to /tmp, outside the root, then deleted at 17:20Z.

## Credits

FHLX §4 (sections of the simplex, the lower bound Prop. 4.1, the n >= 9 counterexamples). r132 (route R1–R4, (★),
first-variation numerics). I43/r131 (family history, simplex-product tests). Source P (products of simplices, the
counterexample for large n).
