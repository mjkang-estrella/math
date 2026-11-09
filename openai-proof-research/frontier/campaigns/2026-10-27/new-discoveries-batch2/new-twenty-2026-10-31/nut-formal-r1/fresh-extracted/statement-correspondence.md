# Statement correspondence

All graph vertex types in this packet use `V : Type` (universe 0). Abstract
linear algebra helper lemmas are universe-polymorphic. The requested endpoint
permits universe 0. The exact types and bodies appear in the full audit log.

| Source or obligation | Lean declaration | Status |
| --- | --- | --- |
| Finite simple undirected graph | `SimpleGraph V`, `[Fintype V]` | Library definition |
| Every degree is 3 | `Nut8.Cubic` | Definition |
| Real 0/1 adjacency operator | `Nut8.adjacency` | `Matrix.mulVecLin (G.adjMatrix ℝ)` |
| Nontrivial, real kernel dimension 1, full nonzero kernel vector | `Nut8.Nut` | Definition with `2 ≤ card`, `finrank ker = 1`, explicit vector |
| Cyclic generator, exactly l equal-sized orbits | `Nut8.Circulant` | Integer-power orbit equivalence, quotient `Nat.card`, common orbit size |
| Equal orbit sizes imply common period | `pow_eq_one_of_equal_orbits`, `circulant_semiregular` | Proved; generator-only formulation |
| Local orbit has exactly that period | `orbit_period_iff`, `labelOrbit` | Proved, including singleton orbits |
| Positive orbit size on nonempty V | `orbit_size_pos` | Proved |
| Adjacency intertwines automorphism pullback | `adjacency_pullback`, `kernel_stable` | Proved for every graph automorphism |
| One-dimensional stable subspace is scalar | `stable_line_scalar` | Proved |
| Finite-period real scalar is ±1 | `iterate_scalar`, `scalar_is_sign`, `stable_line_sign` | Proved, negative case has even period |
| Full nut kernel transforms by a sign | `nut_sign_character` | Proved with explicit positive-period hypothesis |
| Conjecture 16 / published Conjecture 1 | `Nut8.Target` | Exact proposition definition ONLY; unproved |
| Source cyclic subgroup ↔ chosen generator | No subgroup-level declaration | Ordinary equivalence; formal bridge missing |
| Quotient matrix and complete finite obstruction | No declaration | Missing |
| Two list determinant values | `CertificateBench.sampleInvertible`, `sampleCofactor` | Kernel checked computations; no `Matrix.det` bridge |

Fully qualified graph declarations have prefix `Nut8.`; determinant samples have
prefix `Nut8.CertificateBench.`. `Nut8.Target` literally quantifies W, Fintype,
DecidableEq, G and DecidableRel G.Adj and negates Cubic ∧ Nut ∧ Circulant 8.
No theorem asserts this target. Cubic is not used in the existing sign lemmas;
that is an honest general helper, not the claimed cubic-8 obstruction.
