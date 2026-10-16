# Scoped formal coverage supplement

This supplement integrates the actual scoped formal PASS without changing the frozen manuscript. The original author README's "independent semantic audit pending" and paper metadata's pending formal-integration fields describe earlier stages; they remain byte-preserved historical records. This supplement and the actual parent disposition provide the later state. The final independent manuscript gate is still pending here.

The independent review `staircase-formal-review-r1/review.md` has SHA256 `92b21ed40425c72be41c00a4eb65e2d349b33e8dfeffe3bbb930067cbe30b254`; its output manifest has SHA256 `1d1b217da179bd012e12006f35348ce4c7b3a43fed7a86047db919ea54fd3327`. The parent disposition has SHA256 `280128251a8b315e51b5b1baa4b843b8c7c981117b81f8db2becd74bce0c8494`. All are included as their actual bytes and fixed in the allowlist. Parent authentication records 28 review inputs and 41 outputs, fresh compilation and exact types for 16 author theorems and 4 definitions, 18 review theorems and 26 public review declarations, three actual semantic mutation rejections, and only standard axioms `propext`, `Classical.choice`, `Quot.sound`. These are scoped source/review facts, not counts of formalized staircase results.

The substantive author source is `StaircaseSupport.lean`, SHA256 `a8a8473d98a673790eb8e72546b890aa93bfba02351a97f401c39d4dbc10e989`; its output manifest has SHA256 `5ff7c5b4e0504d88e1409065129bcef9737160d9484abaa212c7bd69151fd3a0`. The exact paper snapshot is present at `staircase-formal-review-r1/context/main.tex` and equals the frozen `staircase-manuscript/main.tex` bytes.

For any commutative unital ring R, finite group G, R-module M, representation ρ, vector z and R-linear functional θ, the support proves the conditional regular-coordinate mechanism. Its explicit hypothesis `Separates ρ z θ` says θ(ρ(g)z) = δ(g,1). The maps are

```text
I(a) = Σ_g a(g) ρ(g) z
P(x)(g) = θ(ρ(g⁻¹)x)
(h·a)(g) = a(h⁻¹g).
```

It proves equivariance, P∘I = id, injectivity of I, a complementary kernel and stability of both submodules, conditional on that separating hypothesis. The regular module uses finite function coordinates. The source has generic finite-coordinate actions and unbundled intertwining equations, not bundled group-algebra-linear identifications.

The arbitrary-algebra support proves that scalar extension preserves GIVEN split maps and intertwining equations without flatness. It does not construct or identify staircase Specht lattices or their extended tensor cubes. The integer-square support proves that a zero sum of squares of integer deficits forces each deficit to vanish; it does not derive the support budget or any palette premise.

The independent review supplies a proper integral summand in the nonfree ambient module Z^6 ⊕ Z/2 with noncommuting S3 action. It tests the correct left-action/inverse convention, an arbitrary algebra, a nonflat mod-2 split control, the zero ring, and the counterexample that doubling Z is injective but becomes zero and noninjective after extension to Z/2. Three altered source definitions actually fail proofs: missing inverse, right coordinate shift, zero normalization. Their compiler rejection logs are supplied as negative evidence and must not be mistaken for errors in accepted source.

Not formalized: Specht lattices and polytabloids; the staircase tensor-cube generator; triangular palette uniqueness; expansion support and global square budget; unit sign +1; existence/construction of the staircase separating functional; an all-m instance of `Separates`; the paper's full `thm:main`, `prop:unit` or `lem:palette`; bundled group-algebra, scalar-extended action and Specht base-change equivalences; constituent/projective multiplicity consequences. There is no full formal theorem certificate. General `Separates` is a hypothesis, not a custom axiom proving the staircase instance.

`paper-correspondence.json`, the author's exact README and the full independent review carry the precise paper-label/declaration map. The regular-summand/separating-product mechanism is classical Bryant–Kovács; triangular uniqueness is credited to Ikenmeyer; the deficit mechanism is inherited from the pinned source. I21 plus Harman–Ryba already supply the complex regular-containment antecedent. No new classical mechanism or worldwide priority is asserted.
