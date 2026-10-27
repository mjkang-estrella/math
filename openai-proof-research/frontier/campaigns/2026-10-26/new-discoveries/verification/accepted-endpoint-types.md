# Checked accepted endpoint types

Extracted from retained strict-replay Checks.log files whose bytes and complete
payloads match the accepted archives. These are all configured headline
endpoints, including credited background/helper endpoints where retained. Only
the scoped combined outcome, not every endpoint, earns credit. This index is
not a new Lean compile or a new mathematical review.

## 1. Sharp converse fractional-binomial inequality

Checked from [build/fractional-binomial-packet-audit/fractional-binomial/build/verified/Checks.log](../build/fractional-binomial-packet-audit/fractional-binomial/build/verified/Checks.log).

```lean
FractionalBinomial.source_conjecture_352508 (k : ℕ) {a x y : ℝ} (ha : 2 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
  (x + y) ^ (a * ↑k) ≤ 2 ^ (a - 1) * FractionalBinomial.binomialSum k a x y
```

```lean
FractionalBinomial.homogeneous_biased_bound (k : ℕ) {a x y : ℝ} (ha : 2 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y)
  (hc : 0 < x + y) :
  (x + y) ^ (a * ↑k) * ((1 + (-x / (x + y) + y / (x + y)) ^ (2 * k)) / 2) ^ (a - 1) ≤
    FractionalBinomial.binomialSum k a x y
```

```lean
FractionalBinomial.sharp_coefficient {a C : ℝ} (ha : 2 ≤ a)
  (hC : ∀ (k : ℕ) (x y : ℝ), 0 ≤ x → 0 ≤ y → (x + y) ^ (a * ↑k) ≤ C * FractionalBinomial.binomialSum k a x y) :
  2 ^ (a - 1) ≤ C
```


## 2. Nonconvergence for every finite all-odd randomized subtraction set

Checked from [build/odd-subtraction-packet-audit/odd-subtraction/build/verified/Checks.log](../build/odd-subtraction-packet-audit/odd-subtraction/build/verified/Checks.log).

```lean
OddSubtraction.all_odd_game_nonconvergence (S : Finset ℕ) (hne : S.Nonempty) (hodd : ∀ k ∈ S, k % 2 = 1) :
  ¬∃ L, Filter.Tendsto (OddSubtraction.gameWin S) Filter.atTop (nhds L)
```

```lean
OddSubtraction.all_odd_game_positive_invariant (S : Finset ℕ) (hodd : ∀ k ∈ S, k % 2 = 1) (n : ℕ) :
  ↑S.card ≤ OddSubtraction.window S (OddSubtraction.centered (OddSubtraction.gameWin S)) (n + S.sup id)
```


## 3. Exact counterexample to square-root trigonometric positivity

Checked from [build/trig-counterexample-packet-audit/trig-counterexample/build/verified/Checks.log](../build/trig-counterexample-packet-audit/trig-counterexample/build/verified/Checks.log).

```lean
KovalevCounterexample.explicit_source_counterexample :
  KovalevCounterexample.trigPartial 49 949 TrigBridge.witnessAngle < 0
```

```lean
KovalevCounterexample.conjecture_369172_false :
  ¬∀ (d n : ℕ) (t : ℝ), 2 ≤ d → 0 < KovalevCounterexample.trigPartial d n t
```


## 4. Odd-degree derivative-root mean identity

Checked from [build/odd-root-means-packet-audit/odd-root-means/build/verified/Checks.log](../build/odd-root-means-packet-audit/odd-root-means/build/verified/Checks.log).

```lean
OddRootMeans.source_conjecture_336466 (p : Polynomial ℂ) (hodd : Odd p.natDegree) :
  ∑ r ∈ Finset.Ioo 0 p.natDegree, (-1) ^ r * ↑(p.natDegree.choose r) * OddRootMeans.derivativeRootMean p r = 0
```


## 5. Four interior roots refute Yuster Conjecture3.9

Checked from [build/yuster-rootcount-packet-audit/yuster-rootcount/build/verified/Checks.log](../build/yuster-rootcount-packet-audit/yuster-rootcount/build/verified/Checks.log).

```lean
YusterCounterexample.source_rootcount_ge_four :
  4 ≤ FourRoots.interiorRootCount (YusterCounterexample.sourceP 48 YusterCounterexample.sourceAlpha48)
```

```lean
YusterCounterexample.source_conjecture_357503_false :
  ¬∀ (k : ℕ) (psi : ℝ),
      2 ≤ k →
        psi ∈ Set.Icc 0 1 →
          (1 - psi) ^ k = psi → FourRoots.interiorRootCount (YusterCounterexample.sourceP k ((1 - psi) ^ (k - 1))) ≤ 2
```


## 6. Arbitrary-rank negative-order Vendi–LCR comparison

Checked from [build/vendi-negative-packet-audit/vendi-negative/build/verified/Checks.log](../build/vendi-negative-packet-audit/vendi-negative/build/verified/Checks.log).

```lean
VendiScores.source_conjecture_negative.{u_1} {I : Type u_1} [Fintype I] [DecidableEq I] [Nonempty I] (Z : Matrix I I ℝ)
  (hZ : Z.PosSemidef) (hdiag : ∀ (i : I), Z i i = 1) (hentry : ∀ (i j : I), 0 ≤ Z i j ∧ Z i j ≤ 1) (q : ℝ)
  (hq : q < 0) : VendiScores.lcrScore Z q ≤ VendiScores.vendiScore hZ q
```

```lean
VendiScores.source_conjecture_negativeInfinity.{u_1} {I : Type u_1} [Fintype I] [DecidableEq I] [Nonempty I]
  (Z : Matrix I I ℝ) (hZ : Z.PosSemidef) (hdiag : ∀ (i : I), Z i i = 1) (hentry : ∀ (i j : I), 0 ≤ Z i j ∧ Z i j ≤ 1) :
  VendiScores.negativeInfinityLcr Z ≤ VendiScores.negativeInfinityVendi hZ hdiag
```

```lean
VendiMatrix.source_spectral_energy_bound.{u_1} {n : Type u_1} [Fintype n] [DecidableEq n] (Z : Matrix n n ℝ)
  (hZ : Z.PosSemidef) (hdiag : ∀ (i : n), Z i i = 1) (q : ℝ) (hq : q < 1) :
  ∑ i, (Z * Z) i i ^ (q - 1) ≤ ∑ j ∈ VendiMatrix.positiveSpectrum hZ, ⋯.eigenvalues j ^ q
```


## 7. Full unit-circle nonvanishing and root allocation for rational Hartogs-triangle polynomials

Checked from [build/bergman-unit-circle-packet-audit/bergman-unit-circle/build/verified/Checks.log](../build/bergman-unit-circle-packet-audit/bergman-unit-circle/build/verified/Checks.log).

```lean
BergmanUnitCircle.source_full_conjecture_368572 {m n : ℕ} (hn : 0 < n) (hmn : n < m) (hcop : m.Coprime n) :
  (∀ (z : ℂ), ‖z‖ = 1 → Polynomial.eval z (BergmanUnitCircle.polynomialQ m n) ≠ 0) ∧
    (Multiset.filter (fun z => z ≠ 0 ∧ ‖z‖ < 1) (BergmanUnitCircle.polynomialQ m n).roots).card = m - n
```

```lean
BergmanUnitCircle.source_root_allocation {m n : ℕ} (hn : 0 < n) (hmn : n < m) (hcop : m.Coprime n) :
  (Multiset.filter (fun z => z ≠ 0 ∧ ‖z‖ < 1) (BergmanUnitCircle.polynomialQ m n).roots).card = m - n
```

```lean
BergmanUnitCircle.source_conjecture_368572 {m n : ℕ} (hn : 0 < n) (hmn : n < m) (hcop : m.Coprime n) {z : ℂ}
  (hz : ‖z‖ = 1) : BergmanUnitCircle.sourceQ m n z ≠ 0
```

```lean
BergmanUnitCircle.sourceQ_sos {m n : ℕ} (hn : 0 < n) (hmn : n < m) {z : ℂ} (hz : ‖z‖ = 1) :
  BergmanUnitCircle.sourceQ m n z = z ^ (m - n) * ↑(BergmanUnitCircle.gram m n z)
```


## 8. Complete real-exponent classification for both four-classical-mean comparison directions

Checked from [build/classical-means-packet-audit-final/classical-means/build/verified/Checks.log](../build/classical-means-packet-audit-final/classical-means/build/verified/Checks.log).

```lean
ClassicalMeanRange.source_full_classification (n : ℝ) :
  (ClassicalMeanRange.UniversallyValid n ↔ n ≤ 0 ∨ 1 ≤ n) ∧ (ClassicalMeanRange.ConverseUniversallyValid n ↔ n = 0)
```

```lean
ClassicalMeanRange.source_exponent_classification (n : ℝ) : ClassicalMeanRange.UniversallyValid n ↔ n ≤ 0 ∨ 1 ≤ n
```

```lean
ClassicalMeanRange.source_converse_exponent_classification (n : ℝ) :
  ClassicalMeanRange.ConverseUniversallyValid n ↔ n = 0
```

```lean
ClassicalMeanRange.source_failure_all_intermediate {n : ℝ} (hn0 : 0 < n) (hn1 : n < 1) :
  ∃ x y, 0 < x ∧ 0 < y ∧ ¬ClassicalMeanRange.SourceComparison n x y
```

```lean
ClassicalMeanRange.explicit_half_power_failure : ¬ClassicalMeanRange.SourceComparison (1 / 2) (4 + √15) (4 - √15)
```


## 9. Strict-valley refutation of Keith’s three-color linear-cut conjecture

Checked from [build/keith-multicolor-packet-audit/keith-multicolor/build/verified/Checks.log](../build/keith-multicolor-packet-audit/keith-multicolor/build/verified/Checks.log).

```lean
KeithMulticolor.source_full_counterexample_345259 :
  ¬KeithMulticolor.Unimodal fun x => ((KeithMulticolor.sourcePolynomial 25 325).coeff ↑x).coeff (45 - 2 * ↑x)
```

```lean
KeithMulticolor.source_polynomial_strict_valley :
  ((KeithMulticolor.sourcePolynomial 25 325).coeff 21).coeff 3 <
      ((KeithMulticolor.sourcePolynomial 25 325).coeff 20).coeff 5 ∧
    ((KeithMulticolor.sourcePolynomial 25 325).coeff 21).coeff 3 <
      ((KeithMulticolor.sourcePolynomial 25 325).coeff 22).coeff 1
```

```lean
KeithMulticolor.sourcePolynomial_coefficient (N n i j : ℕ) :
  ((KeithMulticolor.sourcePolynomial N n).coeff i).coeff j = KeithMulticolor.sourceArray N n i j
```

```lean
KeithMulticolor.sourceArray_first : KeithMulticolor.sourceArray 25 325 20 5 = 53130
```

```lean
KeithMulticolor.sourceArray_middle : KeithMulticolor.sourceArray 25 325 21 3 = 50600
```

```lean
KeithMulticolor.sourceArray_third_lower : 52900 ≤ KeithMulticolor.sourceArray 25 325 22 1
```


## 10. Hermitian finite-matrix refutation of C*-algebraic Novak positivity

Checked from [build/cstar-novak-packet-audit/cstar-novak/build/verified/Checks.log](../build/cstar-novak-packet-audit/cstar-novak/build/verified/Checks.log).

```lean
Novak.source_counterexample_351633 :
  (∀ (i : Fin 4) (l : Fin 2), Matrix.IsHermitian (Novak.inputs i l)) ∧
    (Novak.sourceMatrix Novak.inputs).IsHermitian ∧ ¬(Novak.sourceMatrix Novak.inputs).PosSemidef
```

```lean
Novak.quadratic_form : star Novak.witness ⬝ᵥ (Novak.sourceMatrix Novak.inputs).mulVec Novak.witness = ↑(Novak.c - 3)
```

```lean
Novak.source_hermitian : (Novak.sourceMatrix Novak.inputs).IsHermitian
```


## 11. One cubic refutation of three C*-algebraic polynomial moment conjectures

Checked from [build/cstar-polynomial-packet-audit-v2/cstar-polynomial/build/verified/Checks.log](../build/cstar-polynomial-packet-audit-v2/cstar-polynomial/build/verified/Checks.log).

```lean
CstarPolynomial.source_all_three_conjectures_false :
  ∑ i, CstarPolynomial.roots i = 0 ∧
    (∀ (i : Fin 3), CstarPolynomial.cubic CstarPolynomial.roots (CstarPolynomial.roots i) = 0) ∧
      (∀ (z : CstarPolynomial.M₂),
          CstarPolynomial.sourceDerivative CstarPolynomial.roots z =
            3 • ((z - CstarPolynomial.critical 0) * (z - CstarPolynomial.critical 1))) ∧
        (∀ (i : Fin 2), CstarPolynomial.sourceDerivative CstarPolynomial.roots (CstarPolynomial.critical i) = 0) ∧
          ∀ (k : Fin 6), Matrix.IsHermitian (CstarPolynomial.defects k) ∧ ¬Matrix.PosSemidef (CstarPolynomial.defects k)
```

```lean
CstarPolynomial.source_counterexample_355008_355009 :
  ∑ i, CstarPolynomial.roots i = 0 ∧
    (∀ (z : CstarPolynomial.M₂),
        CstarPolynomial.sourceDerivative CstarPolynomial.roots z =
          3 • ((z - CstarPolynomial.critical 0) * (z - CstarPolynomial.critical 1))) ∧
      ¬Matrix.PosSemidef (CstarPolynomial.schoenbergLeft CstarPolynomial.roots CstarPolynomial.critical) ∧
        ¬Matrix.PosSemidef (CstarPolynomial.schoenbergRight CstarPolynomial.roots CstarPolynomial.critical) ∧
          ¬Matrix.PosSemidef (CstarPolynomial.deBruinLeft CstarPolynomial.roots CstarPolynomial.critical) ∧
            ¬Matrix.PosSemidef (CstarPolynomial.deBruinRight CstarPolynomial.roots CstarPolynomial.critical)
```

```lean
CstarPolynomial.derivative_factorization (z : CstarPolynomial.M₂) :
  CstarPolynomial.sourceDerivative CstarPolynomial.roots z =
    3 • ((z - CstarPolynomial.critical 0) * (z - CstarPolynomial.critical 1))
```

```lean
CstarPolynomial.defect_matrices :
  CstarPolynomial.defects =
    ![!![8, -4; -4, 0], !![0, 4; 4, 8], !![56, -24; -24, 8], !![8, 24; 24, 56], !![-392, 168; 168, -56],
      !![-56, -168; -168, -392]]
```


## 12. Sharp maximal index for separately sorted arithmetic and geometric means in every dimension at least five

Checked from [build/maximal-index-packet-audit-v1/maximal-index/build/verified/Checks.log](../build/maximal-index-packet-audit-v1/maximal-index/build/verified/Checks.log).

```lean
MaxIndex.source_index_classification (d : ℕ) (hd : 5 ≤ d) (k : ℕ) (hk : k ≤ d * d) :
  (∀ (p : Fin d → ℝ),
      (∀ (i : Fin d), 0 ≤ p i) →
        ∑ i, p i = 1 →
          MaxIndex.sortedTopSum (MaxIndex.arithmeticEntry p) k + MaxIndex.sortedTopSum (MaxIndex.geometricEntry p) k ≤
            ↑d) ↔
    k ≤ 2 * d - 5
```

```lean
MaxIndex.source_next_index_counterexample (d : ℕ) (hd : 5 ≤ d) :
  ∃ p,
    (∀ (i : Fin d), 0 ≤ p i) ∧
      ∑ i, p i = 1 ∧
        ↑d <
          MaxIndex.sortedTopSum (MaxIndex.arithmeticEntry p) (2 * d - 4) +
            MaxIndex.sortedTopSum (MaxIndex.geometricEntry p) (2 * d - 4)
```

```lean
MaxIndex.source_universal_index (d : ℕ) (hd : 3 ≤ d) (p : Fin d → ℝ) (hp : ∀ (i : Fin d), 0 ≤ p i)
  (hsum : ∑ i, p i = 1) :
  MaxIndex.sortedTopSum (MaxIndex.arithmeticEntry p) (2 * d - 5) +
      MaxIndex.sortedTopSum (MaxIndex.geometricEntry p) (2 * d - 5) <
    ↑d
```


## 13. Positive diagonal concavity does not imply concavity for elementary-symmetric sums

Checked from [build/lachaume-quartic-packet-audit-v2/lachaume-quartic/build/verified/Checks.log](../build/lachaume-quartic-packet-audit-v2/lachaume-quartic/build/verified/Checks.log).

```lean
Lachaume.source_nonreal_root_counterexample :
  Lachaume.quarticPoly.natDegree = 4 ∧
    (∀ (i : ℕ), 0 ≤ Lachaume.quarticPoly.coeff i) ∧
      (∀ (x : ℝ),
          Polynomial.eval x Lachaume.quarticPoly *
                Polynomial.eval x (Polynomial.derivative (Polynomial.derivative Lachaume.quarticPoly)) +
              (1 / ↑Lachaume.quarticPoly.natDegree - 1) *
                Polynomial.eval x (Polynomial.derivative Lachaume.quarticPoly) ^ 2 ≤
            0) ∧
        ∃ z, (Polynomial.map (algebraMap ℝ ℂ) Lachaume.quarticPoly).IsRoot z ∧ z.im ≠ 0
```

```lean
Lachaume.source_diagonal_concavity_counterexample :
  (∀ (k : Fin 5), 0 < Lachaume.sourceCoefficient k) ∧
    (∀ v ∈ Lachaume.positiveOrthant, 0 < Lachaume.sourceFunction v) ∧
      ContDiffOn ℝ 2 (fun v => Lachaume.sourceFunction v ^ (1 / 4)) Lachaume.positiveOrthant ∧
        (ConcaveOn ℝ (Set.Ioi 0) fun x => (Lachaume.sourceFunction fun x_1 => x) ^ (1 / 4)) ∧
          ¬ConcaveOn ℝ Lachaume.positiveOrthant fun v => Lachaume.sourceFunction v ^ (1 / 4)
```


## 14. Sharp universal constants for the3x3permanental Koteljanskii ratio

Checked from [build/permanental3-packet-audit-v3/permanental3/build/verified/Checks.log](../build/permanental3-packet-audit-v3/permanental3/build/verified/Checks.log).

```lean
PermanentalThree.strictTP3_iff_allMinors (A : PermanentalThree.Mat3) :
  PermanentalThree.StrictTP3 A ↔ PermanentalThree.AllMinorsPositive A
```

```lean
PermanentalThree.source_sharp_permanental_bounds :
  (∀ (A : PermanentalThree.Mat3),
      PermanentalThree.AllMinorsPositive A →
        2 / 3 < PermanentalThree.sourceRatio A ∧ PermanentalThree.sourceRatio A < 9 / 8) ∧
    (∀ (c : ℝ),
        (∀ (A : PermanentalThree.Mat3), PermanentalThree.AllMinorsPositive A → c ≤ PermanentalThree.sourceRatio A) ↔
          c ≤ 2 / 3) ∧
      ∀ (c : ℝ),
        (∀ (A : PermanentalThree.Mat3), PermanentalThree.AllMinorsPositive A → PermanentalThree.sourceRatio A ≤ c) ↔
          9 / 8 ≤ c
```


## 15. Strict connection–Dirac spectral dominance for every finite graph

Checked from [build/connection-graph-packet-audit-v1/connection-graph/build/verified/Checks.log](../build/connection-graph-packet-audit-v1/connection-graph/build/verified/Checks.log).

```lean
ConnectionGraph.graph_low_connection_bound.{u_2} {V : Type u_2} [Fintype V] [LinearOrder V] {E : Finset (V × V)}
  (hE : ConnectionGraph.ValidEdges E) (hne : E.Nonempty) {k : ℕ} (hk0 : 0 < k) (hk : k ≤ Fintype.card V) :
  ↑k + ConnectionGraph.sortedTopSum (ConnectionGraph.degree E) k / 2 + (√2 - 1) ≤ ConnectionGraph.spectralTopSum ⋯ k
```

```lean
ConnectionGraph.graph_high_connection_bound.{u_3} {V : Type u_3} [Fintype V] [LinearOrder V] [Nonempty V]
  {E : Finset (V × V)} (hE : ConnectionGraph.ValidEdges E) {k : ℕ} (hv : Fintype.card V ≤ k)
  (hk : k ≤ Fintype.card V + E.card) : ↑E.card + ↑(Fintype.card V) / 2 + 1 / 2 ≤ ConnectionGraph.spectralTopSum ⋯ k
```

```lean
ConnectionGraph.empty_graph_strict_gap.{u_1} {V : Type u_1} [Fintype V] [LinearOrder V] {E : Finset (V × V)}
  (hE : E = ∅) {k : ℕ} (hk0 : 0 < k) (hk : k ≤ Fintype.card V + E.card) :
  √2 - 1 ≤ ConnectionGraph.spectralTopSum ⋯ k - ConnectionGraph.spectralTopSum ⋯ k
```

```lean
ConnectionGraph.simplex_injective.{u_1} {V : Type u_1} [LinearOrder V] {E : Finset (V × V)}
  (hE : ConnectionGraph.ValidEdges E) : Function.Injective (ConnectionGraph.simplex E)
```

```lean
ConnectionGraph.graphFaces_closed.{u_1} {V : Type u_1} [Fintype V] [LinearOrder V] (E : Finset (V × V)) {s t : Finset V}
  (hs : s ∈ ConnectionGraph.graphFaces E) (ht : t.Nonempty) (hts : t ⊆ s) : t ∈ ConnectionGraph.graphFaces E
```

```lean
ConnectionGraph.face_connection_spectral_sum.{u_1} {V : Type u_1} [Fintype V] [LinearOrder V] {E : Finset (V × V)}
  (hE : ConnectionGraph.ValidEdges E) (k : ℕ) : ConnectionGraph.spectralTopSum ⋯ k = ConnectionGraph.spectralTopSum ⋯ k
```

```lean
ConnectionGraph.face_dirac_spectral_sum.{u_1} {V : Type u_1} [Fintype V] [LinearOrder V] {E : Finset (V × V)}
  (hE : ConnectionGraph.ValidEdges E) (k : ℕ) : ConnectionGraph.spectralTopSum ⋯ k = ConnectionGraph.spectralTopSum ⋯ k
```

```lean
ConnectionGraph.complex_connection_spectral_sum.{u_1} {V : Type u_1} [Fintype V] [LinearOrder V] (F : Finset (Finset V))
  (hsingle : ∀ (v : V), {v} ∈ F) (hcard : ∀ s ∈ F, s.card = 1 ∨ s.card = 2) (k : ℕ) :
  ConnectionGraph.spectralTopSum ⋯ k = ConnectionGraph.spectralTopSum ⋯ k
```

```lean
ConnectionGraph.complex_dirac_spectral_sum.{u_1} {V : Type u_1} [Fintype V] [LinearOrder V] (F : Finset (Finset V))
  (hsingle : ∀ (v : V), {v} ∈ F) (hcard : ∀ s ∈ F, s.card = 1 ∨ s.card = 2) (k : ℕ) :
  ConnectionGraph.spectralTopSum ⋯ k = ConnectionGraph.spectralTopSum ⋯ k
```

```lean
ConnectionGraph.restricted_connection_spectral_sum.{u_1} {X : Type u_1} [LinearOrder X] (F : Finset (Finset X))
  (k : ℕ) : ConnectionGraph.spectralTopSum ⋯ k = ConnectionGraph.spectralTopSum ⋯ k
```

```lean
ConnectionGraph.restricted_dirac_spectral_sum.{u_1} {X : Type u_1} [LinearOrder X] [Fintype X] (F : Finset (Finset X))
  (k : ℕ) : ConnectionGraph.spectralTopSum ⋯ k = ConnectionGraph.spectralTopSum ⋯ k
```

```lean
ConnectionGraph.restrictedFamily_singletons.{u_1} {X : Type u_1} [LinearOrder X] (F : Finset (Finset X))
  (hclosed : ∀ s ∈ F, ∀ t ⊆ s, t.Nonempty → t ∈ F) (v : ↥(ConnectionGraph.supportVertices F)) :
  {v} ∈ ConnectionGraph.restrictedFamily F
```

```lean
ConnectionGraph.dirac_spectral_top_sum_le_sqrt.{u_4} {V : Type u_4} [Fintype V] [LinearOrder V] (E : Finset (V × V))
  {k : ℕ} (hk : k ≤ Fintype.card V) :
  ConnectionGraph.spectralTopSum ⋯ k ≤ √(2 * ↑k * ConnectionGraph.sortedTopSum (ConnectionGraph.degree E) k)
```

```lean
ConnectionGraph.dirac_spectral_top_sum_le_global.{u_4} {V : Type u_4} [Fintype V] [LinearOrder V] (E : Finset (V × V))
  (hE : ConnectionGraph.ValidEdges E) {k : ℕ} (hk : k ≤ Fintype.card (V ⊕ ↥E)) :
  ConnectionGraph.spectralTopSum ⋯ k ≤ ↑E.card + ↑(Fintype.card V) / 2
```

```lean
ConnectionGraph.source_graph_strict_gap.{u_1} {V : Type u_1} [Fintype V] [LinearOrder V] (F : Finset (Finset V))
  (hF : F.Nonempty) (hclosed : ∀ s ∈ F, ∀ t ⊆ s, t.Nonempty → t ∈ F) (hcard : ∀ s ∈ F, s.card = 1 ∨ s.card = 2) {k : ℕ}
  (hk0 : 0 < k) (hk : k ≤ F.card) : √2 - 1 ≤ ConnectionGraph.spectralTopSum ⋯ k - ConnectionGraph.spectralTopSum ⋯ k
```

```lean
ConnectionGraph.source_graph_spectral_dominance.{u_1} {V : Type u_1} [Fintype V] [LinearOrder V] (F : Finset (Finset V))
  (hF : F.Nonempty) (hclosed : ∀ s ∈ F, ∀ t ⊆ s, t.Nonempty → t ∈ F) (hcard : ∀ s ∈ F, s.card = 1 ∨ s.card = 2) {k : ℕ}
  (hk0 : 0 < k) (hk : k ≤ F.card) : ConnectionGraph.spectralTopSum ⋯ k < ConnectionGraph.spectralTopSum ⋯ k
```


## 16. A continuous critical-branch obstruction to C*-algebraic Sendov conjectures

Checked from [build/cstar-sendov-packet-audit-v2/cstar-sendov/build/verified/Checks.log](../build/cstar-sendov-packet-audit-v2/cstar-sendov/build/verified/Checks.log).

```lean
CStarSendov.source_critical_classification (z : CStarSendov.FunctionAlgebra) (hz : CStarSendov.sourceDeleted z = 0) :
  z = CStarSendov.criticalPlusMap ∨ z = CStarSendov.criticalMinusMap
```

```lean
CStarSendov.source_critical_strict_real_weights (z : CStarSendov.FunctionAlgebra)
  (hz : CStarSendov.sourceDeleted z = 0) :
  ∃ w,
    (∀ (j : Fin 3) (t : ↑CStarSendov.Time), 0 < (w j) t) ∧
      (∀ (t : ↑CStarSendov.Time), ∑ j, (w j) t = 1) ∧
        ∀ (t : ↑CStarSendov.Time), z t = ∑ j, ↑((w j) t) * (CStarSendov.roots j) t
```

```lean
CStarSendov.source_critical_positive_convex (z : CStarSendov.FunctionAlgebra) (hz : CStarSendov.sourceDeleted z = 0) :
  CStarSendov.sourcePositiveConvex CStarSendov.roots z
```

```lean
CStarSendov.source_all_critical_distance_gt (z : CStarSendov.FunctionAlgebra)
  (hz : CStarSendov.sourceCubicDeleted CStarSendov.roots z = 0) : 21 / 20 < ‖CStarSendov.roots 0 - z‖
```

```lean
CStarSendov.source_counterexample_353909 : ¬CStarSendov.sourceCubicConjecture353909
```

```lean
CStarSendov.source_counterexample_published_conjecture4 : ¬CStarSendov.sourceSplitCubicConjecture4
```

```lean
CStarSendov.source_complete_counterexample :
  CStarSendov.sourcePolynomial.Monic ∧
    CStarSendov.sourcePolynomial.natDegree = 3 ∧
      (∀ (j : Fin 3), ‖CStarSendov.roots j‖ ≤ 9 / 10) ∧
        (∀ (k : Fin 2), ‖CStarSendov.criticals k‖ < 9 / 10) ∧
          (∀ (k : Fin 2), CStarSendov.sourcePositiveConvex CStarSendov.roots (CStarSendov.criticals k)) ∧
            (∀ (t : ↑CStarSendov.Time), Function.Injective fun k => (CStarSendov.criticals k) t) ∧
              Polynomial.derivative CStarSendov.sourcePolynomial =
                  Polynomial.C 3 * (Polynomial.X - Polynomial.C (CStarSendov.criticals 0)) *
                    (Polynomial.X - Polynomial.C (CStarSendov.criticals 1)) ∧
                (∀ (z : CStarSendov.FunctionAlgebra),
                    CStarSendov.sourceCubicDeleted CStarSendov.roots z = 0 → 21 / 20 < ‖CStarSendov.roots 0 - z‖) ∧
                  ¬CStarSendov.sourceCubicConjecture353909 ∧ ¬CStarSendov.sourceSplitCubicConjecture4
```


## 17. Odd-total lower bound for simple SOC representations

Checked from [build/wgm-parity-packet-audit-v1/wgm-parity/build/verified/Checks.log](../build/wgm-parity-packet-audit-v1/wgm-parity/build/verified/Checks.log).

```lean
WGMParity.source_odd_total_bound (m n : ℕ) (s : Fin m → ℕ) (hs : ∀ (j : Fin m), 0 < s j) (root : Fin n)
  (child : Fin n × Bool → Fin m ⊕ Fin n) (h : WGMParity.SourceRepresentation s root child) (hodd : Odd (∑ j, s j)) :
  m ≤ n
```

```lean
WGMParity.odd_total_sound_size_bound.{u_1, u_2} {L : Type u_1} {I : Type u_2} [Fintype L] [Fintype I] (s : L → ℕ)
  (hs : ∀ (j : L), 0 < s j) (root : I) (child : I × Bool → L ⊕ I) (h : WGMParity.CircuitSound s root child)
  (hodd : Odd (∑ j, s j)) : Fintype.card L ≤ Fintype.card I
```

```lean
WGMParity.equality_size_forces_even.{u_1, u_2} {L : Type u_1} {I : Type u_2} [Fintype L] [Fintype I] (s : L → ℕ)
  (hs : ∀ (j : L), 0 < s j) (root : I) (child : I × Bool → L ⊕ I) (h : WGMParity.CircuitSound s root child)
  (hsize : Fintype.card I + 1 = Fintype.card L) : Even (∑ j, s j)
```


## 18. A fortieth-derivative obstruction to the Mills-ratio complete-monotonicity conjecture

Checked from [build/mills-cm-packet-audit-v1/mills-cm/build/verified/Checks.log](../build/mills-cm-packet-audit-v1/mills-cm/build/verified/Checks.log).

```lean
MillsCounterexample.source_counterexample_351688 : ¬MillsCounterexample.SourceConjecture351688
```

```lean
MillsCounterexample.source_ratio_zero_positive_interval :
  ∃ δ, 0 < δ ∧ ∀ x ∈ Set.Ioo 0 δ, iteratedDeriv 40 (MillsCounterexample.sourceRatio 0) x < 0
```

```lean
MillsCounterexample.regular_positive_interval_counterexample :
  ∃ δ,
    0 < δ ∧
      ∀ x ∈ Set.Ioo 0 δ, deriv MillsCounterexample.mills x < 0 ∧ iteratedDeriv 40 MillsCounterexample.quotient x < 0
```

```lean
MillsCounterexample.quotient_derivative40_negative : iteratedDeriv 40 MillsCounterexample.quotient 0 < 0
```


## 19. All-order smooth realization of increasing repeated-integral endpoint jets

Checked from [build/repeated-integrals-packet-audit-v1/repeated-integrals/build/verified/Checks.log](../build/repeated-integrals-packet-audit-v1/repeated-integrals/build/verified/Checks.log).

```lean
RepeatedIntegrals.source_measure_exists {n : ℕ} {b : RepeatedIntegrals.MomentSpace n}
  (hb : b ∈ RepeatedIntegrals.SourceW n) : Nonempty (RepeatedIntegrals.SourceMeasure n b)
```

```lean
RepeatedIntegrals.endpointMomentTransform_density (n : ℕ) {ρ : ℝ → ℝ} (hρ : Continuous ρ) (j : Fin (n + 1)) :
  (RepeatedIntegrals.endpointMomentTransform n) (RepeatedIntegrals.densityMoments n ρ) j =
    (∫ (t : ℝ) in 0..1, (1 - t) ^ (n - ↑j) * ρ t) / ↑(n - ↑j).factorial
```

```lean
RepeatedIntegrals.repeatedPrimitive_goodWitness (n : ℕ) {ρ : ℝ → ℝ} (hρ : RepeatedIntegrals.GoodDensity ρ) :
  RepeatedIntegrals.GoodWitness n ((RepeatedIntegrals.endpointMomentTransform n) (RepeatedIntegrals.densityMoments n ρ))
    (RepeatedIntegrals.repeatedPrimitive (n + 1) ρ)
```

```lean
RepeatedIntegrals.zero_mem_closure_smoothMomentSet (n : ℕ) : 0 ∈ closure (RepeatedIntegrals.smoothMomentSet n)
```

```lean
RepeatedIntegrals.atomless_moment_strict_positive {n : ℕ} (a : RepeatedIntegrals.MomentSpace n) (ha : a ≠ 0)
  {μ : MeasureTheory.Measure ℝ} [MeasureTheory.IsFiniteMeasure μ] [MeasureTheory.NullSingletonClass μ]
  (hs : μ (Set.Icc 0 1)ᶜ = 0) (hm : 0 < μ.real Set.univ)
  (hn : ∀ t ∈ Set.Icc 0 1, 0 ≤ RepeatedIntegrals.momentPairing a (RepeatedIntegrals.momentCurve n t)) :
  0 < RepeatedIntegrals.momentPairing a (RepeatedIntegrals.measureMoments n μ)
```

```lean
RepeatedIntegrals.atomless_measure_mem_smoothMomentSet {n : ℕ} (hc : Convex ℝ (RepeatedIntegrals.smoothMomentSet n))
  (ho : IsOpen (RepeatedIntegrals.smoothMomentSet n)) {μ : MeasureTheory.Measure ℝ} [MeasureTheory.IsFiniteMeasure μ]
  [MeasureTheory.NullSingletonClass μ] (hs : μ (Set.Icc 0 1)ᶜ = 0) (hm : 0 < μ.real Set.univ) :
  RepeatedIntegrals.measureMoments n μ ∈ RepeatedIntegrals.smoothMomentSet n
```

```lean
RepeatedIntegrals.sourceW_eq_smoothMomentImage (n : ℕ) (hc : Convex ℝ (RepeatedIntegrals.smoothMomentSet n))
  (ho : IsOpen (RepeatedIntegrals.smoothMomentSet n)) :
  RepeatedIntegrals.SourceW n = ⇑(RepeatedIntegrals.endpointMomentTransform n) '' RepeatedIntegrals.smoothMomentSet n
```

```lean
RepeatedIntegrals.source_conjecture_of_moment_openness (hc : ∀ (n : ℕ), Convex ℝ (RepeatedIntegrals.smoothMomentSet n))
  (ho : ∀ (n : ℕ), IsOpen (RepeatedIntegrals.smoothMomentSet n)) : RepeatedIntegrals.SourceConjecture371768
```

```lean
RepeatedIntegrals.smoothMomentSet_convex (n : ℕ) : Convex ℝ (RepeatedIntegrals.smoothMomentSet n)
```

```lean
RepeatedIntegrals.smoothMomentSet_isOpen (n : ℕ) : IsOpen (RepeatedIntegrals.smoothMomentSet n)
```

```lean
RepeatedIntegrals.source_moment_image (n : ℕ) :
  RepeatedIntegrals.SourceW n = ⇑(RepeatedIntegrals.endpointMomentTransform n) '' RepeatedIntegrals.smoothMomentSet n
```

```lean
RepeatedIntegrals.source_conjecture_371768 : RepeatedIntegrals.SourceConjecture371768
```


## 20. Davis all-degree rational-function conjecture via a fourth-moment bound

Checked from [build/davis-packet-audit-v1/davis/build/verified/Checks.log](../build/davis-packet-audit-v1/davis/build/verified/Checks.log).

```lean
Davis.raw_moment_identity (d : ℕ) (x : ℝ) :
  2 * ∑ i ∈ Finset.range (d + 1), Davis.weight d i x * (↑i - ↑d / 2) ^ 4 +
      Davis.momentCoefficient (↑d) (x - ↑d / 2) * ∑ i ∈ Finset.range (d + 1), Davis.weight d i x * (↑i - ↑d / 2) ^ 2 =
    ↑d / 2 * (x - ↑d / 2) ^ 2 * Davis.P d x
```

```lean
Davis.moment_identity {d : ℕ} {x : ℝ} (hx : ↑d / 2 < x) :
  2 * Davis.centralMoment d x 4 + Davis.momentCoefficient (↑d) (x - ↑d / 2) * Davis.centralMoment d x 2 =
    ↑d / 2 * (x - ↑d / 2) ^ 2
```

```lean
Davis.remainder_ratio_moment {d : ℕ} {x : ℝ} (hx : ↑d / 2 < x) :
  -Davis.remainder d x / Davis.P d x = (↑d - 4 * Davis.centralMoment d x 2) / (2 * (↑d + 1))
```

```lean
Davis.source_tail {d : ℕ} {x : ℝ} (hd : 43 ≤ d) (hx : (↑d + √(↑d + 2)) / 2 ≤ x) :
  199 / 200 * (↑d - 2) / (2 * x + ↑d - 2) < -Davis.remainder d x / Davis.P d x
```

```lean
Davis.coeffEval_inequality (d : ℕ) (x : ℝ) :
  Davis.coeffEval (Davis.inequalityCoeffs d) x =
    400 * (↑d + 1) * ↑d.factorial *
      (((2 * x + ↑d - 2) * Davis.quotient d x - 199 / 200 * (↑d - 2)) * Davis.P d x -
        (2 * x + ↑d - 2) * Davis.P (d + 1) x)
```

```lean
Davis.certificate_implies_positive {d : ℕ} {x : ℝ} (hc : Davis.certificateCheck d = true)
  (hx : (↑d + √(↑d + 2)) / 2 ≤ x) : 0 < Davis.coeffEval (Davis.inequalityCoeffs d) x
```

```lean
Davis.small_certificates {d : ℕ} (hlo : 5 ≤ d) (hhi : d ≤ 42) : Davis.certificateCheck d = true
```

```lean
Davis.source_strict_bound {d : ℕ} {x : ℝ} (hd : 5 ≤ d) (hx : (↑d + √(↑d + 2)) / 2 ≤ x) :
  199 / 200 * (↑d - 2) / (2 * x + ↑d - 2) < -Davis.remainder d x / Davis.P d x
```

```lean
Davis.source_conjecture_319187 : Davis.SourceConjecture319187
```


## 21. Uniform Burnside-Gautschi bound for interpolated gamma values

Checked from [build/schmidlin-packet-audit-v1/schmidlin/build/verified/Checks.log](../build/schmidlin-packet-audit-v1/schmidlin/build/verified/Checks.log).

```lean
Schmidlin.gammaError_le_stirlingUpper {z : ℝ} (hz : 0 < z) : Schmidlin.gammaError z ≤ Schmidlin.stirlingUpper z
```

```lean
Schmidlin.source_strict_bound {x alpha : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ alpha) :
  Schmidlin.sourceError x alpha < 1 / (12 * (x + alpha) + 18 - 12 * Real.exp (1 / 48))
```

```lean
Schmidlin.source_conjecture_372858 : Schmidlin.SourceConjecture372858
```


## 22. All-order adjacent-count inequality for the flat Bernoulli game

Checked from [build/hetyei-packet-audit-v1/hetyei/build/verified/Checks.log](../build/hetyei-packet-audit-v1/hetyei/build/verified/Checks.log).

```lean
FlatBernoulli.source_K_tail (n : ℕ) (hn : 11 ≤ n) : FlatBernoulli.sourceK n < ↑n * FlatBernoulli.sourceK (n - 1)
```

```lean
FlatBernoulli.source_conjecture_319292 (n : ℕ) (hn : 12 ≤ n) :
  FlatBernoulli.sourceKappa n < ↑n * FlatBernoulli.sourceKappa (n - 1)
```


## 23. Convexity of the literal Le Roy parameter threshold

Checked from [build/simon-threshold-packet-audit-v1/simon-threshold/build/verified/Checks.log](../build/simon-threshold-packet-audit-v1/simon-threshold/build/verified/Checks.log).

```lean
SimonThreshold.source_threshold_convex {γ : ℝ} (hγ : 1 < γ) :
  ConvexOn ℝ (Set.Ioo 0 (1 / γ)) (SimonThreshold.sourceThreshold γ)
```


## 24. Full alternating Turan inequality for normalized Euler numbers

Checked from [build/euler-turan-packet-audit-v1/euler-turan/build/verified/Checks.log](../build/euler-turan-packet-audit-v1/euler-turan/build/verified/Checks.log).

```lean
EulerTuran.source_conjecture_338918 (n j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
  0 <
    (-1) ^ (n + 1) *
      (EulerTuran.normalizedEuler n * EulerTuran.normalizedEuler (n + j + k) -
        EulerTuran.normalizedEuler (n + j) * EulerTuran.normalizedEuler (n + k))
```


## 25. Strictly interior refutation of the DeTemple CM threshold

Checked from [build/detemple-packet-audit-v1/detemple/build/verified/Checks.log](../build/detemple-packet-audit-v1/detemple/build/verified/Checks.log).

```lean
DeTemple.source_counterexample_328867ii : ¬DeTemple.SourceConjecture328867ii
```

```lean
DeTemple.source_interior_not_completelyMonotone :
  ∃ a, 0 < a ∧ a < 155 / 294 ∧ ¬DeTemple.SourceCompletelyMonotone fun x => -DeTemple.sourceG a x
```


## 26. Full literal Hermite envelope conjecture

Checked from [build/hermite-packet-audit-v1/hermite/build/verified/Checks.log](../build/hermite-packet-audit-v1/hermite/build/verified/Checks.log).

```lean
HermiteEnvelope.source_tail_abs (n : ℕ) (hn : 3 ≤ n) (x : ℝ) (hx : HermiteEnvelope.sourceCutoff n ≤ x) :
  |HermiteEnvelope.weightedHermite n x| ≤ |HermiteEnvelope.weightedHermite n (HermiteEnvelope.sourceCutoff n)|
```

```lean
HermiteEnvelope.source_one_all_x (x : ℝ) (hx : 0 ≤ x) :
  |HermiteEnvelope.sourceHermite 1 x * Real.exp (-x ^ 2)| ≤
    HermiteEnvelope.sourceCoefficient 1 * HermiteEnvelope.sourceEnvelope 1 (min x (HermiteEnvelope.sourceCutoff 1)) *
      Real.exp (-x ^ 2 / 2)
```

```lean
HermiteEnvelope.source_even_all_x (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (hx : 0 ≤ x) :
  |HermiteEnvelope.sourceHermite (2 * m) x * Real.exp (-x ^ 2)| ≤
    HermiteEnvelope.sourceCoefficient (2 * m) *
        HermiteEnvelope.sourceEnvelope (2 * m) (min x (HermiteEnvelope.sourceCutoff (2 * m))) *
      Real.exp (-x ^ 2 / 2)
```

```lean
HermiteEnvelope.source_conjecture_of_odd_bulk
  (hb :
    ∀ (m : ℕ),
      1 ≤ m →
        ∀ (x : ℝ),
          0 ≤ x →
            x ^ 2 < 2 * ↑(2 * m + 1) + 1 →
              |HermiteEnvelope.weightedHermite (2 * m + 1) x| ≤
                HermiteEnvelope.sourceCoefficient (2 * m + 1) * HermiteEnvelope.sourceEnvelope (2 * m + 1) x) :
  HermiteEnvelope.SourceConjecture346243
```

```lean
HermiteEnvelope.preX0_sin_sq_bound (E : ℝ) (hE : 7 ≤ E) (u : ℝ) (hu : 0 ≤ u) (hu2 : u ≤ √2) :
  (1 - u ^ 2 / E ^ 2) * Real.sin (√(1 - 2 / E ^ 2) * u) ^ 2 ≤ 49 / 50 * (1 - 2 / E ^ 2)
```

```lean
HermiteEnvelope.source_odd_small_of_sine_upper (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (hx : 0 ≤ x) (hx0 : x ≤ √(2 / (4 * ↑m + 3)))
  (hy : 0 ≤ HermiteEnvelope.signedOddValue m x)
  (hupper :
    HermiteEnvelope.signedOddValue m x ≤
      HermiteEnvelope.oddSlopeMagnitude m / √(4 * ↑m + 3 - 2 / (4 * ↑m + 3)) *
        Real.sin (√(4 * ↑m + 3 - 2 / (4 * ↑m + 3)) * x)) :
  |HermiteEnvelope.weightedHermite (2 * m + 1) x| ≤
    HermiteEnvelope.sourceCoefficient (2 * m + 1) * HermiteEnvelope.sourceEnvelope (2 * m + 1) x
```

```lean
HermiteEnvelope.sine_comparison {E A : ℝ} {f g : ℝ → ℝ} (hE : 7 ≤ E) (hA : 0 < A) (hf : ∀ (t : ℝ), HasDerivAt f (g t) t)
  (hg : ∀ (t : ℝ), HasDerivAt g ((t ^ 2 - E) * f t) t) (hf0 : f 0 = 0) (hg0 : g 0 = A) (x : ℝ) :
  0 ≤ x → x ≤ √(2 / E) → A / √E * Real.sin (√E * x) ≤ f x ∧ f x ≤ A / √(E - 2 / E) * Real.sin (√(E - 2 / E) * x)
```

```lean
HermiteEnvelope.energy_loss {E A : ℝ} {f g : ℝ → ℝ} (hE : 7 ≤ E) (hA : 0 < A) (hf : ∀ (t : ℝ), HasDerivAt f (g t) t)
  (hg : ∀ (t : ℝ), HasDerivAt g ((t ^ 2 - E) * f t) t) (hf0 : f 0 = 0) (hg0 : g 0 = A) :
  HermiteEnvelope.genEnergy E f g √(2 / E) < A ^ 2 * (1 - 1 / (2 * E ^ 2))
```

```lean
HermiteEnvelope.source_odd_bulk_proved (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (hx : 0 ≤ x) (hq : x ^ 2 < 2 * ↑(2 * m + 1) + 1) :
  |HermiteEnvelope.weightedHermite (2 * m + 1) x| ≤
    HermiteEnvelope.sourceCoefficient (2 * m + 1) * HermiteEnvelope.sourceEnvelope (2 * m + 1) x
```

```lean
HermiteEnvelope.source_conjecture_346243 : HermiteEnvelope.SourceConjecture346243
```


## 27. Complete universal peakon trace-power partition coefficients

Checked from [build/peakon-coefficients-packet-audit-v1/peakon-coefficients/build/verified/Checks.log](../build/peakon-coefficients-packet-audit-v1/peakon-coefficients/build/verified/Checks.log).

```lean
PeakonCoefficients.trace_partition_universal.{u_1, u_2} {K : Type u_1} [Field K] [CharZero K] {n : Type u_2} [Fintype n]
  [DecidableEq n] [LinearOrder n] (u v : n → K) (lam xi gamma : K) (hcurve : xi ^ 2 = lam ^ 2 + gamma * lam + 1) (m : ℕ)
  (hm : 0 < m) :
  (PeakonCoefficients.algebraicLax u v lam xi ^ m).trace =
    ∑ j ∈ Finset.range m,
      ∑ p ∈ (Finset.Icc 1 m).sym (j + 1),
        if (↑p).sum = m then
          PeakonCoefficients.coefficientWeight m ↑p * lam ^ (j + 1) *
            (Multiset.map (PeakonCoefficients.rawHamiltonian u v gamma) ↑p).prod
        else 0
```

```lean
PeakonCoefficients.universalCoefficient_formula (p : Multiset ℕ) (hp : 0 < p.card) :
  PeakonCoefficients.universalCoefficient p =
    ↑p.sum * ↑(p.card - 1).factorial /
      ((Multiset.map (fun k => ↑k) p).prod * ↑(PeakonCoefficients.multiplicityDenominator p))
```

```lean
PeakonCoefficients.universalCoefficient_families :
  PeakonCoefficients.ConjecturedCoefficientFamilies PeakonCoefficients.universalCoefficient
```

```lean
PeakonCoefficients.coherent_source_expansion {N : ℕ} (r : Fin N → ℂ) (q : Fin N → ℝ) (nu z gamma : ℂ)
  (hz : 2 * z + gamma ≠ 0) (m : ℕ) (hm : 0 < m) :
  (PeakonCoefficients.sourceLax r q nu (PeakonCoefficients.spectralLambda z gamma)
          (PeakonCoefficients.spectralXi z gamma) ^
        m).trace =
    ∑ j ∈ Finset.range m,
      ∑ k ∈ (Finset.Icc 1 m).sym (j + 1),
        if (↑k).sum = m then
          PeakonCoefficients.universalCoefficient ↑k * PeakonCoefficients.spectralLambda z gamma ^ (j + 1) *
            (Multiset.map (PeakonCoefficients.sourceHamiltonian r q nu gamma) ↑k).prod
        else 0
```

```lean
PeakonCoefficients.nonnegative_source_conjecture_372008 : PeakonCoefficients.NonnegativeSourceConjecture372008
```

```lean
PeakonCoefficients.source_conjecture_372008 : PeakonCoefficients.SourceConjecture372008
```


## 28. No finite C*-Smale norm mean-value constant at fixed degree three

Checked from [build/cstar-smale-unbounded-packet-audit-v1/cstar-smale-unbounded/build/verified/Checks.log](../build/cstar-smale-unbounded-packet-audit-v1/cstar-smale-unbounded/build/verified/Checks.log).

```lean
CStarSmaleUnbounded.critical_iff (epsilon : ℝ) (he : 0 < epsilon) (w : CStarSmaleUnbounded.FunctionAlgebra) :
  CStarSmaleUnbounded.cubicDeleted (CStarSmaleUnbounded.roots epsilon) w = 0 ↔
    w = CStarSmaleUnbounded.branch epsilon ∨ w = -CStarSmaleUnbounded.branch epsilon
```

```lean
CStarSmaleUnbounded.deleted_coordinate_unit (epsilon : ℝ) (he : 0 < epsilon) :
  IsUnit (CStarSmaleUnbounded.cubicDeleted (CStarSmaleUnbounded.roots epsilon) CStarSmaleUnbounded.coordinate)
```

```lean
CStarSmaleUnbounded.infinite_cubic_constant : CStarSmaleUnbounded.InfiniteConstantTheorem
```

```lean
CStarSmaleUnbounded.no_finite_cubic_bound : ¬∃ C, 0 ≤ C ∧ CStarSmaleUnbounded.CubicBound C
```


## 29. Globally injective C*-power series refutes general-coefficient Bieberbach bounds

Checked from [build/cstar-bieberbach-packet-audit-v1/cstar-bieberbach/build/verified/Checks.log](../build/cstar-bieberbach-packet-audit-v1/cstar-bieberbach/build/verified/Checks.log).

```lean
CStarBieberbach.primitiveTerm_summable.{u_1} {A : Type u_1} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  (a u : A) : Summable (CStarBieberbach.primitiveTerm a u)
```

```lean
CStarBieberbach.source_series_hasSum.{u_1} {A : Type u_1} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  (a u : A) : HasSum (fun n => CStarBieberbach.coefficient a (n + 2) * u ^ (n + 2)) (CStarBieberbach.entireMap a u - u)
```

```lean
CStarBieberbach.derivative_series_summable.{u_1} {A : Type u_1} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  (a u : A) : Summable fun n => (↑n + 2) • (CStarBieberbach.coefficient a (n + 2) * u ^ (n + 1))
```

```lean
CStarBieberbach.witnessMap_injective : Function.Injective CStarBieberbach.witnessMap
```

```lean
CStarBieberbach.source_counterexample : ¬CStarBieberbach.SourceClaim
```

```lean
CStarBieberbach.source_strong_counterexample : ¬CStarBieberbach.SourceStrongClaim
```


## 30. Interior two-term refutation of Bessel–Fourier kernel positivity

Checked from [build/bessel-fejer-packet-audit-v1/bessel-fejer/build/verified/Checks.log](../build/bessel-fejer-packet-audit-v1/bessel-fejer/build/verified/Checks.log).

```lean
BesselFejer.source_first_two_characterization :
  IsLeast {x | 0 < x ∧ BesselFejer.besselJ0 x = 0} (BesselFejer.sourceZero 1) ∧
    IsLeast {x | BesselFejer.sourceZero 1 < x ∧ BesselFejer.besselJ0 x = 0} (BesselFejer.sourceZero 2)
```

```lean
BesselFejer.source_first_two_zero_bounds :
  BesselFejer.sourceZero 1 ∈ Set.Icc (24048 / 10000) (24049 / 10000) ∧
    BesselFejer.sourceZero 2 ∈ Set.Icc (55200 / 10000) (55201 / 10000)
```

```lean
BesselFejer.source_kernel_interior_negative : BesselFejer.sourceKernel (2 / 5) 2 (47 / 50) < -(1 / 500)
```

```lean
BesselFejer.source_counterexample_365454 : ¬BesselFejer.SourceClaim365454
```

