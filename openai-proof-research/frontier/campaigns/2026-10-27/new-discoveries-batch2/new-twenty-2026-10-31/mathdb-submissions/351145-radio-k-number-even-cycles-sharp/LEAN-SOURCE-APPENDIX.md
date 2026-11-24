# Lean source appendix

Complete formalization of MathDB 351145. Modules in import order; every block is byte-identical to src/.

### `RadioDefinitions.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace RadioCycles
attribute [local instance] Classical.propDecidable

abbrev cycle (n : ℕ) : SimpleGraph (Fin n) := SimpleGraph.cycleGraph n

noncomputable def D {n : ℕ} (i j : Fin n) : ℕ := (cycle n).dist i j

def Radio {n : ℕ} (k : ℕ) (f : Fin n → ℕ) : Prop :=
  ∀ i j, i ≠ j → (k : ℤ) + 1 - (D i j : ℤ) ≤ |(f i : ℤ) - f j|

noncomputable def span {n : ℕ} (f : Fin n → ℕ) : ℕ :=
  Finset.univ.sup (fun i => Finset.univ.sup (fun j => Nat.dist (f i) (f j)))

def Attainable (n k s : ℕ) : Prop := ∃ f : Fin n → ℕ, Radio k f ∧ span f = s

theorem exists_radio (n k : ℕ) : ∃ f : Fin n → ℕ, Radio k f := by
  refine ⟨fun i => i.val * (k + 1), ?_⟩
  intro i j hij
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hd : (0 : ℤ) ≤ D i j := Int.natCast_nonneg _
  rcases lt_or_gt_of_ne hne with h | h
  · have hm : (i.val : ℤ) + 1 ≤ j.val := by omega
    have hk : (0 : ℤ) ≤ k := Int.natCast_nonneg _
    have hb : (k : ℤ) + 1 ≤ (j.val : ℤ) * (k + 1) - (i.val : ℤ) * (k + 1) := by
      nlinarith
    have ha := neg_le_abs ((i.val : ℤ) * (k + 1) - (j.val : ℤ) * (k + 1))
    omega
  · have hm : (j.val : ℤ) + 1 ≤ i.val := by omega
    have hk : (0 : ℤ) ≤ k := Int.natCast_nonneg _
    have hb : (k : ℤ) + 1 ≤ (i.val : ℤ) * (k + 1) - (j.val : ℤ) * (k + 1) := by
      nlinarith
    have ha := le_abs_self ((i.val : ℤ) * (k + 1) - (j.val : ℤ) * (k + 1))
    omega

theorem exists_attainable (n k : ℕ) : ∃ s, Attainable n k s := by
  obtain ⟨f, hf⟩ := exists_radio n k
  exact ⟨span f, f, hf, rfl⟩

noncomputable def radioKNumber (n k : ℕ) : ℕ := Nat.find (exists_attainable n k)

theorem radioKNumber_attained (n k : ℕ) :
    ∃ f : Fin n → ℕ, Radio k f ∧ span f = radioKNumber n k :=
  Nat.find_spec (exists_attainable n k)

theorem radioKNumber_le {n k : ℕ} {f : Fin n → ℕ} (hf : Radio k f) :
    radioKNumber n k ≤ span f :=
  Nat.find_min' (exists_attainable n k) ⟨f, hf, rfl⟩

theorem le_radioKNumber_iff (n k b : ℕ) :
    b ≤ radioKNumber n k ↔ ∀ f : Fin n → ℕ, Radio k f → b ≤ span f := by
  constructor
  · intro hb f hf
    exact hb.trans (radioKNumber_le hf)
  · intro hb
    obtain ⟨f, hf, he⟩ := radioKNumber_attained n k
    rw [← he]
    exact hb f hf

/-- The even-n, odd-k branch, evaluated in the integers before conversion. -/
def lowerBoundInt (n k : ℕ) : ℤ :=
  ((n : ℤ) / 2 - 1) * ((3 * (k : ℤ) + 3 - n) / 2) + k + 1 - (n : ℤ) / 2

def lowerBound (n k : ℕ) : ℕ := (lowerBoundInt n k).toNat

def hParam (n k : ℕ) : ℕ := (n - k - 1) / 2

def pParam (n k : ℕ) : ℕ := Nat.gcd n (hParam n k)

/-- This is a proposition to be proved, not an asserted theorem. -/
def SharpConjecture : Prop := ∀ n k : ℕ,
  Even n → Odd k → n / 2 ≤ k → k < n - 3 →
  ((n / 2 : ℕ) : ZMod n) ∈ AddSubgroup.zmultiples (hParam n k : ZMod n) →
  radioKNumber n k = lowerBound n k + pParam n k - 1

#print axioms exists_radio
#print axioms radioKNumber_attained
#print axioms radioKNumber_le
#print axioms le_radioKNumber_iff

end RadioCycles
```

### `RadioLabels.lean`

```lean
import RadioDefinitions
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Order
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic.Ring

namespace RadioCycles

attribute [local instance] Classical.propDecidable

theorem dist_le_span {n : ℕ} (f : Fin n → ℕ) (i j : Fin n) :
    Nat.dist (f i) (f j) ≤ span f := by
  unfold span
  exact (Finset.le_sup (f := fun j => Nat.dist (f i) (f j)) (Finset.mem_univ j)).trans
    (Finset.le_sup (f := fun i => Finset.univ.sup (fun j => Nat.dist (f i) (f j))) (Finset.mem_univ i))

theorem span_eq_max_of_zero {n : ℕ} (f : Fin n → ℕ) (hzero : ∃ j, f j = 0) :
    span f = Finset.univ.sup f := by
  obtain ⟨j, hj⟩ := hzero
  apply le_antisymm
  · unfold span
    refine Finset.sup_le fun i _ => Finset.sup_le fun l _ => ?_
    have hi : f i ≤ Finset.univ.sup f := Finset.le_sup (Finset.mem_univ i)
    have hl : f l ≤ Finset.univ.sup f := Finset.le_sup (Finset.mem_univ l)
    simp only [Nat.dist]
    omega
  · refine Finset.sup_le fun i _ => ?_
    have h := dist_le_span f i j
    simpa [hj, Nat.dist] using h

theorem span_eq_max_sub_min {n : ℕ} (f : Fin n → ℕ) (j : Fin n)
    (hmin : ∀ i, f j ≤ f i) : span f = Finset.univ.sup f - f j := by
  apply le_antisymm
  · unfold span
    refine Finset.sup_le fun i _ => Finset.sup_le fun l _ => ?_
    have hi : f i ≤ Finset.univ.sup f := Finset.le_sup (Finset.mem_univ i)
    have hl : f l ≤ Finset.univ.sup f := Finset.le_sup (Finset.mem_univ l)
    have hmi := hmin i
    have hml := hmin l
    simp only [Nat.dist]
    omega
  · have h : Finset.univ.sup f ≤ span f + f j := by
      refine Finset.sup_le fun i _ => ?_
      have hi := dist_le_span f i j
      have hm := hmin i
      simp only [Nat.dist] at hi
      omega
    omega

def normalize {n : ℕ} (f : Fin n → ℕ) (m : ℕ) : Fin n → ℕ := fun i => f i - m

theorem normalize_radio {n k m : ℕ} {f : Fin n → ℕ}
    (hf : Radio k f) (hm : ∀ i, m ≤ f i) : Radio k (normalize f m) := by
  intro i j hij
  have hmi := hm i
  have hmj := hm j
  have hi : ((f i - m : ℕ) : ℤ) = (f i : ℤ) - m := by omega
  have hj : ((f j - m : ℕ) : ℤ) = (f j : ℤ) - m := by omega
  have he : ((normalize f m i : ℕ) : ℤ) - normalize f m j = (f i : ℤ) - f j := by
    simp only [normalize, hi, hj]
    ring
  rw [he]
  exact hf i j hij

theorem normalize_span {n : ℕ} (f : Fin n → ℕ) (m : ℕ) (hm : ∀ i, m ≤ f i) :
    span (normalize f m) = span f := by
  have he : ∀ i j, Nat.dist (normalize f m i) (normalize f m j) = Nat.dist (f i) (f j) := by
    intro i j
    have hi := hm i
    have hj := hm j
    simp only [normalize, Nat.dist]
    omega
  simp only [span, he]

theorem exists_normalized {n k : ℕ} (hn : 0 < n) (f : Fin n → ℕ) (hf : Radio k f) :
    ∃ g : Fin n → ℕ, Radio k g ∧ (∃ j, g j = 0) ∧ span g = span f := by
  let s := Finset.univ.image f
  have hs : s.Nonempty := ⟨f ⟨0, hn⟩, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩
  let m := s.min' hs
  have hm : ∀ i, m ≤ f i := fun i => Finset.min'_le s _
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hmem : m ∈ s := Finset.min'_mem s hs
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
  refine ⟨normalize f m, normalize_radio hf hm, ⟨j, ?_⟩, normalize_span f m hm⟩
  simp [normalize, hj]

/-- A finite injective labeling has a strictly increasing vertex permutation.
This lemma is independent of the still-unproved cycle-diameter estimate. -/
theorem sorted_labeling {n : ℕ} (f : Fin n → ℕ) (hf : Function.Injective f) :
    ∃ x : Fin n ≃ Fin n, StrictMono (f ∘ x) := by
  classical
  let s := Finset.univ.image f
  have hc : s.card = n := by simp [s, Finset.card_image_of_injective _ hf]
  let e : Fin n ≃ s := (s.orderIsoOfFin hc).toEquiv
  let g : Fin n ≃ s := Equiv.ofBijective (fun i => ⟨f i, Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, rfl⟩⟩) (by
    constructor
    · intro i j h
      exact hf (congrArg Subtype.val h)
    · intro y
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp y.property
      exact ⟨i, Subtype.ext hi⟩)
  refine ⟨e.trans g.symm, ?_⟩
  have he : f ∘ (e.trans g.symm) = s.orderEmbOfFin hc := by
    funext i
    have h := congrArg Subtype.val (g.apply_symm_apply (e i))
    exact h
  rw [he]
  exact (s.orderEmbOfFin hc).strictMono

#print axioms span_eq_max_sub_min
#print axioms span_eq_max_of_zero
#print axioms normalize_radio
#print axioms normalize_span
#print axioms exists_normalized
#print axioms sorted_labeling

end RadioCycles
```

### `RadioGraph.lean`

```lean
import RadioLabels

namespace RadioCycles

theorem cycle_connected {n : ℕ} (hn : 0 < n) : (cycle n).Connected := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact SimpleGraph.cycleGraph_connected

theorem D_eq_zero_iff {n : ℕ} (hn : 0 < n) (i j : Fin n) : D i j = 0 ↔ i = j :=
  (cycle_connected hn).dist_eq_zero_iff

theorem D_pos {n : ℕ} (hn : 0 < n) (i j : Fin n) (hij : i ≠ j) : 0 < D i j :=
  (cycle_connected hn).pos_dist_of_ne hij

theorem D_comm {n : ℕ} (i j : Fin n) : D i j = D j i :=
  SimpleGraph.dist_comm

theorem D_triangle {n : ℕ} (hn : 0 < n) (i j l : Fin n) : D i l ≤ D i j + D j l :=
  ((cycle_connected hn) i j).dist_triangle_left l

theorem D_eq_one_iff {n : ℕ} (i j : Fin n) : D i j = 1 ↔ (cycle n).Adj i j :=
  SimpleGraph.dist_eq_one_iff_adj

/-- This is exactly the plus/minus-one Cayley adjacency, in Fin's
cyclic additive group, for all n≥2. -/
theorem cycle_adj (m : ℕ) (i j : Fin (m + 2)) :
    (cycle (m + 2)).Adj i j ↔ i - j = 1 ∨ j - i = 1 :=
  SimpleGraph.cycleGraph_adj

theorem radio_injective_of_distance_bound {n k : ℕ} {f : Fin n → ℕ}
    (hf : Radio k f) (hD : ∀ i j : Fin n, D i j ≤ k) : Function.Injective f := by
  intro i j he
  by_contra hij
  have hr := hf i j hij
  have hd := hD i j
  simp only [he, sub_self, abs_zero] at hr
  omega

theorem radioKNumber_normalized_attained (n k : ℕ) (hn : 0 < n) :
    ∃ f : Fin n → ℕ, Radio k f ∧ (∃ j, f j = 0) ∧ span f = radioKNumber n k := by
  obtain ⟨f, hf, hs⟩ := radioKNumber_attained n k
  obtain ⟨g, hg, hz, hspan⟩ := exists_normalized hn f hf
  exact ⟨g, hg, hz, hspan.trans hs⟩

#print axioms cycle_connected
#print axioms D_eq_zero_iff
#print axioms D_pos
#print axioms D_comm
#print axioms D_triangle
#print axioms D_eq_one_iff
#print axioms cycle_adj
#print axioms radio_injective_of_distance_bound
#print axioms radioKNumber_normalized_attained

end RadioCycles
```

### `RadioParameters.lean`

```lean
import RadioDefinitions
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Tactic.Ring

namespace RadioCycles

/-- The literal subgroup hypothesis is equivalent to the gcd divisibility. -/
theorem mem_zmultiples_iff_gcd_dvd (n h d : ℕ) :
    (d : ZMod n) ∈ AddSubgroup.zmultiples (h : ZMod n) ↔ Nat.gcd n h ∣ d := by
  rw [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨z, hz⟩
    have he : ((z * (h : ℤ) : ℤ) : ZMod n) = (d : ℤ) := by
      simpa [zsmul_eq_mul] using hz
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).mp he
    obtain ⟨a, ha⟩ := hd
    have hn : (Nat.gcd n h : ℤ) ∣ (n : ℤ) := by exact_mod_cast Nat.gcd_dvd_left n h
    have hh : (Nat.gcd n h : ℤ) ∣ (h : ℤ) := by exact_mod_cast Nat.gcd_dvd_right n h
    have hr : (d : ℤ) = (n : ℤ) * a + z * h := by linarith
    have hd : (Nat.gcd n h : ℤ) ∣ (d : ℤ) := by
      rw [hr]
      exact dvd_add (dvd_mul_of_dvd_left hn a) (dvd_mul_of_dvd_right hh z)
    exact_mod_cast hd
  · intro hd
    obtain ⟨a, ha⟩ := hd
    refine ⟨(a : ℤ) * Nat.gcdB n h, ?_⟩
    have hb := Nat.gcd_eq_gcd_ab n h
    have he : ((d : ℤ) : ZMod n) =
        (((a : ℤ) * Nat.gcdB n h) : ZMod n) * (h : ZMod n) := by
      have hc := congrArg (fun z : ℤ => (z : ZMod n)) hb
      simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul, ZMod.natCast_self,
        zero_mul, zero_add] at hc
      rw [ha]
      push_cast
      rw [hc]
      ring
    simpa [zsmul_eq_mul] using he.symm

/-- Elementary range/parity identities used by both bounds. -/
theorem parameter_arithmetic (n k : ℕ) (hn : Even n) (hk : Odd k)
    (hlo : n / 2 ≤ k) (hhi : k < n - 3) :
    3 ≤ n ∧ 2 ≤ hParam n k ∧
    n = 2 * (n / 2) ∧ k + 1 + 2 * hParam n k = n ∧
    2 * hParam n k ≤ n / 2 - 1 ∧ 4 * hParam n k < n ∧
    1 ≤ n / 2 - 2 * hParam n k ∧
    pParam n k ≤ hParam n k := by
  obtain ⟨d, hd⟩ := hn
  obtain ⟨r, hr⟩ := hk
  have hn' : n = 2 * d := by omega
  have hk' : k = 2 * r + 1 := by omega
  have he : n - k - 1 = 2 * (d - r - 1) := by omega
  have hh : hParam n k = d - r - 1 := by simp [hParam, he]
  have hp : pParam n k ≤ hParam n k := Nat.gcd_le_right n (by omega)
  simp only [hh] at hp ⊢
  omega

/-- Rewriting the source LB with exact integer arithmetic; no truncated
natural subtraction is used in its definition. -/
theorem lowerBoundInt_formula (n k : ℕ) (hn : Even n) (hk : Odd k)
    (hlo : n / 2 ≤ k) (hhi : k < n - 3) :
    lowerBoundInt n k =
      ((n / 2 : ℕ) - 1 : ℤ) * (2 * (n / 2 : ℕ) - 3 * (hParam n k : ℤ)) +
        (n / 2 : ℕ) - 2 * (hParam n k : ℤ) := by
  obtain ⟨_, _, hn2, hk2, _, _, _, _⟩ := parameter_arithmetic n k hn hk hlo hhi
  have hnz : (n : ℤ) = 2 * (n / 2 : ℕ) := by exact_mod_cast hn2
  have hkz : (k : ℤ) + 1 + 2 * hParam n k = n := by exact_mod_cast hk2
  have hdiv : (n : ℤ) / 2 = (n / 2 : ℕ) := by omega
  have hphi : (3 * (k : ℤ) + 3 - n) / 2 =
      2 * (n / 2 : ℕ) - 3 * (hParam n k : ℤ) := by omega
  unfold lowerBoundInt
  rw [hdiv, hphi]
  nlinarith

/-- The source uses a ceiling in Phi. On the target parities it is
exactly the integer quotient used by lowerBoundInt. -/
theorem source_phi_agrees (n k : ℕ) (hn : Even n) (hk : Odd k) :
    (3 * (k : ℤ) + 3 - n + 1) / 2 = (3 * (k : ℤ) + 3 - n) / 2 := by
  obtain ⟨d, hd⟩ := hn
  obtain ⟨r, hr⟩ := hk
  have hnz : (n : ℤ) = 2 * d := by exact_mod_cast (show n = 2 * d by omega)
  have hkz : (k : ℤ) = 2 * r + 1 := by exact_mod_cast (show k = 2 * r + 1 by omega)
  omega

theorem lowerBoundInt_nonneg (n k : ℕ) (hn : Even n) (hk : Odd k)
    (hlo : n / 2 ≤ k) (hhi : k < n - 3) : 0 ≤ lowerBoundInt n k := by
  have ha := parameter_arithmetic n k hn hk hlo hhi
  have hh : 2 * (hParam n k : ℤ) ≤ (n / 2 : ℕ) - 1 := by omega
  have hm : 0 ≤ ((n / 2 : ℕ) - 1 : ℤ) *
      (2 * (n / 2 : ℕ) - 3 * (hParam n k : ℤ)) :=
    mul_nonneg (by omega) (by omega)
  rw [lowerBoundInt_formula n k hn hk hlo hhi]
  omega

theorem lowerBound_cast (n k : ℕ) (hn : Even n) (hk : Odd k)
    (hlo : n / 2 ≤ k) (hhi : k < n - 3) :
    (lowerBound n k : ℤ) = lowerBoundInt n k := by
  exact Int.toNat_of_nonneg (lowerBoundInt_nonneg n k hn hk hlo hhi)

/-- The target assumptions are satisfiable; this is not a theorem over an
empty parameter set. This does not prove sharpness even for this example. -/
theorem admissible_parameters_exist : ∃ n k : ℕ,
    Even n ∧ Odd k ∧ n / 2 ≤ k ∧ k < n - 3 ∧
    ((n / 2 : ℕ) : ZMod n) ∈ AddSubgroup.zmultiples (hParam n k : ZMod n) := by
  refine ⟨12, 7, by decide, by decide, by decide, by decide, ?_⟩
  rw [mem_zmultiples_iff_gcd_dvd]
  decide

#print axioms mem_zmultiples_iff_gcd_dvd
#print axioms parameter_arithmetic
#print axioms lowerBoundInt_formula
#print axioms source_phi_agrees
#print axioms lowerBoundInt_nonneg
#print axioms lowerBound_cast
#print axioms admissible_parameters_exist

end RadioCycles
```

### `RadioPath.lean`

```lean
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace RadioCycles

/-- Total variation of the finite path z_0,...,z_m. -/
def variation (z : ℕ → ℤ) (m : ℕ) : ℤ :=
  ∑ t ∈ Finset.range m, |z (t + 1) - z t|

@[simp] theorem variation_zero (z : ℕ → ℤ) : variation z 0 = 0 := by
  simp [variation]

@[simp] theorem variation_succ (z : ℕ → ℤ) (m : ℕ) :
    variation z (m + 1) = variation z m + |z (m + 1) - z m| := by
  simp [variation, Finset.sum_range_succ]

theorem travel_le_variation (z : ℕ → ℤ) {i j : ℕ} (hij : i ≤ j) :
    |z j - z i| ≤ variation z j - variation z i := by
  induction j with
  | zero => have : i = 0 := by omega
            simp [this]
  | succ j ih =>
    by_cases h : i ≤ j
    · have hi := ih h
      have ht : |z (j + 1) - z i| ≤ |z (j + 1) - z j| + |z j - z i| := by
        calc
          _ = |(z (j + 1) - z j) + (z j - z i)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      rw [variation_succ]
      linarith
    · have : i = j + 1 := by omega
      simp [this]

/-- The endpoint term is essential: this is an open path, not a closed walk. -/
theorem path_range (z : ℕ → ℤ) {m i j : ℕ} (hi : i ≤ m) (hj : j ≤ m) :
    2 * |z i - z j| ≤ variation z m + |z m - z 0| := by
  have ordered : ∀ a b : ℕ, a ≤ b → b ≤ m →
      2 * |z b - z a| ≤ variation z m + |z m - z 0| := by
    intro a b hab hbm
    have hA := travel_le_variation z (Nat.zero_le a)
    have hB := travel_le_variation z hab
    have hC := travel_le_variation z hbm
    have hT : |z b - z a| ≤ |z m - z b| + |z m - z 0| + |z a - z 0| := by
      calc
        _ = |-(z m - z b) + (z m - z 0) - (z a - z 0)| := by congr 1; ring
        _ ≤ |-(z m - z b) + (z m - z 0)| + |z a - z 0| := abs_sub _ _
        _ ≤ (|-(z m - z b)| + |z m - z 0|) + |z a - z 0| :=
          add_le_add (abs_add_le _ _) le_rfl
        _ = _ := by rw [abs_neg]
    simp only [variation_zero] at hA
    linarith
  rcases le_total i j with h | h
  · rw [abs_sub_comm]
    exact ordered i j h hj
  · exact ordered j i h hi

/-- If the variation and endpoint cost total at most 2s, all integer lifts
are separated by at most s. -/
theorem path_diameter_le (z : ℕ → ℤ) {m : ℕ} {s : ℤ}
    (hbudget : variation z m + |z m - z 0| ≤ 2 * s)
    {i j : ℕ} (hi : i ≤ m) (hj : j ≤ m) : |z i - z j| ≤ s := by
  have := path_range z hi hj
  omega

#print axioms travel_le_variation
#print axioms path_range
#print axioms path_diameter_le

end RadioCycles
```

### `RadioSlacks.lean`

```lean
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace RadioCycles

/-- The exact telescoping identity for the two nonnegative slack tracks. -/
theorem slack_sum_identity (ε η δ : ℕ → ℤ) (m : ℕ)
    (hrel : ∀ t < m, η t = ε t + δ (t + 1) - δ t) :
    (∑ t ∈ Finset.range m, η t) =
      (∑ t ∈ Finset.range m, ε t) + δ m - δ 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih (fun t ht => hrel t (by omega)),
      hrel m (by omega)]
    omega

/-- Monotonicity of the slack potential. -/
theorem slack_potential_mono (ε η δ : ℕ → ℤ) (m : ℕ)
    (hη : ∀ t < m, 0 ≤ η t)
    (hrel : ∀ t < m, η t = ε t + δ (t + 1) - δ t)
    {i j : ℕ} (hij : i ≤ j) (hjm : j ≤ m) :
    (∑ t ∈ Finset.range i, ε t) + δ i ≤
      (∑ t ∈ Finset.range j, ε t) + δ j := by
  induction j with
  | zero => have hi : i = 0 := by omega
            simp [hi]
  | succ j ih =>
    by_cases hi : i ≤ j
    · have h := ih hi (by omega)
      have hj : j < m := by omega
      have hηj := hη j hj
      have hr := hrel j hj
      rw [Finset.sum_range_succ]
      omega
    · have hi : i = j + 1 := by omega
      simp [hi]

/-- Equations (1)--(3) in the discovery proof, for arbitrary finite tracks. -/
theorem slack_bounds (ε η δ : ℕ → ℤ) (m : ℕ) (s : ℤ)
    (hε : ∀ t < m, 0 ≤ ε t) (hη : ∀ t < m, 0 ≤ η t)
    (hδ : ∀ t ≤ m, 0 ≤ δ t)
    (hrel : ∀ t < m, η t = ε t + δ (t + 1) - δ t)
    (hbudget : s = (∑ t ∈ Finset.range m, ε t) + δ m) :
    (∀ t ≤ m, δ t ≤ s) ∧
    (∀ t < m, ε t + δ (t + 1) ≤ s) ∧
    (∑ t ∈ Finset.range m, η t) = s - δ 0 ∧
    (∀ t < m, η t ≤ s) := by
  have hsum : ∀ i ≤ m, 0 ≤ ∑ t ∈ Finset.range i, ε t := by
    intro i hi
    exact Finset.sum_nonneg fun t ht => hε t (by have ht' := Finset.mem_range.mp ht; omega)
  have hδbound : ∀ t ≤ m, δ t ≤ s := by
    intro t ht
    have h := slack_potential_mono ε η δ m hη hrel ht (le_refl m)
    have he := hsum t ht
    omega
  have hεbound : ∀ t < m, ε t + δ (t + 1) ≤ s := by
    intro t ht
    have h := slack_potential_mono ε η δ m hη hrel (show t + 1 ≤ m by omega) (le_refl m)
    have he := hsum t (by omega)
    rw [Finset.sum_range_succ] at h
    omega
  have htotal : (∑ t ∈ Finset.range m, η t) = s - δ 0 := by
    rw [slack_sum_identity ε η δ m hrel]
    omega
  refine ⟨hδbound, hεbound, htotal, ?_⟩
  intro t ht
  have hle : η t ≤ ∑ t ∈ Finset.range m, η t := by
    exact Finset.single_le_sum (fun i hi => hη i (Finset.mem_range.mp hi))
      (Finset.mem_range.mpr ht)
  have hzero := hδ 0 (Nat.zero_le m)
  omega

#print axioms slack_sum_identity
#print axioms slack_potential_mono
#print axioms slack_bounds

end RadioCycles
```

### `RadioTracks.lean`

```lean
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace RadioCycles

/-- Strictly sub-modulus congruences do not wrap. -/
theorem no_wrap {n : ℕ} {z : ℤ} (hn : 0 < n)
    (hz : (z : ZMod n) = 0) (hb : |z| < (n : ℤ)) : z = 0 := by
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd z n).mp hz
  obtain ⟨a, ha⟩ := hd
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  have hb' := abs_lt.mp hb
  by_cases hp : 0 < a
  · have : (n : ℤ) ≤ n * a := by nlinarith
    omega
  · by_cases hm : a < 0
    · have : (n : ℤ) * a ≤ -(n : ℤ) := by nlinarith
      omega
    · have : a = 0 := by omega
      simp [this] at ha
      exact ha

/-- The two track signs agree at an individual step. No hypothesis says
that the sign is constant from one step to the next. -/
theorem same_direction (n : ℕ) (h s ε η δ δ' e e' u b σ τ : ℤ)
    (hhs : s < h) (hhn : 4 * h < (n : ℤ))
    (hε : 0 ≤ ε) (_hη : 0 ≤ η) (_hδ : 0 ≤ δ) (hδ' : 0 ≤ δ')
    (hrel : η = ε + δ' - δ) (hbudget : ε + δ' ≤ s)
    (he : |e| ≤ δ) (he' : |e'| ≤ δ')
    (hu : |u| ≤ ε) (hb : |b| ≤ η)
    (hσ : σ = -1 ∨ σ = 1) (hτ : τ = -1 ∨ τ = 1)
    (hcong : ((τ * h + b - (σ * h + u) - e' + e : ℤ) : ZMod n) = 0) :
    τ = σ ∧ b - u = e' - e := by
  have hnonneg : 0 ≤ s := by omega
  have hh : 0 < h := by omega
  have hn : 0 < n := by omega
  have heB := abs_le.mp he
  have heB' := abs_le.mp he'
  have huB := abs_le.mp hu
  have hbB := abs_le.mp hb
  have hbound : |τ * h + b - (σ * h + u) - e' + e| < (n : ℤ) := by
    apply abs_lt.mpr
    rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;>
      constructor <;> nlinarith
  have hzero := no_wrap hn hcong hbound
  have hsign : τ = σ := by
    rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl
    · rfl
    · exfalso; nlinarith
    · exfalso; nlinarith
    · rfl
  constructor
  · exact hsign
  · rw [hsign] at hzero
    linarith

/-- The difference of the integer lifts is an equality, not just a
congruence modulo p. -/
theorem lift_difference (V W e u b : ℕ → ℤ) (m : ℕ)
    (hV : V 0 = 0) (hW : W 0 = e 0)
    (hVstep : ∀ t < m, V (t + 1) = V t + u t)
    (hWstep : ∀ t < m, W (t + 1) = W t + b t)
    (hstep : ∀ t < m, b t - u t = e (t + 1) - e t) :
    ∀ t ≤ m, W t - V t = e t := by
  intro t ht
  induction t with
  | zero => simp [hV, hW]
  | succ t ih =>
    have ht' : t < m := by omega
    have hi := ih (by omega)
    rw [hVstep t ht', hWstep t ht']
    have hs := hstep t ht'
    omega

#print axioms no_wrap
#print axioms same_direction
#print axioms lift_difference

end RadioCycles
```

### `RadioResidues.lean`

```lean
import RadioPath
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Card

namespace RadioCycles

/-- An integer set of diameter at most s representing every residue modulo p
must contain an interval's worth of at least p points. -/
theorem residue_diameter_bound (p s : ℕ) (hp : 0 < p)
    (S : Finset ℤ) (hS : S.Nonempty)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ (s : ℤ))
    (hcover : ∀ r : ZMod p, ∃ z ∈ S, (z : ZMod p) = r) : p ≤ s + 1 := by
  classical
  let : NeZero p := ⟨by omega⟩
  let a := S.min' hS
  have ha : a ∈ S := Finset.min'_mem S hS
  have hsubset : S ⊆ Finset.Icc a (a + (s : ℤ)) := by
    intro x hx
    have hlo : a ≤ x := Finset.min'_le S x hx
    have hhi := (abs_le.mp (hdiam x hx a ha)).2
    exact Finset.mem_Icc.mpr ⟨hlo, by omega⟩
  have himage : S.image (fun z : ℤ => (z : ZMod p)) = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro r
    obtain ⟨z, hz, he⟩ := hcover r
    exact Finset.mem_image.mpr ⟨z, hz, he⟩
  have hcard : p ≤ S.card := by
    have hc := Finset.card_image_le (s := S) (f := fun z : ℤ => (z : ZMod p))
    rw [himage] at hc
    simpa using hc
  have hinterval := Finset.card_le_card hsubset
  have hcount : (Finset.Icc a (a + (s : ℤ))).card = s + 1 := by
    rw [Int.card_Icc]
    omega
  omega

/-- The abstract residue obstruction in the proof. The input is an actual
integer path, with coverage and the complete endpoint-sensitive budget. -/
theorem path_residue_bound (p s m : ℕ) (hp : 0 < p) (z : ℕ → ℤ)
    (hbudget : variation z m + |z m - z 0| ≤ 2 * (s : ℤ))
    (hcover : ∀ r : ZMod p, ∃ t ≤ m, (z t : ZMod p) = r) : p ≤ s + 1 := by
  classical
  let S := (Finset.range (m + 1)).image z
  have hS : S.Nonempty := ⟨z 0, Finset.mem_image.mpr ⟨0, by simp, rfl⟩⟩
  apply residue_diameter_bound p s hp S hS
  · intro x hx y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact path_diameter_le z hbudget (by simpa using hi) (by simpa using hj)
  · intro r
    obtain ⟨t, ht, he⟩ := hcover r
    exact ⟨z t, Finset.mem_image.mpr ⟨t, by simpa using ht, rfl⟩, he⟩

#print axioms residue_diameter_bound
#print axioms path_residue_bound

end RadioCycles
```

### `RadioLiftObstruction.lean`

```lean
import RadioResidues
import RadioSlacks
import Mathlib.Algebra.BigOperators.Intervals

namespace RadioCycles

theorem variation_congr (z w : ℕ → ℤ) (m : ℕ) (h : ∀ t ≤ m, z t = w t) :
    variation z m = variation w m := by
  unfold variation
  apply Finset.sum_congr rfl
  intro t ht
  rw [h t (by have := Finset.mem_range.mp ht; omega),
    h (t + 1) (by have := Finset.mem_range.mp ht; omega)]

theorem variation_reverse (V : ℕ → ℤ) (m : ℕ) :
    variation (fun t => V (m - t)) m = variation V m := by
  unfold variation
  rw [← Finset.sum_range_reflect (fun t => |V (t + 1) - V t|) m]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_range.mp ht
  have h1 : m - 1 - t + 1 = m - t := by omega
  have h2 : m - 1 - t = m - (t + 1) := by omega
  change |V (m - (t + 1)) - V (m - t)| =
    |V (m - 1 - t + 1) - V (m - 1 - t)|
  rw [h1, h2]
  exact abs_sub_comm (V (m - (t + 1))) (V (m - t))

/-- V followed backwards, then the initial bridge, then W forwards. -/
def joinedPath (V W : ℕ → ℤ) (m t : ℕ) : ℤ :=
  if t ≤ m then V (m - t) else W (t - (m + 1))

theorem joinedPath_variation (V W : ℕ → ℤ) (m : ℕ) :
    variation (joinedPath V W m) (m + 1 + m) =
      variation V m + |W 0 - V 0| + variation W m := by
  let z := joinedPath V W m
  have hfirst : variation z m = variation V m := by
    rw [variation_congr z (fun t => V (m - t)) m (by
      intro t ht; simp [z, joinedPath, ht]), variation_reverse]
  have hmid : |z (m + 1) - z m| = |W 0 - V 0| := by
    simp [z, joinedPath]
  have hlast : (∑ t ∈ Finset.range m, |z (m + 1 + t + 1) - z (m + 1 + t)|) =
      variation W m := by
    unfold variation
    apply Finset.sum_congr rfl
    intro t _
    have h1 : ¬m + 1 + t + 1 ≤ m := by omega
    have h2 : ¬m + 1 + t ≤ m := by omega
    have h3 : m + 1 + t + 1 - (m + 1) = t + 1 := by omega
    have h4 : m + 1 + t - (m + 1) = t := by omega
    simp [z, joinedPath, h1, h2, h3, h4]
  change variation z (m + 1 + m) = _
  unfold variation
  rw [Finset.sum_range_add]
  change variation z (m + 1) + _ = _
  rw [variation_succ, hfirst, hmid, hlast]
  rfl

/-- The entire integer-lift/cardinality conclusion, conditional on obtaining
the two tracks and their slack data from the graph. -/
theorem two_track_residue_bound (p s m : ℕ) (hp : 0 < p)
    (V W ε η δ : ℕ → ℤ)
    (hε : ∀ t < m, 0 ≤ ε t) (hη : ∀ t < m, 0 ≤ η t)
    (hδ : ∀ t ≤ m, 0 ≤ δ t)
    (hrel : ∀ t < m, η t = ε t + δ (t + 1) - δ t)
    (hbudget : (s : ℤ) = (∑ t ∈ Finset.range m, ε t) + δ m)
    (hV : ∀ t < m, |V (t + 1) - V t| ≤ ε t)
    (hW : ∀ t < m, |W (t + 1) - W t| ≤ η t)
    (hstart : |W 0 - V 0| ≤ δ 0) (hend : |W m - V m| ≤ δ m)
    (hcover : ∀ r : ZMod p, ∃ t ≤ m,
      (V t : ZMod p) = r ∨ (W t : ZMod p) = r) : p ≤ s + 1 := by
  have hsumη := (slack_bounds ε η δ m s hε hη hδ hrel hbudget).2.2.1
  have hvarV : variation V m ≤ ∑ t ∈ Finset.range m, ε t := by
    exact Finset.sum_le_sum fun t ht => hV t (Finset.mem_range.mp ht)
  have hvarW : variation W m ≤ ∑ t ∈ Finset.range m, η t := by
    exact Finset.sum_le_sum fun t ht => hW t (Finset.mem_range.mp ht)
  apply path_residue_bound p s (m + 1 + m) hp (joinedPath V W m)
  · rw [joinedPath_variation]
    have he : |joinedPath V W m (m + 1 + m) - joinedPath V W m 0| =
        |W m - V m| := by
      simp [joinedPath, show ¬m + 1 + m ≤ m by omega]
    rw [he]
    omega
  · intro r
    obtain ⟨t, ht, hr⟩ := hcover r
    rcases hr with hr | hr
    · refine ⟨m - t, by omega, ?_⟩
      simpa [joinedPath, show m - t ≤ m by omega, Nat.sub_sub_self ht] using hr
    · refine ⟨m + 1 + t, by omega, ?_⟩
      simpa [joinedPath, show ¬m + 1 + t ≤ m by omega] using hr

#print axioms joinedPath_variation
#print axioms two_track_residue_bound

end RadioCycles
```

### `RadioEndpoints.lean`

```lean
import RadioParameters
import RadioGraph
import RadioTracks
import RadioLiftObstruction

namespace RadioCycles

/-- The span's Nat.dist is precisely the absolute integer label difference. -/
theorem label_distance_cast (a b : ℕ) :
    (Nat.dist a b : ℤ) = |(a : ℤ) - b| := by
  by_cases h : a ≤ b
  · rw [Nat.dist_eq_sub_of_le h, abs_of_nonpos (by omega)]
    omega
  · rw [Nat.dist_eq_sub_of_le_right (by omega), abs_of_nonneg (by omega)]
    omega

theorem span_le_iff {n : ℕ} (f : Fin n → ℕ) (s : ℕ) :
    span f ≤ s ↔ ∀ i j, |(f i : ℤ) - f j| ≤ (s : ℤ) := by
  simp only [span, Finset.sup_le_iff, Finset.mem_univ, forall_const]
  constructor
  · intro h i j
    rw [← label_distance_cast]
    exact_mod_cast h i j
  · intro h i j
    have hi := h i j
    rw [← label_distance_cast] at hi
    exact_mod_cast hi


-- Infrastructure endpoints; the assembled equality is proved in RadioTheorem.
#check radioKNumber_normalized_attained
#check mem_zmultiples_iff_gcd_dvd
#check parameter_arithmetic
#check lowerBoundInt_formula
#check lowerBound_cast
#check sorted_labeling
#check slack_bounds
#check same_direction
#check path_range
#check two_track_residue_bound
#print SharpConjecture

#print axioms label_distance_cast
#print axioms span_le_iff
#print axioms radioKNumber_normalized_attained
#print axioms mem_zmultiples_iff_gcd_dvd
#print axioms parameter_arithmetic
#print axioms lowerBoundInt_formula
#print axioms lowerBound_cast
#print axioms sorted_labeling
#print axioms slack_bounds
#print axioms same_direction
#print axioms path_range
#print axioms two_track_residue_bound

#print axioms exists_radio
#print axioms exists_attainable
#print axioms radioKNumber_attained
#print axioms radioKNumber_le
#print axioms le_radioKNumber_iff
#print axioms variation_zero
#print axioms variation_succ
#print axioms travel_le_variation
#print axioms path_diameter_le
#print axioms dist_le_span
#print axioms span_eq_max_of_zero
#print axioms span_eq_max_sub_min
#print axioms normalize_radio
#print axioms normalize_span
#print axioms exists_normalized
#print axioms source_phi_agrees
#print axioms lowerBoundInt_nonneg
#print axioms admissible_parameters_exist
#print axioms slack_sum_identity
#print axioms slack_potential_mono
#print axioms no_wrap
#print axioms lift_difference
#print axioms residue_diameter_bound
#print axioms path_residue_bound
#print axioms variation_congr
#print axioms variation_reverse
#print axioms joinedPath_variation
#print axioms cycle_connected
#print axioms D_eq_zero_iff
#print axioms D_pos
#print axioms D_comm
#print axioms D_triangle
#print axioms D_eq_one_iff
#print axioms cycle_adj
#print axioms radio_injective_of_distance_bound

end RadioCycles
```

### `RadioArcDistance.lean`

```lean
import RadioGraph

namespace RadioCycles

/-- The two arc lengths, using the source's canonical vertex representatives. -/
def arcDistance {n : ℕ} (i j : Fin n) : ℕ :=
  min (Nat.dist i.val j.val) (n - Nat.dist i.val j.val)

theorem arcDistance_comm {n : ℕ} (i j : Fin n) :
    arcDistance i j = arcDistance j i := by
  simp [arcDistance, Nat.dist_comm]

theorem arcDistance_triangle {n : ℕ} (i j l : Fin n) :
    arcDistance i l ≤ arcDistance i j + arcDistance j l := by
  have hi := i.isLt
  have hj := j.isLt
  have hl := l.isLt
  simp only [arcDistance, Nat.dist]
  omega

theorem arcDistance_adj {n : ℕ} {i j : Fin n} (h : (cycle n).Adj i j) :
    arcDistance i j = 1 := by
  rw [SimpleGraph.cycleGraph_adj'] at h
  rcases h with h | h
  · by_cases hij : j ≤ i
    · rw [Fin.coe_sub_iff_le.mpr hij] at h
      simp only [arcDistance, Nat.dist]
      have hi := i.isLt
      have hj := j.isLt
      have hij' : j.val ≤ i.val := hij
      omega
    · have hij' : i < j := lt_of_not_ge hij
      rw [Fin.coe_sub_iff_lt.mpr hij'] at h
      simp only [arcDistance, Nat.dist]
      have hi := i.isLt
      have hj := j.isLt
      have hij'' : i.val < j.val := hij'
      omega
  · rw [arcDistance_comm]
    by_cases hij : i ≤ j
    · rw [Fin.coe_sub_iff_le.mpr hij] at h
      simp only [arcDistance, Nat.dist]
      have hi := i.isLt
      have hj := j.isLt
      have hij' : i.val ≤ j.val := hij
      omega
    · have hij' : j < i := lt_of_not_ge hij
      rw [Fin.coe_sub_iff_lt.mpr hij'] at h
      simp only [arcDistance, Nat.dist]
      have hi := i.isLt
      have hj := j.isLt
      have hij'' : j.val < i.val := hij'
      omega

theorem arcDistance_le_walk {n : ℕ} {i j : Fin n} (w : (cycle n).Walk i j) :
    arcDistance i j ≤ w.length := by
  induction w with
  | nil => simp [arcDistance]
  | @cons u v w huv p ih =>
    have ht := arcDistance_triangle u v w
    rw [arcDistance_adj huv] at ht
    simp only [SimpleGraph.Walk.length_cons]
    omega


#print axioms arcDistance_comm
#print axioms arcDistance_triangle
#print axioms arcDistance_adj
#print axioms arcDistance_le_walk

end RadioCycles
```

### `RadioCycleMetric.lean`

```lean
import RadioArcDistance

namespace RadioCycles

theorem D_le_forward {n : ℕ} (hn : 0 < n) (i j : Fin n) (hij : i.val ≤ j.val) :
    D i j ≤ j.val - i.val := by
  obtain ⟨b, hb⟩ := j
  change i.val ≤ b at hij
  change D i ⟨b, hb⟩ ≤ b - i.val
  induction b generalizing i with
  | zero =>
    have hi : i = ⟨0, hb⟩ := Fin.ext (by change i.val = 0; omega)
    subst i
    simp [D, SimpleGraph.dist_self]
  | succ b ih =>
    by_cases he : i.val = b + 1
    · have hi : i = ⟨b + 1, hb⟩ := Fin.ext he
      subst i
      simp [D, SimpleGraph.dist_self]
    · let v : Fin n := ⟨b, by omega⟩
      have hv : D i v ≤ b - i.val := ih i (by omega) (by omega)
      have ha : (cycle n).Adj v ⟨b + 1, hb⟩ :=
        SimpleGraph.pathGraph_le_cycleGraph (SimpleGraph.pathGraph_adj.mpr (Or.inl rfl))
      have hd := (D_eq_one_iff v ⟨b + 1, hb⟩).mpr ha
      have ht := D_triangle hn i v ⟨b + 1, hb⟩
      omega

theorem D_le_linear {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    D i j ≤ Nat.dist i.val j.val := by
  rcases le_total i.val j.val with h | h
  · have := D_le_forward hn i j h
    simp only [Nat.dist]
    omega
  · rw [D_comm]
    have := D_le_forward hn j i h
    simp only [Nat.dist]
    omega

/-- The graph distance is exactly the minimum of the two cycle arcs. -/
theorem D_eq_arcDistance {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    D i j = arcDistance i j := by
  have hn0 : 0 < n := by omega
  apply le_antisymm
  · have hlin := D_le_linear hn0 i j
    have wrap : ∀ u v : Fin n, u.val ≤ v.val → D u v ≤ n - (v.val - u.val) := by
      intro u v huv
      let z : Fin n := ⟨0, hn0⟩
      let l : Fin n := ⟨n - 1, by omega⟩
      have h0 := D_le_linear hn0 u z
      have h1 := D_le_linear hn0 l v
      have hadj : (cycle n).Adj z l := by
        rw [SimpleGraph.cycleGraph_adj']
        left
        rw [Fin.coe_sub_iff_lt.mpr (show z < l by change 0 < n - 1; omega)]
        dsimp [z, l]
        omega
      have h2 := (D_eq_one_iff z l).mpr hadj
      have ht := D_triangle hn0 u z v
      have ht' := D_triangle hn0 z l v
      dsimp [z, l] at h0 h1
      simp only [Nat.dist] at h0 h1
      have hv := v.isLt
      dsimp [z, l] at h2 ht ht'
      omega
    rcases le_total i.val j.val with h | h
    · have hw := wrap i j h
      simp only [arcDistance, Nat.dist] at *
      omega
    · have hw := wrap j i h
      rw [D_comm j i] at hw
      simp only [arcDistance, Nat.dist] at *
      omega
  · obtain ⟨w, hw⟩ := ((cycle_connected hn0) i j).exists_walk_length_eq_dist
    have ha := arcDistance_le_walk w
    change w.length = D i j at hw
    omega

theorem D_formula {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    D i j = min (Nat.dist i.val j.val) (n - Nat.dist i.val j.val) :=
  D_eq_arcDistance hn i j

theorem D_diameter {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) : D i j ≤ n / 2 := by
  rw [D_formula hn]
  have hi := i.isLt
  have hj := j.isLt
  simp only [Nat.dist]
  omega

theorem D_perimeter {n : ℕ} (hn : 3 ≤ n) (i j l : Fin n) :
    D i j + D j l + D i l ≤ n := by
  rw [D_formula hn, D_formula hn, D_formula hn]
  have hi := i.isLt
  have hj := j.isLt
  have hl := l.isLt
  simp only [Nat.dist]
  omega

#print axioms D_formula
#print axioms D_diameter
#print axioms D_perimeter

end RadioCycles
```

### `RadioCycleGeometry.lean`

```lean
import RadioCycleMetric
import RadioTracks

namespace RadioCycles

def antipode {n : ℕ} (hn : 3 ≤ n) (i : Fin n) : Fin n :=
  i + ⟨n / 2, by omega⟩

theorem D_antipode {n : ℕ} (hn : 3 ≤ n) (he : Even n) (i j : Fin n) :
    D (antipode hn i) j + D i j = n / 2 := by
  obtain ⟨d, hd⟩ := he
  have hn2 : n = 2 * d := by omega
  have hhalf : n / 2 = d := by omega
  rw [D_formula hn, D_formula hn]
  simp only [antipode, Fin.val_add_eq_ite, hhalf, Nat.dist]
  have hi := i.isLt
  have hj := j.isLt
  split_ifs <;> omega

theorem D_translate {n : ℕ} (hn : 3 ≤ n) (i j a : Fin n) :
    D (i + a) (j + a) = D i j := by
  rw [D_formula hn, D_formula hn]
  simp only [Fin.val_add_eq_ite, Nat.dist]
  have hi := i.isLt
  have hj := j.isLt
  have ha := a.isLt
  split_ifs <;> omega

/-- Signed shortest displacements, with a congruence in the literal cycle. -/
theorem signed_displacement {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    ∃ q : ℤ, |q| = (D i j : ℤ) ∧
      (q : ZMod n) = (j.val : ZMod n) - (i.val : ZMod n) := by
  have hi := i.isLt
  have hj := j.isLt
  have hd := D_formula hn i j
  simp only [Nat.dist] at hd
  by_cases hij : i.val ≤ j.val
  · by_cases hh : j.val - i.val ≤ n - (j.val - i.val)
    · refine ⟨(j.val : ℤ) - i.val, ?_, by push_cast; rfl⟩
      rw [abs_of_nonneg (by omega)]
      omega
    · refine ⟨(j.val : ℤ) - i.val - n, ?_, ?_⟩
      · rw [abs_of_nonpos (by omega)]
        omega
      · simp
  · by_cases hh : i.val - j.val ≤ n - (i.val - j.val)
    · refine ⟨(j.val : ℤ) - i.val, ?_, by push_cast; rfl⟩
      rw [abs_of_nonpos (by omega)]
      omega
    · refine ⟨(j.val : ℤ) - i.val + n, ?_, ?_⟩
      · rw [abs_of_nonneg (by omega)]
        omega
      · simp

theorem D_le_congruent {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) (z : ℤ)
    (hz : (z : ZMod n) = (j.val : ZMod n) - (i.val : ZMod n)) :
    (D i j : ℤ) ≤ |z| := by
  have hdiam := D_diameter hn i j
  by_cases hb : (n / 2 : ℕ) ≤ |z|
  · omega
  · obtain ⟨q, hq, hqc⟩ := signed_displacement hn i j
    have hc : ((q - z : ℤ) : ZMod n) = 0 := by
      push_cast
      rw [hqc, hz]
      ring
    have hsmall : |q - z| < (n : ℤ) := by
      have ht := abs_sub q z
      omega
    have he := no_wrap (by omega) hc hsmall
    have hqz : q = z := by omega
    rw [hqz] at hq
    omega

theorem antipode_cast {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    ((antipode hn i).val : ZMod n) = (i.val : ZMod n) + (n / 2 : ℕ) := by
  simp only [antipode, Fin.val_add]
  rw [ZMod.natCast_mod, Nat.cast_add]

/-- Near-antipodal vertices have the small error in equation (4). -/
theorem near_antipodal {n : ℕ} (hn : 3 ≤ n) (he : Even n)
    (i j : Fin n) (δ : ℤ) (hδ : (n / 2 : ℕ) - δ ≤ (D i j : ℤ)) :
    ∃ e : ℤ, |e| ≤ δ ∧
      (j.val : ZMod n) = (i.val : ZMod n) + (n / 2 : ℕ) + e := by
  obtain ⟨e, habs, hcong⟩ := signed_displacement hn (antipode hn i) j
  have hd := D_antipode hn he i j
  have hcast := antipode_cast hn i
  refine ⟨e, by omega, ?_⟩
  rw [hcast] at hcong
  rw [hcong]
  ring

#print axioms D_antipode
#print axioms D_translate
#print axioms signed_displacement
#print axioms D_le_congruent
#print axioms antipode_cast
#print axioms near_antipodal

end RadioCycles
```

### `RadioOrdinaryBound.lean`

```lean
import RadioCycleMetric
import RadioEndpoints

namespace RadioCycles

/-- Labels outside the sorted enumeration are irrelevant and set to zero. -/
def sortedValue {n : ℕ} (f : Fin n → ℕ) (x : Fin n ≃ Fin n) (t : ℕ) : ℤ :=
  if ht : t < n then (f (x ⟨t, ht⟩) : ℤ) else 0

def labelGap (F : ℕ → ℤ) (t : ℕ) : ℤ := F (t + 1) - F t

theorem sum_gap_pairs (F : ℕ → ℤ) (m : ℕ) :
    (∑ t ∈ Finset.range m, (labelGap F (2 * t) + labelGap F (2 * t + 1))) +
      labelGap F (2 * m) = F (2 * m + 1) - F 0 := by
  induction m with
  | zero => simp [labelGap]
  | succ m ih =>
    rw [Finset.sum_range_succ]
    simp only [labelGap] at ih ⊢
    have h1 : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [h1]
    linarith

theorem radio_injective {n k : ℕ} (hn : 3 ≤ n) (hk : n / 2 ≤ k)
    {f : Fin n → ℕ} (hf : Radio k f) : Function.Injective f := by
  exact radio_injective_of_distance_bound hf (fun i j => (D_diameter hn i j).trans hk)

theorem sorted_radio_gap {n k : ℕ} (hn : 3 ≤ n) {f : Fin n → ℕ} (hf : Radio k f)
    (x : Fin n ≃ Fin n) (hx : StrictMono (f ∘ x)) (t : ℕ) (ht : t + 1 < n) :
    (k : ℤ) + 1 - (n / 2 : ℕ) ≤ labelGap (sortedValue f x) t := by
  let i : Fin n := ⟨t, by omega⟩
  let j : Fin n := ⟨t + 1, ht⟩
  have hij : i < j := by change t < t + 1; omega
  have hlabels := hx hij
  have hne : x i ≠ x j := x.injective.ne (ne_of_lt hij)
  have hr := hf (x i) (x j) hne
  have hd := D_diameter hn (x i) (x j)
  have ha : |(f (x i) : ℤ) - f (x j)| = (f (x j) : ℤ) - f (x i) := by
    rw [abs_of_nonpos (by change f (x i) < f (x j) at hlabels; omega)]
    ring
  rw [ha] at hr
  simpa [labelGap, sortedValue, show t < n by omega, ht, i, j] using
    (show (k : ℤ) + 1 - (n / 2 : ℕ) ≤ (f (x j) : ℤ) - f (x i) by omega)

theorem sorted_radio_pair {n k : ℕ} (hn : 3 ≤ n) {f : Fin n → ℕ} (hf : Radio k f)
    (x : Fin n ≃ Fin n) (hx : StrictMono (f ∘ x)) (t : ℕ) (ht : t + 2 < n) :
    (3 * (k : ℤ) + 3 - n) ≤
      2 * (labelGap (sortedValue f x) t + labelGap (sortedValue f x) (t + 1)) := by
  let i : Fin n := ⟨t, by omega⟩
  let j : Fin n := ⟨t + 1, by omega⟩
  let l : Fin n := ⟨t + 2, ht⟩
  have hij : i < j := by change t < t + 1; omega
  have hjl : j < l := by change t + 1 < t + 2; omega
  have hil := lt_trans hij hjl
  have h1 := hf (x i) (x j) (x.injective.ne (ne_of_lt hij))
  have h2 := hf (x j) (x l) (x.injective.ne (ne_of_lt hjl))
  have h3 := hf (x i) (x l) (x.injective.ne (ne_of_lt hil))
  have hD := D_perimeter hn (x i) (x j) (x l)
  have hfi : (f (x i) : ℤ) ≤ f (x j) := by have := hx hij; change f (x i) < f (x j) at this; omega
  have hfj : (f (x j) : ℤ) ≤ f (x l) := by have := hx hjl; change f (x j) < f (x l) at this; omega
  rw [abs_of_nonpos (by omega)] at h1 h2 h3
  simp only [labelGap, sortedValue, show t < n by omega,
    show t + 1 < n by omega, show t + 1 + 1 < n by omega]
  change 3 * (k : ℤ) + 3 - n ≤
    2 * (((f (x j) : ℤ) - f (x i)) + ((f (x l) : ℤ) - f (x j)))
  omega

theorem sorted_span {n : ℕ} (hn : 0 < n) (f : Fin n → ℕ)
    (x : Fin n ≃ Fin n) (hx : StrictMono (f ∘ x)) :
    (span f : ℤ) = sortedValue f x (n - 1) - sortedValue f x 0 := by
  let i : Fin n := ⟨0, hn⟩
  let j : Fin n := ⟨n - 1, by omega⟩
  have hmin : ∀ v, f (x i) ≤ f v := by
    intro v
    have h := hx.monotone (show i ≤ x.symm v by exact Nat.zero_le _)
    simpa [Function.comp_def] using h
  have hmax : Finset.univ.sup f = f (x j) := by
    apply le_antisymm
    · apply Finset.sup_le
      intro v _
      have h := hx.monotone (show x.symm v ≤ j by change (x.symm v).val ≤ n - 1; have := (x.symm v).isLt; omega)
      simpa [Function.comp_def] using h
    · exact Finset.le_sup (Finset.mem_univ _)
  rw [span_eq_max_sub_min f (x i) hmin, hmax]
  have hle := hmin (x j)
  simp only [sortedValue, show n - 1 < n by omega, hn]
  dsimp [i, j] at *
  omega

/-- The source's ordinary lower bound, for every literal labeling. -/
theorem radio_span_lowerBound {n k : ℕ} (hn : Even n) (hk : Odd k)
    (hlo : n / 2 ≤ k) (hhi : k < n - 3) {f : Fin n → ℕ} (hf : Radio k f) :
    lowerBound n k ≤ span f := by
  have hp := parameter_arithmetic n k hn hk hlo hhi
  obtain ⟨x, hx⟩ := sorted_labeling f (radio_injective hp.1 hlo hf)
  let F := sortedValue f x
  let d := n / 2
  let h := hParam n k
  let Φ : ℤ := 2 * (d : ℤ) - 3 * h
  let a : ℤ := (d : ℤ) - 2 * h
  have hdn : n = 2 * d := hp.2.2.1
  have hkz : (k : ℤ) + 1 + 2 * h = n := by exact_mod_cast hp.2.2.2.1
  have hdnz : (n : ℤ) = 2 * (d : ℤ) := by exact_mod_cast hdn
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hpair : ∀ t ∈ Finset.range (d - 1), Φ ≤ labelGap F (2 * t) + labelGap F (2 * t + 1) := by
    intro t ht
    have ht' := Finset.mem_range.mp ht
    have hg := sorted_radio_pair hp.1 hf x hx (2 * t) (by omega)
    dsimp [Φ, F]
    omega
  have hsum : ((d - 1 : ℕ) : ℤ) * Φ ≤
      ∑ t ∈ Finset.range (d - 1), (labelGap F (2 * t) + labelGap F (2 * t + 1)) := by
    calc
      _ = ∑ _t ∈ Finset.range (d - 1), Φ := by simp
      _ ≤ _ := Finset.sum_le_sum hpair
  have hlast : a ≤ labelGap F (2 * (d - 1)) := by
    have hg := sorted_radio_gap hp.1 hf x hx (2 * (d - 1)) (by omega)
    dsimp [a, F, d] at *
    omega
  have htel := sum_gap_pairs F (d - 1)
  have hindex : 2 * (d - 1) + 1 = n - 1 := by omega
  rw [hindex, ← sorted_span (by omega) f x hx] at htel
  have hlb := lowerBoundInt_formula n k hn hk hlo hhi
  have hlbc := lowerBound_cast n k hn hk hlo hhi
  have hdcast : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  dsimp [Φ, a, d, h] at *
  nlinarith

#print axioms radio_injective
#print axioms sorted_radio_gap
#print axioms sorted_radio_pair
#print axioms sorted_span
#print axioms sum_gap_pairs
#print axioms radio_span_lowerBound

end RadioCycles
```

### `RadioSlackExtraction.lean`

```lean
import RadioOrdinaryBound

namespace RadioCycles

def evenSlack (F : ℕ → ℤ) (a : ℤ) (t : ℕ) : ℤ := labelGap F (2 * t) - a

def pairSlack (F : ℕ → ℤ) (Φ : ℤ) (t : ℕ) : ℤ :=
  labelGap F (2 * t) + labelGap F (2 * t + 1) - Φ

def offsetSlack (F : ℕ → ℤ) (Φ : ℤ) (t : ℕ) : ℤ :=
  labelGap F (2 * t + 1) + labelGap F (2 * t + 2) - Φ

theorem extracted_slack_relation (F : ℕ → ℤ) (a Φ : ℤ) (t : ℕ) :
    offsetSlack F Φ t = pairSlack F Φ t + evenSlack F a (t + 1) - evenSlack F a t := by
  simp only [offsetSlack, pairSlack, evenSlack]
  have hi : 2 * (t + 1) = 2 * t + 2 := by omega
  rw [hi]
  ring

theorem extracted_slack_budget (F : ℕ → ℤ) (a Φ : ℤ) (m : ℕ) :
    F (2 * m + 1) - F 0 - ((m : ℤ) * Φ + a) =
      (∑ t ∈ Finset.range m, pairSlack F Φ t) + evenSlack F a m := by
  have ht := sum_gap_pairs F m
  simp only [pairSlack, evenSlack, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  linarith

/-- A literal arbitrary radio labeling supplies all the scalar slack data
in equations (1)--(3) of the written proof, without any extra graph hypothesis. -/
theorem radio_slack_extraction {n k : ℕ} (hn : Even n) (hk : Odd k)
    (hlo : n / 2 ≤ k) (hhi : k < n - 3) {f : Fin n → ℕ} (hf : Radio k f) :
    ∃ x : Fin n ≃ Fin n,
      StrictMono (f ∘ x) ∧
      let F := sortedValue f x
      let a : ℤ := (n / 2 : ℕ) - 2 * (hParam n k : ℤ)
      let Φ : ℤ := 2 * (n / 2 : ℕ) - 3 * (hParam n k : ℤ)
      let m := n / 2 - 1
      let s : ℤ := (span f : ℤ) - lowerBoundInt n k
      (∀ t < m, 0 ≤ pairSlack F Φ t) ∧
      (∀ t < m, 0 ≤ offsetSlack F Φ t) ∧
      (∀ t ≤ m, 0 ≤ evenSlack F a t) ∧
      (∀ t < m, offsetSlack F Φ t =
        pairSlack F Φ t + evenSlack F a (t + 1) - evenSlack F a t) ∧
      s = (∑ t ∈ Finset.range m, pairSlack F Φ t) + evenSlack F a m := by
  have hp := parameter_arithmetic n k hn hk hlo hhi
  obtain ⟨x, hx⟩ := sorted_labeling f (radio_injective hp.1 hlo hf)
  refine ⟨x, hx, ?_⟩
  dsimp only
  have hn2 := hp.2.2.1
  have hk2 := hp.2.2.2.1
  have hnz : (n : ℤ) = 2 * (n / 2 : ℕ) := by exact_mod_cast hn2
  have hkz : (k : ℤ) + 1 + 2 * hParam n k = n := by exact_mod_cast hk2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have hg := sorted_radio_pair hp.1 hf x hx (2 * t) (by omega)
    dsimp [pairSlack]
    omega
  · intro t ht
    have hg := sorted_radio_pair hp.1 hf x hx (2 * t + 1) (by omega)
    have hi : 2 * t + 1 + 1 = 2 * t + 2 := by omega
    rw [hi] at hg
    dsimp [offsetSlack]
    omega
  · intro t ht
    have hg := sorted_radio_gap hp.1 hf x hx (2 * t) (by omega)
    dsimp [evenSlack]
    omega
  · intro t _
    exact extracted_slack_relation _ _ _ t
  · have hb := extracted_slack_budget (sortedValue f x)
      ((n / 2 : ℕ) - 2 * (hParam n k : ℤ))
      (2 * (n / 2 : ℕ) - 3 * (hParam n k : ℤ)) (n / 2 - 1)
    have hi : 2 * (n / 2 - 1) + 1 = n - 1 := by omega
    rw [hi, ← sorted_span (by omega) f x hx] at hb
    have hlb := lowerBoundInt_formula n k hn hk hlo hhi
    have hc : ((n / 2 - 1 : ℕ) : ℤ) = (n / 2 : ℕ) - 1 := by omega
    rw [hc] at hb
    linarith

#print axioms extracted_slack_relation
#print axioms extracted_slack_budget
#print axioms radio_slack_extraction

end RadioCycles
```

### `RadioNearSteps.lean`

```lean
import RadioCycleGeometry
import RadioSlackExtraction

namespace RadioCycles

/-- The radio inequality with its absolute value removed in sorted order. -/
theorem sorted_radio_separation {n k : ℕ} {f : Fin n → ℕ} (hf : Radio k f)
    (x : Fin n ≃ Fin n) (hx : StrictMono (f ∘ x))
    (i j : ℕ) (hij : i < j) (hj : j < n) :
    (k : ℤ) + 1 - D (x ⟨i, by omega⟩) (x ⟨j, hj⟩) ≤
      sortedValue f x j - sortedValue f x i := by
  have hlt : (⟨i, by omega⟩ : Fin n) < ⟨j, hj⟩ := hij
  have hfi := hx hlt
  have hr := hf (x ⟨i, by omega⟩) (x ⟨j, hj⟩) (x.injective.ne (ne_of_lt hlt))
  change f (x ⟨i, by omega⟩) < f (x ⟨j, hj⟩) at hfi
  rw [abs_of_nonpos (by omega)] at hr
  simp only [sortedValue, hj, show i < n by omega, dite_true]
  omega

/-- Equations (5) and (6), derived directly from five literal radio
inequalities and the even-cycle antipodal identity. -/
theorem near_step_bounds {n k h : ℕ} (hn : 3 ≤ n) (he : Even n)
    (hk : k + 1 + 2 * h = n)
    (v w v' w' : Fin n) (E O E' : ℤ)
    (hE : (k : ℤ) + 1 - D v w ≤ E)
    (hO : (k : ℤ) + 1 - D w v' ≤ O)
    (hE' : (k : ℤ) + 1 - D v' w' ≤ E')
    (hV : (k : ℤ) + 1 - D v v' ≤ E + O)
    (hW : (k : ℤ) + 1 - D w w' ≤ O + E') :
    let Φ : ℤ := 2 * (n / 2 : ℕ) - 3 * (h : ℤ)
    let ε := E + O - Φ
    let η := O + E' - Φ
    ((h : ℤ) - ε ≤ D v v' ∧ (D v v' : ℤ) ≤ h + ε) ∧
    ((h : ℤ) - η ≤ D w w' ∧ (D w w' : ℤ) ≤ h + η) := by
  dsimp only
  obtain ⟨d, hd⟩ := he
  have hn2 : n = 2 * d := by omega
  have hhalf : n / 2 = d := by omega
  have hnz : (n : ℤ) = 2 * (d : ℤ) := by exact_mod_cast hn2
  have hkz : (k : ℤ) + 1 + 2 * h = n := by exact_mod_cast hk
  have hA := D_antipode hn ⟨d, hd⟩ v w
  have hB := D_antipode hn ⟨d, hd⟩ v v'
  have hC := D_antipode hn ⟨d, hd⟩ v' w
  have hD := D_antipode hn ⟨d, hd⟩ v' w'
  have htV := D_triangle (by omega) w (antipode hn v) v'
  have htW := D_triangle (by omega) w (antipode hn v') w'
  rw [D_comm w (antipode hn v)] at htV
  rw [D_comm w (antipode hn v')] at htW
  rw [D_comm v' w] at hC
  rw [hhalf] at *
  omega

/-- Removing the sign of a shortest step does not lose its small error. -/
theorem signed_step_error (q h ε : ℤ) (_hε : 0 ≤ ε) (_hpos : ε < h)
    (hlo : h - ε ≤ |q|) (hhi : |q| ≤ h + ε) :
    ∃ σ u : ℤ, (σ = -1 ∨ σ = 1) ∧ q = σ * h + u ∧ |u| ≤ ε := by
  by_cases hq : 0 ≤ q
  · refine ⟨1, q - h, Or.inr rfl, by ring, ?_⟩
    rw [abs_of_nonneg hq] at hlo hhi
    exact abs_le.mpr ⟨by omega, by omega⟩
  · refine ⟨-1, q + h, Or.inl rfl, by ring, ?_⟩
    rw [abs_of_nonpos (by omega)] at hlo hhi
    exact abs_le.mpr ⟨by omega, by omega⟩

#print axioms sorted_radio_separation
#print axioms near_step_bounds
#print axioms signed_step_error

end RadioCycles
```

### `RadioEnumeration.lean`

```lean
import RadioNearSteps

namespace RadioCycles

def enumVertex {n : ℕ} (hn : 0 < n) (x : Fin n ≃ Fin n) (t : ℕ) : Fin n :=
  x ⟨t % n, Nat.mod_lt _ hn⟩

theorem enum_radio_separation {n k : ℕ} (hn : 0 < n) {f : Fin n → ℕ} (hf : Radio k f)
    (x : Fin n ≃ Fin n) (hx : StrictMono (f ∘ x))
    (i j : ℕ) (hij : i < j) (hj : j < n) :
    (k : ℤ) + 1 - D (enumVertex hn x i) (enumVertex hn x j) ≤
      sortedValue f x j - sortedValue f x i := by
  simpa only [enumVertex, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (lt_trans hij hj)] using
    sorted_radio_separation hf x hx i j hij hj

/-- An enumeration of every cycle vertex covers every residue modulo a
positive divisor, including when split into its even and odd positions. -/
theorem enum_residue_cover {n p : ℕ} (hn : 0 < n) (he : Even n)
    (hp : 0 < p) (hpn : p ∣ n) (x : Fin n ≃ Fin n) :
    ∀ r : ZMod p, ∃ t ≤ n / 2 - 1,
      (((enumVertex hn x (2 * t)).val : ℕ) : ZMod p) = r ∨
      (((enumVertex hn x (2 * t + 1)).val : ℕ) : ZMod p) = r := by
  let : NeZero p := ⟨by omega⟩
  intro r
  have hpn' : p ≤ n := Nat.le_of_dvd hn hpn
  let v : Fin n := ⟨r.val, lt_of_lt_of_le (ZMod.val_lt r) hpn'⟩
  let j := x.symm v
  obtain ⟨d, hd⟩ := he
  have hn2 : n = 2 * d := by omega
  have hj : j.val < n := j.isLt
  refine ⟨j.val / 2, by omega, ?_⟩
  have hrem : j.val % 2 = 0 ∨ j.val % 2 = 1 := by omega
  rcases hrem with hh | hh
  · left
    have hi : 2 * (j.val / 2) = j.val := by omega
    simp only [hi, enumVertex, Nat.mod_eq_of_lt hj]
    have heq : x ⟨j.val, hj⟩ = v := x.apply_symm_apply v
    rw [heq]
    exact ZMod.natCast_zmod_val r
  · right
    have hi : 2 * (j.val / 2) + 1 = j.val := by omega
    simp only [hi, enumVertex, Nat.mod_eq_of_lt hj]
    have heq : x ⟨j.val, hj⟩ = v := x.apply_symm_apply v
    rw [heq]
    exact ZMod.natCast_zmod_val r

#print axioms enum_radio_separation
#print axioms enum_residue_cover

end RadioCycles
```

### `RadioModularLifts.lean`

```lean
import RadioLiftObstruction
import RadioTracks

namespace RadioCycles

theorem reduce_congruence {n p : ℕ} (hpn : p ∣ n) {a b : ℤ}
    (hab : (a : ZMod n) = (b : ZMod n)) : (a : ZMod p) = (b : ZMod p) := by
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).mpr
  exact dvd_trans (by exact_mod_cast hpn) ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).mp hab)

/-- The lift and residue portion of the lower bound, with actual modular
vertex tracks and signed shortest-step data as inputs. -/
theorem modular_track_obstruction (n p h d s m : ℕ) (hp : 0 < p)
    (hpn : p ∣ n) (hph : p ∣ h) (hpd : p ∣ d)
    (hsmall : s < h) (hsize : 4 * h < n)
    (v w ε η δ e σ τ u b : ℕ → ℤ)
    (hε : ∀ t < m, 0 ≤ ε t) (hη : ∀ t < m, 0 ≤ η t)
    (hδ : ∀ t ≤ m, 0 ≤ δ t)
    (hrel : ∀ t < m, η t = ε t + δ (t + 1) - δ t)
    (hbudget : (s : ℤ) = (∑ t ∈ Finset.range m, ε t) + δ m)
    (he : ∀ t ≤ m, |e t| ≤ δ t)
    (hec : ∀ t ≤ m, (w t : ZMod n) = (v t : ZMod n) + (d : ℕ) + e t)
    (hσ : ∀ t < m, σ t = -1 ∨ σ t = 1)
    (hτ : ∀ t < m, τ t = -1 ∨ τ t = 1)
    (hu : ∀ t < m, |u t| ≤ ε t) (hb : ∀ t < m, |b t| ≤ η t)
    (hqc : ∀ t < m, ((σ t * (h : ℤ) + u t : ℤ) : ZMod n) =
      (v (t + 1) : ZMod n) - (v t : ZMod n))
    (hrc : ∀ t < m, ((τ t * (h : ℤ) + b t : ℤ) : ZMod n) =
      (w (t + 1) : ZMod n) - (w t : ZMod n))
    (hcover : ∀ r : ZMod p, ∃ t ≤ m, (v t : ZMod p) = r ∨ (w t : ZMod p) = r) :
    p ≤ s + 1 := by
  have hs := slack_bounds ε η δ m s hε hη hδ hrel hbudget
  have hsign : ∀ t < m, τ t = σ t ∧ b t - u t = e (t + 1) - e t := by
    intro t ht
    apply same_direction n h s (ε t) (η t) (δ t) (δ (t + 1))
      (e t) (e (t + 1)) (u t) (b t) (σ t) (τ t)
      (by exact_mod_cast hsmall) (by exact_mod_cast hsize)
      (hε t ht) (hη t ht) (hδ t (by omega)) (hδ (t + 1) (by omega))
      (hrel t ht) (hs.2.1 t ht) (he t (by omega)) (he (t + 1) (by omega))
      (hu t ht) (hb t ht) (hσ t ht) (hτ t ht)
    have hQ := hqc t ht
    have hR := hrc t ht
    have hE := hec t (by omega)
    have hE' := hec (t + 1) (by omega)
    push_cast at hQ hR ⊢
    rw [hQ, hR, hE, hE']
    ring
  let V : ℕ → ℤ := fun t => ∑ i ∈ Finset.range t, u i
  let W : ℕ → ℤ := fun t => e 0 + ∑ i ∈ Finset.range t, b i
  have hV0 : V 0 = 0 := by simp [V]
  have hW0 : W 0 = e 0 := by simp [W]
  have hVstep : ∀ t < m, V (t + 1) = V t + u t := by
    intro t _; simp [V, Finset.sum_range_succ]
  have hWstep : ∀ t < m, W (t + 1) = W t + b t := by
    intro t _; simp [W, Finset.sum_range_succ]; ring
  have hdiff := lift_difference V W e u b m hV0 hW0 hVstep hWstep
    (fun t ht => (hsign t ht).2)
  have hh0 : ((h : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff h p).mpr hph
  have hd0 : ((d : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff d p).mpr hpd
  have hVc : ∀ t ≤ m, (V t : ZMod p) = (v t : ZMod p) - (v 0 : ZMod p) := by
    intro t ht
    induction t with
    | zero => simp [hV0]
    | succ t ih =>
      have ht' : t < m := by omega
      have hQ := reduce_congruence hpn (a := σ t * (h : ℤ) + u t)
        (b := v (t + 1) - v t) (by simpa only [Int.cast_sub] using hqc t ht')
      push_cast at hQ
      simp only [hh0, mul_zero, zero_add] at hQ
      rw [hVstep t ht', Int.cast_add, ih (by omega), hQ]
      ring
  have hWc : ∀ t ≤ m, (W t : ZMod p) = (w t : ZMod p) - (v 0 : ZMod p) := by
    intro t ht
    have hE := reduce_congruence hpn (a := w t) (b := v t + (d : ℤ) + e t)
      (by simpa only [Int.cast_add, Int.cast_natCast] using hec t ht)
    push_cast at hE
    simp only [hd0, add_zero] at hE
    have hD := congrArg (fun z : ℤ => (z : ZMod p)) (hdiff t ht)
    rw [Int.cast_sub] at hD
    calc
      (W t : ZMod p) = (V t : ZMod p) + (e t : ZMod p) := (by simpa [add_comm] using (sub_eq_iff_eq_add.mp hD))
      _ = (w t : ZMod p) - (v 0 : ZMod p) := by rw [hVc t ht, hE]; ring
  apply two_track_residue_bound p s m hp V W ε η δ hε hη hδ hrel hbudget
  · intro t ht
    rw [hVstep t ht]
    simpa using hu t ht
  · intro t ht
    rw [hWstep t ht]
    simpa using hb t ht
  · rw [hW0, hV0, sub_zero]
    exact he 0 (by omega)
  · rw [hdiff m le_rfl]
    exact he m le_rfl
  · intro r
    obtain ⟨t, ht, hcov⟩ := hcover (r + (v 0 : ZMod p))
    refine ⟨t, ht, ?_⟩
    rcases hcov with hc | hc
    · left; rw [hVc t ht, hc]; ring
    · right; rw [hWc t ht, hc]; ring

#print axioms reduce_congruence
#print axioms modular_track_obstruction

end RadioCycles
```

### `RadioGeometricObstruction.lean`

```lean
import RadioNearSteps
import RadioModularLifts
import Mathlib.Tactic.Choose

namespace RadioCycles

theorem short_step_data {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) (h ε : ℤ)
    (hε : 0 ≤ ε) (hsmall : ε < h)
    (hlo : h - ε ≤ D i j) (hhi : (D i j : ℤ) ≤ h + ε) :
    ∃ σ u : ℤ, (σ = -1 ∨ σ = 1) ∧ |u| ≤ ε ∧
      ((σ * h + u : ℤ) : ZMod n) = (j.val : ZMod n) - (i.val : ZMod n) := by
  obtain ⟨q, hq, hqc⟩ := signed_displacement hn i j
  obtain ⟨σ, u, hσ, hqu, hu⟩ := signed_step_error q h ε hε hsmall (by omega) (by omega)
  exact ⟨σ, u, hσ, hu, hqu ▸ hqc⟩

/-- The integer-lift obstruction applied to actual vertices with the
near-antipodal and two-step distance estimates proved from the radio inequalities. -/
theorem geometric_track_obstruction (n p h s m : ℕ) (hn : 3 ≤ n) (heven : Even n)
    (hp : 0 < p) (hpn : p ∣ n) (hph : p ∣ h) (hpd : p ∣ n / 2)
    (hsmall : s < h) (hsize : 4 * h < n)
    (v w : ℕ → Fin n) (ε η δ : ℕ → ℤ)
    (hε : ∀ t < m, 0 ≤ ε t) (hη : ∀ t < m, 0 ≤ η t)
    (hδ : ∀ t ≤ m, 0 ≤ δ t)
    (hrel : ∀ t < m, η t = ε t + δ (t + 1) - δ t)
    (hbudget : (s : ℤ) = (∑ t ∈ Finset.range m, ε t) + δ m)
    (hpair : ∀ t ≤ m, (n / 2 : ℕ) - δ t ≤ (D (v t) (w t) : ℤ))
    (hV : ∀ t < m, (h : ℤ) - ε t ≤ D (v t) (v (t + 1)) ∧
      (D (v t) (v (t + 1)) : ℤ) ≤ h + ε t)
    (hW : ∀ t < m, (h : ℤ) - η t ≤ D (w t) (w (t + 1)) ∧
      (D (w t) (w (t + 1)) : ℤ) ≤ h + η t)
    (hcover : ∀ r : ZMod p, ∃ t ≤ m,
      ((v t).val : ZMod p) = r ∨ ((w t).val : ZMod p) = r) : p ≤ s + 1 := by
  classical
  have hs := slack_bounds ε η δ m s hε hη hδ hrel hbudget
  have hex : ∀ t : ℕ, ∃ e : ℤ, t ≤ m → |e| ≤ δ t ∧
      ((w t).val : ZMod n) = ((v t).val : ZMod n) + (n / 2 : ℕ) + e := by
    intro t
    by_cases ht : t ≤ m
    · obtain ⟨e, he, hc⟩ := near_antipodal hn heven (v t) (w t) (δ t) (hpair t ht)
      exact ⟨e, fun _ => ⟨he, hc⟩⟩
    · exact ⟨0, fun h => False.elim (ht h)⟩
  choose e he using hex
  have hqx : ∀ t : ℕ, ∃ σ u : ℤ, t < m → (σ = -1 ∨ σ = 1) ∧ |u| ≤ ε t ∧
      ((σ * (h : ℤ) + u : ℤ) : ZMod n) =
        ((v (t + 1)).val : ZMod n) - ((v t).val : ZMod n) := by
    intro t
    by_cases ht : t < m
    · have hb := hs.2.1 t ht
      have hz := hδ (t + 1) (by omega)
      have hεsmall : ε t < (h : ℤ) := by omega
      obtain ⟨σ, u, hσ, hu, hc⟩ := short_step_data hn (v t) (v (t + 1)) h (ε t)
        (hε t ht) hεsmall (hV t ht).1 (hV t ht).2
      exact ⟨σ, u, fun _ => ⟨hσ, hu, hc⟩⟩
    · exact ⟨1, 0, fun h => False.elim (ht h)⟩
  choose σ u hq using hqx
  have hrx : ∀ t : ℕ, ∃ τ b : ℤ, t < m → (τ = -1 ∨ τ = 1) ∧ |b| ≤ η t ∧
      ((τ * (h : ℤ) + b : ℤ) : ZMod n) =
        ((w (t + 1)).val : ZMod n) - ((w t).val : ZMod n) := by
    intro t
    by_cases ht : t < m
    · have hb := hs.2.2.2 t ht
      have hηsmall : η t < (h : ℤ) := by omega
      obtain ⟨τ, b, hτ, hb, hc⟩ := short_step_data hn (w t) (w (t + 1)) h (η t)
        (hη t ht) hηsmall (hW t ht).1 (hW t ht).2
      exact ⟨τ, b, fun _ => ⟨hτ, hb, hc⟩⟩
    · exact ⟨1, 0, fun h => False.elim (ht h)⟩
  choose τ b hr using hrx
  apply modular_track_obstruction n p h (n / 2) s m hp hpn hph hpd hsmall hsize
    (fun t => ((v t).val : ℤ)) (fun t => ((w t).val : ℤ)) ε η δ e σ τ u b
    hε hη hδ hrel hbudget
  · intro t ht; exact (he t ht).1
  · intro t ht; simpa only [Int.cast_natCast] using (he t ht).2
  · intro t ht; exact (hq t ht).1
  · intro t ht; exact (hr t ht).1
  · intro t ht; exact (hq t ht).2.1
  · intro t ht; exact (hr t ht).2.1
  · intro t ht; simpa only [Int.cast_natCast] using (hq t ht).2.2
  · intro t ht; simpa only [Int.cast_natCast] using (hr t ht).2.2
  · simpa only [Int.cast_natCast] using hcover

#print axioms short_step_data
#print axioms geometric_track_obstruction

end RadioCycles
```

### `RadioSharpLower.lean`

```lean
import RadioEnumeration
import RadioGeometricObstruction

namespace RadioCycles

/-- The universal sharp lower bound, for every labeling and all admissible
parameters satisfying the literal source subgroup hypothesis. -/
theorem radio_span_sharp_lower {n k : ℕ} (hn : Even n) (hk : Odd k)
    (hlo : n / 2 ≤ k) (hhi : k < n - 3)
    (hsub : ((n / 2 : ℕ) : ZMod n) ∈ AddSubgroup.zmultiples (hParam n k : ZMod n))
    {f : Fin n → ℕ} (hf : Radio k f) :
    lowerBound n k + pParam n k - 1 ≤ span f := by
  have hpar := parameter_arithmetic n k hn hk hlo hhi
  have hn0 : 0 < n := by omega
  have hn2 := hpar.2.2.1
  have hk2 := hpar.2.2.2.1
  have hnz : (n : ℤ) = 2 * (n / 2 : ℕ) := by exact_mod_cast hn2
  have hkz : (k : ℤ) + 1 + 2 * hParam n k = n := by exact_mod_cast hk2
  have hp : 0 < pParam n k := by
    exact Nat.gcd_pos_of_pos_left (hParam n k) hn0
  have hpn : pParam n k ∣ n := Nat.gcd_dvd_left _ _
  have hph : pParam n k ∣ hParam n k := Nat.gcd_dvd_right _ _
  have hpd : pParam n k ∣ n / 2 := (mem_zmultiples_iff_gcd_dvd _ _ _).mp hsub
  have hbase := radio_span_lowerBound hn hk hlo hhi hf
  by_contra hbad
  have hbad' : span f < lowerBound n k + pParam n k - 1 := by omega
  let s := span f - lowerBound n k
  have hsmall : s < hParam n k := by dsimp [s]; have := hpar.2.2.2.2.2.2.2; omega
  have hsize : 4 * hParam n k < n := hpar.2.2.2.2.2.1
  obtain ⟨x, hx, hε, hη, hδ, hrel, hbudget⟩ := radio_slack_extraction hn hk hlo hhi hf
  let F := sortedValue f x
  let a : ℤ := (n / 2 : ℕ) - 2 * (hParam n k : ℤ)
  let Φ : ℤ := 2 * (n / 2 : ℕ) - 3 * (hParam n k : ℤ)
  let m := n / 2 - 1
  let ε := pairSlack F Φ
  let η := offsetSlack F Φ
  let δ := evenSlack F a
  let v : ℕ → Fin n := fun t => enumVertex hn0 x (2 * t)
  let w : ℕ → Fin n := fun t => enumVertex hn0 x (2 * t + 1)
  have hscast : (s : ℤ) = (span f : ℤ) - lowerBoundInt n k := by
    have := lowerBound_cast n k hn hk hlo hhi
    dsimp [s]
    omega
  change (span f : ℤ) - lowerBoundInt n k = (∑ t ∈ Finset.range m, ε t) + δ m at hbudget
  rw [← hscast] at hbudget
  have hpair : ∀ t ≤ m, (n / 2 : ℕ) - δ t ≤ (D (v t) (w t) : ℤ) := by
    intro t ht
    have hr := enum_radio_separation hn0 hf x hx (2 * t) (2 * t + 1) (by omega) (by dsimp [m] at ht; omega)
    change (k : ℤ) + 1 - D (v t) (w t) ≤ F (2 * t + 1) - F (2 * t) at hr
    dsimp [δ, evenSlack, labelGap, a]
    omega
  have hsteps : ∀ t < m,
      (((hParam n k : ℕ) : ℤ) - ε t ≤ D (v t) (v (t + 1)) ∧
        (D (v t) (v (t + 1)) : ℤ) ≤ hParam n k + ε t) ∧
      (((hParam n k : ℕ) : ℤ) - η t ≤ D (w t) (w (t + 1)) ∧
        (D (w t) (w (t + 1)) : ℤ) ≤ hParam n k + η t) := by
    intro t ht
    have hindex : 2 * (t + 1) = 2 * t + 2 := by omega
    have hindex' : 2 * t + 2 + 1 = 2 * t + 3 := by omega
    have hend : 2 * t + 3 < n := by dsimp [m] at ht; omega
    have hE := enum_radio_separation hn0 hf x hx (2 * t) (2 * t + 1) (by omega) (by omega)
    have hO := enum_radio_separation hn0 hf x hx (2 * t + 1) (2 * t + 2) (by omega) (by omega)
    have hE' := enum_radio_separation hn0 hf x hx (2 * t + 2) (2 * t + 3) (by omega) hend
    have hV := enum_radio_separation hn0 hf x hx (2 * t) (2 * t + 2) (by omega) (by omega)
    have hW := enum_radio_separation hn0 hf x hx (2 * t + 1) (2 * t + 3) (by omega) hend
    have hE0 : (k : ℤ) + 1 - D (v t) (w t) ≤ labelGap F (2 * t) := hE
    have hO0 : (k : ℤ) + 1 - D (w t) (v (t + 1)) ≤ labelGap F (2 * t + 1) := by
      dsimp [v, w, labelGap, F]
      rw [hindex]
      exact hO
    have hE0' : (k : ℤ) + 1 - D (v (t + 1)) (w (t + 1)) ≤ labelGap F (2 * t + 2) := by
      dsimp [v, w, labelGap, F]
      rw [hindex, hindex']
      exact hE'
    have hV0 : (k : ℤ) + 1 - D (v t) (v (t + 1)) ≤ labelGap F (2 * t) + labelGap F (2 * t + 1) := by
      dsimp [v, labelGap, F]
      rw [hindex]
      linarith
    have hW0 : (k : ℤ) + 1 - D (w t) (w (t + 1)) ≤ labelGap F (2 * t + 1) + labelGap F (2 * t + 2) := by
      dsimp [w, labelGap, F]
      rw [hindex, hindex']
      linarith
    exact near_step_bounds hpar.1 hn hk2 (v t) (w t) (v (t + 1)) (w (t + 1))
      (labelGap F (2 * t)) (labelGap F (2 * t + 1)) (labelGap F (2 * t + 2))
      hE0 hO0 hE0' hV0 hW0
  have hob := geometric_track_obstruction n (pParam n k) (hParam n k) s m hpar.1 hn
    hp hpn hph hpd hsmall hsize v w ε η δ hε hη hδ hrel hbudget hpair
    (fun t ht => (hsteps t ht).1) (fun t ht => (hsteps t ht).2)
    (enum_residue_cover hn0 hn hp hpn x)
  dsimp [s] at hob
  omega

/-- The lower half of the literal radio-number equality. -/
theorem radioKNumber_sharp_lower {n k : ℕ} (hn : Even n) (hk : Odd k)
    (hlo : n / 2 ≤ k) (hhi : k < n - 3)
    (hsub : ((n / 2 : ℕ) : ZMod n) ∈ AddSubgroup.zmultiples (hParam n k : ZMod n)) :
    lowerBound n k + pParam n k - 1 ≤ radioKNumber n k := by
  apply (le_radioKNumber_iff _ _ _).mpr
  intro f hf
  exact radio_span_sharp_lower hn hk hlo hhi hsub hf

#print axioms radio_span_sharp_lower
#print axioms radioKNumber_sharp_lower

end RadioCycles
```

### `RadioConstructionArithmetic.lean`

```lean
import RadioSharpLower

namespace RadioCycles

/-- Orbit length and half-orbit of h, as used by construction (11). -/
theorem construction_orbit_parameters (n d h : ℕ) (hn : n = 2 * d) (hd0 : 0 < d)
    (hpd : Nat.gcd n h ∣ d) :
    ∃ q : ℕ, 0 < q ∧ d = Nat.gcd n h * q ∧
      addOrderOf (h : ZMod n) = 2 * q ∧
      (q : ZMod n) * (h : ZMod n) = (d : ZMod n) := by
  let p := Nat.gcd n h
  have hn0 : 0 < n := by omega
  have hp : 0 < p := Nat.gcd_pos_of_pos_left h hn0
  obtain ⟨q, hd⟩ := hpd
  obtain ⟨r, hh⟩ := Nat.gcd_dvd_right n h
  change d = p * q at hd
  change h = p * r at hh
  have hq : 0 < q := by nlinarith
  have hn' : n = p * (2 * q) := by rw [hn, hd]; ring
  have hg : Nat.gcd (2 * q) r = 1 := by
    have heq : p * Nat.gcd (2 * q) r = p * 1 := by
      rw [← Nat.gcd_mul_left, ← hn', ← hh]
      simp [p]
    exact Nat.mul_left_cancel hp heq
  have hc : Nat.Coprime (2 * q) r := hg
  have hodd : Odd r := (hc.of_dvd_left (dvd_mul_right 2 q)).odd_of_left
  obtain ⟨u, hu⟩ := hodd
  have hqh : q * h = d + n * u := by rw [hh, hd, hn', hu]; ring
  refine ⟨q, hq, hd, ?_, ?_⟩
  · rw [ZMod.addOrderOf_coe h (by omega)]
    change n / p = 2 * q
    rw [hn', Nat.mul_div_cancel_left _ hp]
  · have heq := congrArg (fun a : ℕ => (a : ZMod n)) hqh
    simpa using heq

/-- Equality of multiples of h forces divisibility by its exact orbit length. -/
theorem orbit_multiple_congruence {n h q : ℕ}
    (ho : addOrderOf (h : ZMod n) = 2 * q) {a b : ℤ}
    (hab : ((a * (h : ℤ) : ℤ) : ZMod n) = ((b * (h : ℤ) : ℤ) : ZMod n)) :
    ((2 * q : ℕ) : ℤ) ∣ a - b := by
  have heq : (a - b) • (h : ZMod n) = 0 := by
    simp only [zsmul_eq_mul, Int.cast_sub]
    push_cast at hab
    calc
      _ = (a : ZMod n) * (h : ZMod n) - (b : ZMod n) * (h : ZMod n) := by ring
      _ = 0 := sub_eq_zero.mpr hab
  rw [← ho]
  exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr heq

/-- A short signed representative realizes the cycle distance exactly. -/
theorem D_eq_abs_congruent {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) (z : ℤ)
    (hz : (z : ZMod n) = (j.val : ZMod n) - (i.val : ZMod n))
    (hshort : |z| ≤ (n / 2 : ℕ)) : (D i j : ℤ) = |z| := by
  have hle := D_le_congruent hn i j z hz
  apply le_antisymm hle
  by_contra hbad
  obtain ⟨q, hq, hqc⟩ := signed_displacement hn i j
  have hc : ((q - z : ℤ) : ZMod n) = 0 := by
    push_cast
    rw [hqc, hz]
    ring
  have hb : |q - z| < (n : ℤ) := by have := abs_sub q z; omega
  have heq := no_wrap (by omega) hc hb
  have : q = z := by omega
  rw [this] at hq
  omega

#print axioms construction_orbit_parameters
#print axioms orbit_multiple_congruence
#print axioms D_eq_abs_congruent

end RadioCycles
```

### `RadioConstructionPermutation.lean`

```lean
import RadioConstructionArithmetic

set_option linter.unusedSimpArgs false

namespace RadioCycles

def constructionInteger (d h q i : ℕ) : ℤ :=
  -((i / 2 : ℕ) : ℤ) * h - ((i / 2 / q : ℕ) : ℤ) + ((i % 2 : ℕ) : ℤ) * d

/-- The vertex order in equation (11) is a permutation, with no finite cutoff. -/
theorem construction_injective (n d h p q : ℕ) (hn : n = 2 * d)
    (_hp : 0 < p) (hq : 0 < q) (hd : d = p * q)
    (hpn : p ∣ n) (hph : p ∣ h) (hpd : p ∣ d)
    (ho : addOrderOf (h : ZMod n) = 2 * q)
    (hqh : (q : ZMod n) * (h : ZMod n) = (d : ZMod n)) :
    Function.Injective (fun i : Fin n => (constructionInteger d h q i.val : ZMod n)) := by
  intro i j hij
  let T := i.val / 2
  let U := j.val / 2
  have hi : T < d := by dsimp [T]; have := i.isLt; omega
  have hj : U < d := by dsimp [U]; have := j.isLt; omega
  have hB : T / q < p := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
  have hC : U / q < p := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
  have hh0 := (ZMod.natCast_eq_zero_iff h p).mpr hph
  have hd0 := (ZMod.natCast_eq_zero_iff d p).mpr hpd
  have hc := reduce_congruence hpn hij
  simp only [constructionInteger, Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_natCast] at hc
  simp only [hh0, hd0, mul_zero, zero_sub, add_zero] at hc
  have hBC : T / q = U / q := by
    have hcast : ((T / q : ℕ) : ZMod p) = ((U / q : ℕ) : ZMod p) := neg_injective hc
    have heq := congrArg ZMod.val hcast
    rw [ZMod.val_cast_of_lt hB, ZMod.val_cast_of_lt hC] at heq
    exact heq
  have hcong : (((-(T : ℤ) + ((i.val % 2 : ℕ) : ℤ) * q) * h : ℤ) : ZMod n) =
      (((-(U : ℤ) + ((j.val % 2 : ℕ) : ℤ) * q) * h : ℤ) : ZMod n) := by
    simp only [constructionInteger, Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_natCast] at hij
    change -(T : ZMod n) * h - ((T / q : ℕ) : ZMod n) +
      ((i.val % 2 : ℕ) : ZMod n) * d =
      -(U : ZMod n) * h - ((U / q : ℕ) : ZMod n) +
      ((j.val % 2 : ℕ) : ZMod n) * d at hij
    simp only [Int.cast_mul, Int.cast_add, Int.cast_neg, Int.cast_natCast]
    calc
      _ = -(T : ZMod n) * h + ((i.val % 2 : ℕ) : ZMod n) * d := by rw [← hqh]; ring
      _ = -(U : ZMod n) * h + ((j.val % 2 : ℕ) : ZMod n) * d := by
        calc
          _ = (-(T : ZMod n) * h - ((T / q : ℕ) : ZMod n) +
              ((i.val % 2 : ℕ) : ZMod n) * d) + ((T / q : ℕ) : ZMod n) := by ring
          _ = (-(U : ZMod n) * h - ((U / q : ℕ) : ZMod n) +
              ((j.val % 2 : ℕ) : ZMod n) * d) + ((T / q : ℕ) : ZMod n) := congrArg (fun z => z + ((T / q : ℕ) : ZMod n)) hij
          _ = _ := by rw [hBC]; ring
      _ = _ := by rw [← hqh]; ring
  have hdiv := orbit_multiple_congruence ho hcong
  let z : ℤ := (-(T : ℤ) + ((i.val % 2 : ℕ) : ℤ) * q) -
    (-(U : ℤ) + ((j.val % 2 : ℕ) : ℤ) * q)
  have hz0 : (z : ZMod (2 * q)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd z _).mpr hdiv
  have hiq := Nat.mod_lt T hq
  have hjq := Nat.mod_lt U hq
  have hTi := Nat.mod_add_div T q
  have hUj := Nat.mod_add_div U q
  rw [← hBC] at hUj
  have hTz : (T : ℤ) = (T % q : ℕ) + (q : ℤ) * (T / q : ℕ) := by exact_mod_cast hTi.symm
  have hUz : (U : ℤ) = (U % q : ℕ) + (q : ℤ) * (T / q : ℕ) := by exact_mod_cast hUj.symm
  have hiqz : ((T % q : ℕ) : ℤ) < (q : ℤ) := by exact_mod_cast hiq
  have hjqz : ((U % q : ℕ) : ℤ) < (q : ℤ) := by exact_mod_cast hjq
  have hdiff : -(q : ℤ) < (T : ℤ) - U ∧ (T : ℤ) - U < q := by
    constructor <;> linarith only [hTz, hUz, hiqz, hjqz,
      Int.natCast_nonneg (T % q), Int.natCast_nonneg (U % q)]
  have hbi : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
  have hbj : j.val % 2 = 0 ∨ j.val % 2 = 1 := by omega
  have hzsmall : |z| < ((2 * q : ℕ) : ℤ) := by
    unfold z
    rcases hbi with hiBit | hiBit <;> rcases hbj with hjBit | hjBit <;>
      simp only [hiBit, hjBit, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, Nat.cast_mul, Nat.cast_ofNat] <;>
      apply abs_lt.mpr <;> constructor <;> omega
  have hzeq := no_wrap (by omega) hz0 hzsmall
  have hbits : i.val % 2 = j.val % 2 := by
    unfold z at hzeq
    rcases hbi with hi0 | hi1 <;> rcases hbj with hj0 | hj1
    · omega
    · simp only [hi0, hj1, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul] at hzeq
      exfalso; omega
    · simp only [hi1, hj0, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul] at hzeq
      exfalso; omega
    · omega
  have hTU : T = U := by unfold z at hzeq; rw [hbits] at hzeq; omega
  apply Fin.ext
  dsimp [T, U] at hTU
  omega

#print axioms construction_injective

end RadioCycles
```

### `RadioConstructionDistances.lean`

```lean
import RadioConstructionArithmetic

namespace RadioCycles

/-- Distances for two consecutive pairs in construction (11). -/
theorem paired_step_distance {n d ℓ a b : ℕ} (hn : 3 ≤ n) (hnd : n = 2 * d)
    (hℓ : ℓ ≤ d) (ha : a ≤ 1) (hb : b ≤ 1) (i j : Fin n)
    (hc : (j.val : ZMod n) - (i.val : ZMod n) =
      -(ℓ : ZMod n) + ((b : ZMod n) - (a : ZMod n)) * (d : ZMod n)) :
    (D i j : ℤ) = if a = b then (ℓ : ℤ) else (d : ℤ) - ℓ := by
  have hhalf : n / 2 = d := by omega
  have ha' : a = 0 ∨ a = 1 := by omega
  have hb' : b = 0 ∨ b = 1 := by omega
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · simp only [Nat.cast_zero, sub_self, zero_mul, add_zero] at hc
    simp only [ite_true]
    have hd := D_eq_abs_congruent hn i j (-(ℓ : ℤ)) (by simpa using hc.symm) (by rw [abs_neg, abs_of_nonneg (by omega)]; omega)
    simpa using hd
  · simp only [Nat.cast_zero, Nat.cast_one, sub_zero, one_mul] at hc
    simp only [show (0 : ℕ) ≠ 1 by omega, ite_false]
    have hz : (((d : ℤ) - ℓ : ℤ) : ZMod n) = (j.val : ZMod n) - (i.val : ZMod n) := by
      rw [hc]; push_cast; ring
    have hd := D_eq_abs_congruent hn i j ((d : ℤ) - ℓ) hz (by rw [abs_of_nonneg (by omega)]; omega)
    simpa only [abs_of_nonneg (show (0 : ℤ) ≤ (d : ℤ) - ℓ by omega)] using hd
  · simp only [Nat.cast_zero, Nat.cast_one, zero_sub, neg_mul, one_mul] at hc
    simp only [show (1 : ℕ) ≠ 0 by omega, ite_false]
    have hn0 : (2 : ZMod n) * (d : ZMod n) = 0 := by
      have heq := congrArg (fun a : ℕ => (a : ZMod n)) hnd
      simpa using heq.symm
    have hz : (((d : ℤ) - ℓ : ℤ) : ZMod n) = (j.val : ZMod n) - (i.val : ZMod n) := by
      rw [hc]
      push_cast
      calc
        _ = (-(ℓ : ZMod n) + -(d : ZMod n)) + 2 * (d : ZMod n) := by ring
        _ = _ := by rw [hn0, add_zero]
    have hd := D_eq_abs_congruent hn i j ((d : ℤ) - ℓ) hz (by rw [abs_of_nonneg (by omega)]; omega)
    simpa only [abs_of_nonneg (show (0 : ℤ) ≤ (d : ℤ) - ℓ by omega)] using hd
  · simp only [Nat.cast_one, sub_self, zero_mul, add_zero] at hc
    simp only [ite_true]
    have hd := D_eq_abs_congruent hn i j (-(ℓ : ℤ)) (by simpa using hc.symm) (by rw [abs_neg, abs_of_nonneg (by omega)]; omega)
    simpa using hd

#print axioms paired_step_distance

end RadioCycles
```

### `RadioConstructionLabels.lean`

```lean
import RadioConstructionPermutation
import RadioConstructionDistances

set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

namespace RadioCycles

def constructionLabel (d h q i : ℕ) : ℕ :=
  (i / 2) * (2 * d - 3 * h) + (i / 2 / q) + (i % 2) * (d - 2 * h)

/-- All pairwise radio inequalities for the explicit order and label gaps. -/
theorem construction_radio_inequality {n k d h q : ℕ} (hn : 3 ≤ n)
    (hnd : n = 2 * d) (hk : k + 1 + 2 * h = n) (hhd : 2 * h < d) (hq : 0 < q)
    (x : Fin n → Fin n)
    (hx : ∀ i, ((x i).val : ZMod n) = (constructionInteger d h q i.val : ZMod n)) :
    ∀ i j : Fin n, i ≠ j →
      (k : ℤ) + 1 - D (x i) (x j) ≤
        |(constructionLabel d h q i.val : ℤ) - constructionLabel d h q j.val| := by
  have ha : ((d - 2 * h : ℕ) : ℤ) = (d : ℤ) - 2 * h := by omega
  have hΦ : ((2 * d - 3 * h : ℕ) : ℤ) = 2 * (d : ℤ) - 3 * h := by omega
  have hkz : (k : ℤ) + 1 + 2 * h = n := by exact_mod_cast hk
  have hndz : (n : ℤ) = 2 * (d : ℤ) := by exact_mod_cast hnd
  have hΦ0 : 0 ≤ 2 * (d : ℤ) - 3 * h := by omega
  have ordered : ∀ i j : Fin n, i.val < j.val →
      (k : ℤ) + 1 - D (x i) (x j) ≤
        (constructionLabel d h q j.val : ℤ) - constructionLabel d h q i.val := by
    intro i j hij
    let T := i.val / 2
    let U := j.val / 2
    have hTU : T ≤ U := by dsimp [T, U]; omega
    have hbi : i.val % 2 ≤ 1 := by omega
    have hbj : j.val % 2 ≤ 1 := by omega
    have hB : T / q ≤ U / q := Nat.div_le_div_right hTU
    have hLc : ∀ z : Fin n, (constructionLabel d h q z.val : ℤ) =
        ((z.val / 2 : ℕ) : ℤ) * (2 * (d : ℤ) - 3 * h) +
        ((z.val / 2 / q : ℕ) : ℤ) + ((z.val % 2 : ℕ) : ℤ) * ((d : ℤ) - 2 * h) := by
      intro z
      simp only [constructionLabel, Nat.cast_add, Nat.cast_mul, ha, hΦ]
    by_cases heq : T = U
    · have hi0 : i.val % 2 = 0 := by dsimp [T, U] at heq; omega
      have hj1 : j.val % 2 = 1 := by dsimp [T, U] at heq; omega
      have hc : ((d : ℤ) : ZMod n) = ((x j).val : ZMod n) - ((x i).val : ZMod n) := by
        rw [hx i, hx j]
        simp only [constructionInteger, Int.cast_add, Int.cast_sub, Int.cast_neg,
          Int.cast_mul, Int.cast_natCast, hi0, hj1, Nat.cast_zero, Nat.cast_one, Int.cast_zero, Int.cast_one, zero_mul, one_mul]
        change (d : ZMod n) = -(U : ZMod n) * h - ((U / q : ℕ) : ZMod n) + d -
          (-(T : ZMod n) * h - ((T / q : ℕ) : ZMod n) + 0)
        rw [heq]
        ring
      have hd := D_eq_abs_congruent hn (x i) (x j) d hc (by rw [abs_of_nonneg (by omega)]; omega)
      rw [abs_of_nonneg (Int.natCast_nonneg d)] at hd
      rw [hLc i, hLc j, hi0, hj1]
      change (k : ℤ) + 1 - D (x i) (x j) ≤
        (U : ℤ) * (2 * d - 3 * h) + ((U / q : ℕ) : ℤ) + (1 : ℤ) * (d - 2 * h) -
        ((T : ℤ) * (2 * d - 3 * h) + ((T / q : ℕ) : ℤ) + (0 : ℤ) * (d - 2 * h))
      rw [heq]
      nlinarith only [hkz, hndz, hd]
    · by_cases hnear : U = T + 1
      · have hstep : U / q ≤ T / q + 1 := by
          apply Nat.lt_succ_iff.mp
          apply (Nat.div_lt_iff_lt_mul hq).mpr
          have hrem := Nat.mod_lt T hq
          have hdiv := Nat.mod_add_div T q
          nlinarith
        let M := U / q - T / q
        have hM : M ≤ 1 := by dsimp [M]; omega
        have hMB : U / q = T / q + M := by dsimp [M]; omega
        have hℓ : h + M ≤ d := by omega
        have hc : ((x j).val : ZMod n) - ((x i).val : ZMod n) =
            -((h + M : ℕ) : ZMod n) +
            (((j.val % 2 : ℕ) : ZMod n) - ((i.val % 2 : ℕ) : ZMod n)) * d := by
          rw [hx i, hx j]
          simp only [constructionInteger, Int.cast_add, Int.cast_sub, Int.cast_neg,
            Int.cast_mul, Int.cast_natCast]
          change -(U : ZMod n) * h - ((U / q : ℕ) : ZMod n) + ((j.val % 2 : ℕ) : ZMod n) * d -
            (-(T : ZMod n) * h - ((T / q : ℕ) : ZMod n) + ((i.val % 2 : ℕ) : ZMod n) * d) = _
          rw [hMB, hnear]
          push_cast
          ring
        have hd := paired_step_distance hn hnd hℓ hbi hbj (x i) (x j) hc
        rw [hLc i, hLc j]
        change (k : ℤ) + 1 - D (x i) (x j) ≤
          (U : ℤ) * (2 * d - 3 * h) + ((U / q : ℕ) : ℤ) + ((j.val % 2 : ℕ) : ℤ) * (d - 2 * h) -
          ((T : ℤ) * (2 * d - 3 * h) + ((T / q : ℕ) : ℤ) + ((i.val % 2 : ℕ) : ℤ) * (d - 2 * h))
        rw [hMB, hnear]
        simp only [Nat.cast_add, Nat.cast_one]
        have hbi' : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
        have hbj' : j.val % 2 = 0 ∨ j.val % 2 = 1 := by omega
        rcases hbi' with hiBit | hiBit <;> rcases hbj' with hjBit | hjBit <;>
          simp only [hiBit, hjBit, Nat.cast_zero, Nat.cast_one, Int.cast_zero, Int.cast_one, zero_mul, one_mul] at hd ⊢ <;>
          norm_num at hd <;>
          nlinarith only [hkz, hndz, hd, Int.natCast_nonneg M,
            show (0 : ℤ) ≤ (d : ℤ) - 2 * h by omega]
      · have hfar : T + 2 ≤ U := by omega
        have hprod : 2 * (2 * (d : ℤ) - 3 * h) ≤
            (U : ℤ) * (2 * d - 3 * h) - (T : ℤ) * (2 * d - 3 * h) := by
          have hTUz : (T : ℤ) + 2 ≤ U := by exact_mod_cast hfar
          nlinarith only [mul_nonneg (show (0 : ℤ) ≤ (U : ℤ) - T - 2 by omega) hΦ0]
        have hbitProdI : ((i.val % 2 : ℕ) : ℤ) * ((d : ℤ) - 2 * h) ≤ (d : ℤ) - 2 * h := by
          have hbz : ((i.val % 2 : ℕ) : ℤ) ≤ 1 := by omega
          simpa using mul_le_mul_of_nonneg_right hbz (show (0 : ℤ) ≤ (d : ℤ) - 2 * h by omega)
        have hbitProdJ : 0 ≤ ((j.val % 2 : ℕ) : ℤ) * ((d : ℤ) - 2 * h) := mul_nonneg (by omega) (by omega)
        have hD0 : (0 : ℤ) ≤ D (x i) (x j) := by omega
        rw [hLc i, hLc j]
        have hBz : ((T / q : ℕ) : ℤ) ≤ ((U / q : ℕ) : ℤ) := by exact_mod_cast hB
        nlinarith only [hprod, hbitProdI, hbitProdJ, hD0, hBz, hkz, hndz,
          show 2 * (h : ℤ) < d by exact_mod_cast hhd]
  intro i j hij
  rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun h => hij (Fin.ext h)) with hord | hord
  · have ho := ordered i j hord
    have habs := neg_le_abs ((constructionLabel d h q i.val : ℤ) - constructionLabel d h q j.val)
    omega
  · have ho := ordered j i hord
    rw [D_comm] at ho
    have habs := le_abs_self ((constructionLabel d h q i.val : ℤ) - constructionLabel d h q j.val)
    omega

#print axioms construction_radio_inequality

end RadioCycles
```

### `RadioSharpUpper.lean`

```lean
import RadioConstructionLabels

namespace RadioCycles

def constructionVertex {n : ℕ} (hn : 0 < n) (d h q : ℕ) (i : Fin n) : Fin n :=
  letI : NeZero n := ⟨by omega⟩
  ⟨(constructionInteger d h q i.val : ZMod n).val, ZMod.val_lt _⟩

theorem constructionVertex_cast {n : ℕ} (hn : 0 < n) (d h q : ℕ) (i : Fin n) :
    ((constructionVertex hn d h q i).val : ZMod n) = (constructionInteger d h q i.val : ZMod n) := by
  let : NeZero n := ⟨by omega⟩
  exact ZMod.natCast_zmod_val _

/-- The labels from (11) have their maximum at the final pair. -/
theorem construction_label_bound {n d h p q : ℕ} (hn : n = 2 * d)
    (hp : 0 < p) (hq : 0 < q) (hd : d = p * q) (i : Fin n) :
    constructionLabel d h q i.val ≤
      (d - 1) * (2 * d - 3 * h) + (p - 1) + (d - 2 * h) := by
  have ht : i.val / 2 ≤ d - 1 := by have := i.isLt; omega
  have hb : i.val / 2 / q ≤ p - 1 := by
    have hi : i.val / 2 < d := by have := i.isLt; omega
    have hh : i.val / 2 / q < p := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    omega
  have hbit : i.val % 2 ≤ 1 := by omega
  have h1 := Nat.mul_le_mul_right (2 * d - 3 * h) ht
  have h2 := Nat.mul_le_mul_right (d - 2 * h) hbit
  unfold constructionLabel
  omega

/-- Construction (11), as an actual natural labeling of Fin n with zero
minimum and exact sharp span. No upper-bound theorem is imported as an axiom. -/
theorem radio_sharp_construction {n k : ℕ} (hn : Even n) (hk : Odd k)
    (hlo : n / 2 ≤ k) (hhi : k < n - 3)
    (hsub : ((n / 2 : ℕ) : ZMod n) ∈ AddSubgroup.zmultiples (hParam n k : ZMod n)) :
    ∃ f : Fin n → ℕ, Radio k f ∧ (∃ i, f i = 0) ∧
      span f = lowerBound n k + pParam n k - 1 := by
  classical
  have hpar := parameter_arithmetic n k hn hk hlo hhi
  let d := n / 2
  let h := hParam n k
  let p := pParam n k
  have hn0 : 0 < n := by omega
  have hp : 0 < p := Nat.gcd_pos_of_pos_left h hn0
  have hpd : p ∣ d := (mem_zmultiples_iff_gcd_dvd _ _ _).mp hsub
  have hn2 : n = 2 * d := hpar.2.2.1
  obtain ⟨q, hq, hd, ho, hqh⟩ := construction_orbit_parameters n d h hn2 (by dsimp [d]; omega) hpd
  have hinj := construction_injective n d h p q hn2 hp hq hd
    (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _) hpd ho hqh
  let v := constructionVertex hn0 d h q
  have hv : ∀ i, ((v i).val : ZMod n) = (constructionInteger d h q i.val : ZMod n) :=
    constructionVertex_cast hn0 d h q
  have hvinj : Function.Injective v := by
    intro i j heq
    apply hinj
    change (constructionInteger d h q i.val : ZMod n) = (constructionInteger d h q j.val : ZMod n)
    rw [← hv i, ← hv j, heq]
  let x : Fin n ≃ Fin n := Equiv.ofBijective v ⟨hvinj, Finite.surjective_of_injective hvinj⟩
  let f : Fin n → ℕ := fun i => constructionLabel d h q (x.symm i).val
  have hfx : ∀ i, f (x i) = constructionLabel d h q i.val := by intro i; simp [f]
  have hx : ∀ i, ((x i).val : ZMod n) = (constructionInteger d h q i.val : ZMod n) := hv
  have hhd : 2 * h < d := by have := hpar.2.2.2.2.1; dsimp [d, h]; omega
  have hR := construction_radio_inequality hpar.1 hn2 hpar.2.2.2.1 hhd hq x hx
  have hf : Radio k f := by
    intro i j hij
    have hi := hR (x.symm i) (x.symm j) (x.symm.injective.ne hij)
    simpa only [x.apply_symm_apply] using hi
  let B := (d - 1) * (2 * d - 3 * h) + (p - 1) + (d - 2 * h)
  have hlabels : ∀ i, f i ≤ B := by
    intro i
    exact construction_label_bound hn2 hp hq hd (x.symm i)
  have hspan : span f ≤ B := by
    apply (span_le_iff f B).mpr
    intro i j
    have hi := hlabels i
    have hj := hlabels j
    exact abs_le.mpr ⟨by omega, by omega⟩
  have hB : B = lowerBound n k + pParam n k - 1 := by
    have hlb := lowerBoundInt_formula n k hn hk hlo hhi
    have hlbc := lowerBound_cast n k hn hk hlo hhi
    have hd0 : 1 ≤ d := by dsimp [d]; omega
    have ha : ((d - 2 * h : ℕ) : ℤ) = (d : ℤ) - 2 * h := by omega
    have hphi : ((2 * d - 3 * h : ℕ) : ℤ) = 2 * (d : ℤ) - 3 * h := by omega
    have hd1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
    have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
    have hBcast : (B : ℤ) = (lowerBound n k : ℤ) + p - 1 := by
      simp only [B, Nat.cast_add, Nat.cast_mul, ha, hphi, hd1, hp1]
      dsimp [d, h] at *
      linarith
    dsimp [p] at *
    omega
  refine ⟨f, hf, ?_, le_antisymm (by simpa [hB] using hspan) (radio_span_sharp_lower hn hk hlo hhi hsub hf)⟩
  refine ⟨x ⟨0, hn0⟩, ?_⟩
  rw [hfx]
  simp [constructionLabel]

theorem radioKNumber_sharp_upper {n k : ℕ} (hn : Even n) (hk : Odd k)
    (hlo : n / 2 ≤ k) (hhi : k < n - 3)
    (hsub : ((n / 2 : ℕ) : ZMod n) ∈ AddSubgroup.zmultiples (hParam n k : ZMod n)) :
    radioKNumber n k ≤ lowerBound n k + pParam n k - 1 := by
  obtain ⟨f, hf, _, hs⟩ := radio_sharp_construction hn hk hlo hhi hsub
  rw [← hs]
  exact radioKNumber_le hf

#print axioms constructionVertex_cast
#print axioms construction_label_bound
#print axioms radio_sharp_construction
#print axioms radioKNumber_sharp_upper

end RadioCycles
```

### `RadioSourceBound.lean`

```lean
import RadioParameters

namespace RadioCycles

/-- Equation (1): the integer ceiling, before any natural conversion. -/
def sourcePhiInt (n k : ℕ) : ℤ := (3 * (k : ℤ) + 3 - n + 1) / 2

/-- Equation (2), including both parity branches, in integer arithmetic. -/
def sourceLowerBoundInt (n k : ℕ) : ℤ :=
  if Even n then
    sourcePhiInt n k * (((n : ℤ) - 2) / 2) + k - (n : ℤ) / 2 + 1
  else sourcePhiInt n k * (((n : ℤ) - 1) / 2)

def sourceLowerBound (n k : ℕ) : ℕ := (sourceLowerBoundInt n k).toNat

/-- The target branch is exactly the full source formula on its stated parities. -/
theorem lowerBoundInt_eq_source {n k : ℕ} (hn : Even n) (hk : Odd k) :
    lowerBoundInt n k = sourceLowerBoundInt n k := by
  have hphi := source_phi_agrees n k hn hk
  have hd : ((n : ℤ) - 2) / 2 = (n : ℤ) / 2 - 1 := by omega
  simp only [sourceLowerBoundInt, hn, ite_true, sourcePhiInt, hphi, hd, lowerBoundInt]
  ring

theorem lowerBound_eq_source {n k : ℕ} (hn : Even n) (hk : Odd k) :
    lowerBound n k = sourceLowerBound n k := by
  unfold lowerBound sourceLowerBound
  rw [lowerBoundInt_eq_source hn hk]

#print axioms lowerBoundInt_eq_source
#print axioms lowerBound_eq_source

end RadioCycles
```

### `RadioTheorem.lean`

```lean
import RadioSharpUpper
import RadioSourceBound

namespace RadioCycles

/-- Conjecture 1 of arXiv:2106.15059v2, with both inequalities proved for
all admissible parameters and the literal graph-distance minimum. -/
theorem radio_even_cycle_sharp (n k : ℕ) (hn : Even n) (hk : Odd k)
    (hlo : n / 2 ≤ k) (hhi : k < n - 3)
    (hsub : ((n / 2 : ℕ) : ZMod n) ∈ AddSubgroup.zmultiples (hParam n k : ZMod n)) :
    radioKNumber n k = lowerBound n k + pParam n k - 1 := by
  exact le_antisymm (radioKNumber_sharp_upper hn hk hlo hhi hsub)
    (radioKNumber_sharp_lower hn hk hlo hhi hsub)

theorem sharpConjecture_proved : SharpConjecture := by
  intro n k hn hk hlo hhi hsub
  exact radio_even_cycle_sharp n k hn hk hlo hhi hsub

/-- The same endpoint with LB written as the full piecewise source definition. -/
theorem radio_even_cycle_sharp_source (n k : ℕ) (hn : Even n) (hk : Odd k)
    (hlo : n / 2 ≤ k) (hhi : k < n - 3)
    (hsub : ((n / 2 : ℕ) : ZMod n) ∈ AddSubgroup.zmultiples (hParam n k : ZMod n)) :
    radioKNumber n k = sourceLowerBound n k + pParam n k - 1 := by
  rw [← lowerBound_eq_source hn hk]
  exact radio_even_cycle_sharp n k hn hk hlo hhi hsub

#print axioms exists_radio
#print axioms exists_attainable
#print axioms radioKNumber_attained
#print axioms radioKNumber_le
#print axioms le_radioKNumber_iff
#print axioms dist_le_span
#print axioms span_eq_max_of_zero
#print axioms span_eq_max_sub_min
#print axioms normalize_radio
#print axioms normalize_span
#print axioms exists_normalized
#print axioms sorted_labeling
#print axioms cycle_connected
#print axioms D_eq_zero_iff
#print axioms D_pos
#print axioms D_comm
#print axioms D_triangle
#print axioms D_eq_one_iff
#print axioms cycle_adj
#print axioms radio_injective_of_distance_bound
#print axioms radioKNumber_normalized_attained
#print axioms mem_zmultiples_iff_gcd_dvd
#print axioms parameter_arithmetic
#print axioms lowerBoundInt_formula
#print axioms source_phi_agrees
#print axioms lowerBoundInt_nonneg
#print axioms lowerBound_cast
#print axioms admissible_parameters_exist
#print axioms variation_zero
#print axioms variation_succ
#print axioms travel_le_variation
#print axioms path_range
#print axioms path_diameter_le
#print axioms slack_sum_identity
#print axioms slack_potential_mono
#print axioms slack_bounds
#print axioms no_wrap
#print axioms same_direction
#print axioms lift_difference
#print axioms residue_diameter_bound
#print axioms path_residue_bound
#print axioms variation_congr
#print axioms variation_reverse
#print axioms joinedPath_variation
#print axioms two_track_residue_bound
#print axioms label_distance_cast
#print axioms span_le_iff
#print axioms arcDistance_comm
#print axioms arcDistance_triangle
#print axioms arcDistance_adj
#print axioms arcDistance_le_walk
#print axioms D_le_forward
#print axioms D_le_linear
#print axioms D_eq_arcDistance
#print axioms D_formula
#print axioms D_diameter
#print axioms D_perimeter
#print axioms D_antipode
#print axioms D_translate
#print axioms signed_displacement
#print axioms D_le_congruent
#print axioms antipode_cast
#print axioms near_antipodal
#print axioms sum_gap_pairs
#print axioms radio_injective
#print axioms sorted_radio_gap
#print axioms sorted_radio_pair
#print axioms sorted_span
#print axioms radio_span_lowerBound
#print axioms extracted_slack_relation
#print axioms extracted_slack_budget
#print axioms radio_slack_extraction
#print axioms sorted_radio_separation
#print axioms near_step_bounds
#print axioms signed_step_error
#print axioms enum_radio_separation
#print axioms enum_residue_cover
#print axioms reduce_congruence
#print axioms modular_track_obstruction
#print axioms short_step_data
#print axioms geometric_track_obstruction
#print axioms radio_span_sharp_lower
#print axioms radioKNumber_sharp_lower
#print axioms construction_orbit_parameters
#print axioms orbit_multiple_congruence
#print axioms D_eq_abs_congruent
#print axioms construction_injective
#print axioms paired_step_distance
#print axioms construction_radio_inequality
#print axioms constructionVertex_cast
#print axioms construction_label_bound
#print axioms radio_sharp_construction
#print axioms radioKNumber_sharp_upper
#print axioms lowerBoundInt_eq_source
#print axioms lowerBound_eq_source
#print axioms radio_even_cycle_sharp
#print axioms sharpConjecture_proved
#print axioms radio_even_cycle_sharp_source

end RadioCycles
```

