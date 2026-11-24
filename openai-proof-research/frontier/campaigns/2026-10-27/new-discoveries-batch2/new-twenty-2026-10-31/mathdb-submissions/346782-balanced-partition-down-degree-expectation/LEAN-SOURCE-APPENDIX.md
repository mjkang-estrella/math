# Lean source appendix for MathDB 346782

Modules are listed in import order.

### `BalancedRows.lean`

```lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq

open scoped BigOperators
open Finset

namespace BalancedPartition

def width (lam : List ℕ) : ℕ := lam[0]!
def height (lam : List ℕ) : ℕ := lam.length
def gcd (lam : List ℕ) : ℕ := Nat.gcd (width lam) (height lam)
def u (lam : List ℕ) : ℕ := width lam / gcd lam
def v (lam : List ℕ) : ℕ := height lam / gcd lam
def area (lam : List ℕ) : ℕ := width lam * height lam / gcd lam
def perimeter (lam : List ℕ) : ℕ := (width lam + height lam) / gcd lam

def IsPartition (lam : List ℕ) : Prop :=
  0 < height lam ∧ (∀ i < height lam, 0 < lam[i]!) ∧
    (∀ i, i + 1 < height lam → lam[i+1]! ≤ lam[i]!)

def Balanced (lam : List ℕ) : Prop :=
  ∀ s, 1 ≤ s → s < height lam → lam[s]! < lam[s-1]! →
    height lam * lam[s]! + width lam * s = width lam * height lam

theorem row_le_width {lam : List ℕ} (hp : IsPartition lam) :
    ∀ i < height lam, lam[i]! ≤ width lam := by
  intro i
  induction i with
  | zero => exact fun _ => le_rfl
  | succ i ih =>
      intro hi
      exact (hp.2.2 i hi).trans (ih (by omega))

/-- With horizontal distance measured from the right and vertical distance from
the top, an interior addable corner has coordinates (width - row length, s). -/
theorem balanced_iff_diagonal {lam : List ℕ} (hp : IsPartition lam) :
    Balanced lam ↔
      ∀ s, 1 ≤ s → s < height lam → lam[s]! < lam[s-1]! →
        height lam * (width lam - lam[s]!) = width lam * s := by
  have h (s : ℕ) (hs : s < height lam) :
      height lam * (width lam - lam[s]!) + height lam * lam[s]! =
        width lam * height lam := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (row_le_width hp s hs), Nat.mul_comm]
  constructor
  · intro hb s hs hlt hd
    have := hb s hs hlt hd
    have := h s hlt
    omega
  · intro hb s hs hlt hd
    have := hb s hs hlt hd
    have := h s hlt
    omega

/-- A nonrectangular example satisfying the partition and balance hypotheses. -/
theorem balanced_staircase : IsPartition [3, 2, 1] ∧ Balanced [3, 2, 1] := by
  refine ⟨⟨by decide, ?_, ?_⟩, ?_⟩
  · intro i hi
    change i < 3 at hi
    have hh : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hh with rfl | rfl | rfl <;> decide
  · intro i hi
    change i + 1 < 3 at hi
    have hh : i = 0 ∨ i = 1 := by omega
    rcases hh with rfl | rfl <;> decide
  · intro i hi hj _
    change i < 3 at hj
    have hh : i = 1 ∨ i = 2 := by omega
    rcases hh with rfl | rfl <;> decide

theorem gcd_pos {lam : List ℕ} (hp : IsPartition lam) : 0 < gcd lam :=
  Nat.gcd_pos_of_pos_right _ hp.1

theorem u_mul_gcd (lam : List ℕ) : u lam * gcd lam = width lam :=
  Nat.div_mul_cancel (Nat.gcd_dvd_left ..)

theorem v_mul_gcd (lam : List ℕ) : v lam * gcd lam = height lam :=
  Nat.div_mul_cancel (Nat.gcd_dvd_right ..)

theorem area_eq (lam : List ℕ) : area lam = v lam * width lam := by
  unfold area v
  rw [Nat.mul_div_assoc _ ((show gcd lam ∣ height lam from Nat.gcd_dvd_right ..)), Nat.mul_comm]

theorem area_eq' (lam : List ℕ) : area lam = u lam * height lam := by
  unfold area u
  rw [Nat.mul_comm, Nat.mul_div_assoc _ ((show gcd lam ∣ width lam from Nat.gcd_dvd_left ..)), Nat.mul_comm]

theorem perimeter_eq (lam : List ℕ) : perimeter lam = u lam + v lam :=
  Nat.add_div_of_dvd_left (show gcd lam ∣ height lam from Nat.gcd_dvd_right ..)

theorem degreeExponent (lam : List ℕ) (i m : ℕ) :
    (width lam * i + height lam * m) / gcd lam = u lam * i + v lam * m := by
  have hh : gcd lam ∣ height lam * m := dvd_mul_of_dvd_left (Nat.gcd_dvd_right ..) _
  have hw' : gcd lam ∣ width lam := Nat.gcd_dvd_left ..
  have hh' : gcd lam ∣ height lam := Nat.gcd_dvd_right ..
  rw [Nat.add_div_of_dvd_left hh, Nat.mul_comm (width lam), Nat.mul_comm (height lam),
    Nat.mul_div_assoc _ hw', Nat.mul_div_assoc _ hh']
  exact congrArg₂ (· + ·) (Nat.mul_comm _ _) (Nat.mul_comm _ _)

theorem rankExponent (lam : List ℕ) (m : ℕ) :
    height lam * m / gcd lam = v lam * m := by
  simpa using degreeExponent lam 0 m

/-- A diagram in the bounding rectangle, with trailing zero rows allowed. -/
abbrev Rows (lam : List ℕ) := Fin (height lam) → Fin (width lam + 1)

/-- Zero-based row length, extended by zeros below the rectangle. -/
def row {lam : List ℕ} (x : Rows lam) (i : ℕ) : ℕ :=
  if h : i < height lam then (x ⟨i,h⟩).val else 0

@[simp] theorem row_fin {lam : List ℕ} (x : Rows lam) (i : Fin (height lam)) :
    row x i = (x i).val := by simp [row, i.isLt]

@[simp] theorem row_end {lam : List ℕ} (x : Rows lam) : row x (height lam) = 0 := by
  simp [row]

theorem row_le {lam : List ℕ} (x : Rows lam) (i : ℕ) : row x i ≤ width lam := by
  unfold row
  split
  · have := (x ⟨i, ‹i < height lam›⟩).isLt
    omega
  · omega

def prev {lam : List ℕ} (x : Rows lam) (i : ℕ) : ℕ :=
  if i = 0 then width lam else row x (i-1)

@[simp] theorem prev_zero {lam : List ℕ} (x : Rows lam) : prev x 0 = width lam := by
  simp [prev]

@[simp] theorem prev_succ {lam : List ℕ} (x : Rows lam) (i : ℕ) : prev x (i+1) = row x i := by
  simp [prev]

def InInterval {lam : List ℕ} (x : Rows lam) : Prop :=
  ∀ i : Fin (height lam), row x i ≤ lam[i.val]! ∧ row x i ≤ prev x i

noncomputable def interval (lam : List ℕ) : Finset (Rows lam) :=
  open Classical in univ.filter InInterval

@[simp] theorem mem_interval {lam : List ℕ} {x : Rows lam} :
    x ∈ interval lam ↔ InInterval x := by
  classical simp [interval]

def emptyRows (lam : List ℕ) : Rows lam := fun _ => 0

@[simp] theorem row_empty (lam : List ℕ) (i : ℕ) : row (emptyRows lam) i = 0 := by
  simp [row, emptyRows]

theorem empty_mem (lam : List ℕ) : emptyRows lam ∈ interval lam := by
  rw [mem_interval]
  intro i
  rw [row_empty]
  exact ⟨Nat.zero_le _, Nat.zero_le _⟩

def size {lam : List ℕ} (x : Rows lam) : ℕ := ∑ i : Fin (height lam), row x i

def Addable {lam : List ℕ} (x : Rows lam) (i : Fin (height lam)) : Prop :=
  row x i < lam[i.val]! ∧ row x i < prev x i

def Removable {lam : List ℕ} (x : Rows lam) (i : Fin (height lam)) : Prop :=
  row x (i.val+1) < row x i

noncomputable def addRow {lam : List ℕ} (x : Rows lam) (i : Fin (height lam)) : Rows lam :=
  Function.update x i ⟨min (row x i + 1) (width lam), by omega⟩

noncomputable def delRow {lam : List ℕ} (x : Rows lam) (i : Fin (height lam)) : Rows lam :=
  Function.update x i ⟨row x i - 1, Nat.lt_succ_of_le ((Nat.sub_le ..).trans (row_le x i))⟩

theorem row_add {lam : List ℕ} {x : Rows lam} {i : Fin (height lam)} (hi : Addable x i)
    (j : ℕ) : row (addRow x i) j = if j = i.val then row x j + 1 else row x j := by
  have hm : row x i + 1 ≤ width lam := hi.2.trans_le (by
    unfold prev
    split
    · exact le_rfl
    · exact row_le ..)
  by_cases hj : j = i.val
  · subst j
    rw [row_fin, addRow, Function.update_self]
    rw [ite_eq_left rfl]
    exact min_eq_left hm
  · by_cases h : j < height lam
    · have hne : (⟨j,h⟩ : Fin (height lam)) ≠ i := by intro e; exact hj (congrArg Fin.val e)
      simp [row, h, hj, addRow, Function.update_of_ne hne]
    · simp [row, h, hj]

theorem row_del {lam : List ℕ} (x : Rows lam) (i : Fin (height lam))
    (j : ℕ) : row (delRow x i) j = if j = i.val then row x j - 1 else row x j := by
  by_cases hj : j = i.val
  · subst j
    simp [delRow]
  · by_cases h : j < height lam
    · have hne : (⟨j,h⟩ : Fin (height lam)) ≠ i := by intro e; exact hj (congrArg Fin.val e)
      simp [row, h, hj, delRow, Function.update_of_ne hne]
    · simp [row, h, hj]

theorem row_antitone_step {lam : List ℕ} {x : Rows lam} (hx : InInterval x)
    (i : ℕ) : row x (i+1) ≤ row x i := by
  by_cases h : i+1 < height lam
  · simpa using (hx ⟨i+1,h⟩).2
  · simp [row, h]

theorem mem_interval_iff_antitone {lam : List ℕ} {x : Rows lam} :
    x ∈ interval lam ↔
      Antitone (fun i : Fin (height lam) => row x i) ∧
        (∀ i : Fin (height lam), row x i ≤ lam[i.val]!) := by
  rw [mem_interval]
  constructor
  · intro hx
    exact ⟨fun _ _ hij => (antitone_nat_of_succ_le (row_antitone_step hx)) hij, fun i => (hx i).1⟩
  · rintro ⟨ha, hb⟩ i
    refine ⟨hb i, ?_⟩
    unfold prev
    by_cases hi : i.val = 0
    · rw [ite_eq_left hi]
      exact row_le x i
    · rw [ite_eq_right hi]
      have hle : i.val - 1 ≤ i.val := Nat.sub_le ..
      exact ha (show (⟨i.val-1, hle.trans_lt i.isLt⟩ : Fin (height lam)) ≤ i from hle)

theorem interval_represents_rows {lam : List ℕ} (hp : IsPartition lam)
    (r : Fin (height lam) → ℕ) (hr : Antitone r) (hb : ∀ i, r i ≤ lam[i.val]!) :
    ∃! x ∈ interval lam, ∀ i : Fin (height lam), row x i = r i := by
  let x : Rows lam := fun i => ⟨r i, Nat.lt_succ_of_le ((hb i).trans (row_le_width hp i i.isLt))⟩
  have hx (i : Fin (height lam)) : row x i = r i := row_fin x i
  refine ⟨x, ⟨mem_interval_iff_antitone.mpr ⟨?_, ?_⟩, hx⟩, ?_⟩
  · intro i j hij
    change row x j ≤ row x i
    rw [hx, hx]
    exact hr hij
  · intro i
    rw [hx]
    exact hb i
  · intro y hy
    ext i
    rw [← row_fin, ← row_fin, hy.2 i, hx]

theorem prev_add {lam : List ℕ} {x : Rows lam} {i : Fin (height lam)} (hi : Addable x i)
    (j : ℕ) : prev (addRow x i) j = if j = i.val+1 then prev x j + 1 else prev x j := by
  cases j with
  | zero => simp
  | succ j => simp [row_add hi]

theorem prev_del {lam : List ℕ} (x : Rows lam) (i : Fin (height lam))
    (j : ℕ) : prev (delRow x i) j = if j = i.val+1 then prev x j - 1 else prev x j := by
  cases j with
  | zero => simp
  | succ j => simp [row_del]

theorem add_interval {lam : List ℕ} {x : Rows lam} (hx : InInterval x)
    {i : Fin (height lam)} (hi : Addable x i) : InInterval (addRow x i) := by
  intro j
  have hb := hx j
  have ⟨hil, hip⟩ := hi
  rw [row_add hi, prev_add hi]
  by_cases he : j.val = i.val
  · have je : j = i := Fin.ext he
    subst j
    rw [ite_eq_left rfl, ite_eq_right (by omega)]
    omega
  · rw [ite_eq_right he]
    split <;> omega

theorem del_interval {lam : List ℕ} {x : Rows lam} (hx : InInterval x)
    {i : Fin (height lam)} (hi : Removable x i) : InInterval (delRow x i) := by
  intro j
  have hb := hx j
  unfold Removable at hi
  rw [row_del, prev_del]
  by_cases he : j.val = i.val + 1
  · have hn : j.val ≠ i.val := by omega
    rw [ite_eq_left he, ite_eq_right hn]
    have hprev : prev x j = row x i := by rw [he, prev_succ]
    exact ⟨hb.1, by rw [hprev, he]; omega⟩
  · rw [ite_eq_right he]
    split <;> omega

theorem add_removable {lam : List ℕ} {x : Rows lam} (hx : InInterval x)
    {i : Fin (height lam)} (hi : Addable x i) : Removable (addRow x i) i := by
  unfold Removable
  rw [row_add hi, row_add hi, ite_eq_left rfl, ite_eq_right (by omega)]
  have := row_antitone_step hx i
  omega

theorem del_addable {lam : List ℕ} {x : Rows lam} (hx : InInterval x)
    {i : Fin (height lam)} (hi : Removable x i) : Addable (delRow x i) i := by
  have hb := hx i
  unfold Removable at hi
  unfold Addable
  rw [row_del, ite_eq_left rfl]
  constructor
  · omega
  · rw [prev_del, ite_eq_right (by omega)]
    omega

theorem del_add {lam : List ℕ} {x : Rows lam}
    {i : Fin (height lam)} (hi : Addable x i) : delRow (addRow x i) i = x := by
  ext j
  rw [← row_fin, ← row_fin x]
  rw [row_del, row_add hi]
  split <;> omega

theorem add_del {lam : List ℕ} {x : Rows lam} (hx : InInterval x)
    {i : Fin (height lam)} (hi : Removable x i) : addRow (delRow x i) i = x := by
  ext j
  rw [← row_fin, ← row_fin x]
  rw [row_add (del_addable hx hi), row_del]
  unfold Removable at hi
  split <;> (try rw [‹j.val = i.val›]) <;> omega

theorem size_add {lam : List ℕ} {x : Rows lam} {i : Fin (height lam)} (hi : Addable x i) :
    size (addRow x i) = size x + 1 := by
  unfold size
  have he (j : Fin (height lam)) :
      row (addRow x i) j = row x j + if j = i then 1 else 0 := by
    rw [row_add hi]
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj, show j.val ≠ i.val from fun e => hj (Fin.ext e)]
  simp [he, sum_add_distrib]

theorem size_del {lam : List ℕ} {x : Rows lam} (hx : InInterval x)
    {i : Fin (height lam)} (hi : Removable x i) : size (delRow x i) + 1 = size x := by
  rw [← size_add (del_addable hx hi), add_del hx hi]

/-- Inclusion of Young diagrams in row coordinates. -/
def Contained {lam : List ℕ} (x y : Rows lam) : Prop :=
  ∀ i : Fin (height lam), row x i ≤ row y i

/-- The cover relation of the lower interval. -/
def Covers {lam : List ℕ} (y x : Rows lam) : Prop :=
  InInterval y ∧ InInterval x ∧ Contained y x ∧ y ≠ x ∧
    ∀ z : Rows lam, InInterval z → Contained y z → Contained z x → z = y ∨ z = x

theorem removal_covers {lam : List ℕ} {x : Rows lam} (hx : InInterval x)
    {i : Fin (height lam)} (hi : Removable x i) : Covers (delRow x i) x := by
  have hpos : 0 < row x i := Nat.zero_lt_of_lt hi
  refine ⟨del_interval hx hi, hx, ?_, ?_, ?_⟩
  · intro j
    rw [row_del]
    split <;> omega
  · intro e
    have he := congrArg (fun t => row t i.val) e
    rw [row_del, ite_eq_left rfl] at he
    omega
  · intro z _ hyz hzx
    have hyz' := hyz i
    rw [row_del, ite_eq_left rfl] at hyz'
    have hh : row z i = row x i - 1 ∨ row z i = row x i := by have := hzx i; omega
    rcases hh with h | h
    · left
      ext j
      rw [← row_fin, ← row_fin, row_del]
      have hul := hyz j
      have huu := hzx j
      rw [row_del] at hul
      by_cases he : j.val = i.val
      · rw [he, ite_eq_left rfl, h]
      · rw [ite_eq_right he] at hul ⊢
        omega
    · right
      ext j
      rw [← row_fin, ← row_fin]
      have hul := hyz j
      rw [row_del] at hul
      by_cases he : j.val = i.val
      · simpa only [he] using h
      · rw [ite_eq_right he] at hul
        have := hzx j
        omega

theorem covers_iff_removal {lam : List ℕ} {x y : Rows lam} (hx : InInterval x) :
    Covers y x ↔ ∃ i : Fin (height lam), Removable x i ∧ y = delRow x i := by
  constructor
  · rintro ⟨hy, _, hyx, hne, hcover⟩
    have hex : ∃ s : ℕ, s < height lam ∧ row y s < row x s := by
      by_contra hn
      push Not at hn
      apply hne
      ext j
      rw [← row_fin, ← row_fin]
      exact le_antisymm (hyx j) (hn j.val j.isLt)
    let i : Fin (height lam) := ⟨Nat.find hex, (Nat.find_spec hex).1⟩
    have hlt : row y i < row x i := (Nat.find_spec hex).2
    have hprev : prev y i = prev x i := by
      unfold prev
      by_cases hz : i.val = 0
      · rw [ite_eq_left hz, ite_eq_left hz]
      · rw [ite_eq_right hz, ite_eq_right hz]
        have hj : i.val - 1 < i.val := by omega
        let j : Fin (height lam) := ⟨i.val-1, hj.trans i.isLt⟩
        have eq : row y j = row x j := by
          apply le_antisymm (hyx j)
          apply Nat.le_of_not_gt
          intro hh
          exact (Nat.find_min hex hj) ⟨j.isLt, hh⟩
        exact eq
    have ha : Addable y i :=
      ⟨hlt.trans_le (hx i).1, hlt.trans_le (hprev ▸ (hx i).2)⟩
    have hyadd : Contained y (addRow y i) := by
      intro j
      rw [row_add ha]
      split <;> omega
    have haddx : Contained (addRow y i) x := by
      intro j
      rw [row_add ha]
      by_cases hj : j.val = i.val
      · rw [ite_eq_left hj, hj]
        omega
      · rw [ite_eq_right hj]
        exact hyx j
    have heq : addRow y i = x := by
      rcases hcover _ (add_interval hy ha) hyadd haddx with he | he
      · have hh := congrArg (fun t => row t i.val) he
        rw [row_add ha, ite_eq_left rfl] at hh
        omega
      · exact he
    exact ⟨i, heq ▸ add_removable hy ha, by rw [← heq, del_add ha]⟩
  · rintro ⟨i, hi, rfl⟩
    exact removal_covers hx hi

theorem delRow_injective_on_removable {lam : List ℕ} {x : Rows lam}
    {i j : Fin (height lam)} (hi : Removable x i) (he : delRow x i = delRow x j) : i = j := by
  apply Fin.ext
  by_contra hn
  have hf := congrArg (fun t => row t i.val) he
  rw [row_del, row_del, ite_eq_left rfl, ite_eq_right hn] at hf
  have : 0 < row x i := Nat.zero_lt_of_lt hi
  omega

end BalancedPartition
```

### `BalancedTelescoping.lean`

```lean
import BalancedRows
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators
open Finset
namespace BalancedPartition

noncomputable def additions {lam : List ℕ} (x : Rows lam) : Finset (Fin (height lam)) :=
  open Classical in univ.filter (Addable x)

noncomputable def removals {lam : List ℕ} (x : Rows lam) : Finset (Fin (height lam)) :=
  open Classical in univ.filter (Removable x)

@[simp] theorem mem_additions {lam : List ℕ} {x : Rows lam} {i : Fin (height lam)} :
    i ∈ additions x ↔ Addable x i := by
  classical simp [additions]

@[simp] theorem mem_removals {lam : List ℕ} {x : Rows lam} {i : Fin (height lam)} :
    i ∈ removals x ↔ Removable x i := by
  classical simp [removals]

def potential {K : Type*} [CommRing K] (t : K) (lam : List ℕ) (s c : ℕ) : K :=
  t ^ (u lam * s) - t ^ (v lam * (width lam - c))

private theorem balance_exponents {lam : List ℕ} (hp : IsPartition lam) (hb : Balanced lam)
    {s : ℕ} (hs : 1 ≤ s) (hlt : s < height lam) (hdrop : lam[s]! < lam[s-1]!) :
    u lam * s = v lam * (width lam - lam[s]!) := by
  apply Nat.eq_of_mul_eq_mul_right (gcd_pos hp)
  calc
    u lam * s * gcd lam = width lam * s := by
      rw [Nat.mul_right_comm, u_mul_gcd]
    _ = height lam * (width lam - lam[s]!) :=
      ((balanced_iff_diagonal hp).mp hb s hs hlt hdrop).symm
    _ = v lam * (width lam - lam[s]!) * gcd lam := by
      rw [Nat.mul_right_comm, v_mul_gcd]

variable {K : Type*} [CommRing K]

private theorem forbidden_potential (t : K) {lam : List ℕ} (hp : IsPartition lam)
    (hb : Balanced lam) {x : Rows lam} (hx : InInterval x) (i : Fin (height lam))
    (hs : row x i < prev x i) (hf : ¬ row x i < lam[i.val]!) :
    potential t lam i (row x i) = 0 := by
  have he : row x i = lam[i.val]! := by have := (hx i).1; omega
  have hnz : i.val ≠ 0 := by
    intro hz
    rw [he, hz, prev_zero] at hs
    exact Nat.lt_irrefl _ hs
  have hdrop : lam[i.val]! < lam[i.val-1]! := by
    have hprev := (hx ⟨i.val-1, by have := i.isLt; omega⟩).1
    change row x (i.val-1) ≤ lam[i.val-1]! at hprev
    rw [prev, ite_eq_right hnz, he] at hs
    exact hs.trans_le hprev
  unfold potential
  rw [he, balance_exponents hp hb (by omega) i.isLt hdrop, sub_self]

private theorem seam_identity (t : K) {lam : List ℕ} (hp : IsPartition lam)
    (hb : Balanced lam) {x : Rows lam} (hx : InInterval x) :
    (∑ i ∈ additions x, potential t lam i (row x i)) -
      (∑ i ∈ removals x, potential t lam (i.val+1) (row x i)) =
        1 - t ^ area lam := by
  classical
  let P (s : Fin (height lam + 1)) :=
    if row x s < prev x s then potential t lam s (row x s) else 0
  let M (s : Fin (height lam + 1)) :=
    if row x s < prev x s then potential t lam s (prev x s) else 0
  have hpEnd : P (Fin.last _) = 0 := by
    dsimp [P, potential]
    split
    · rw [row_end, Nat.sub_zero, ← area_eq, ← area_eq', sub_self]
    · rfl
  have hmStart : M 0 = 0 := by
    simp [M, potential]
  have hpSum : ∑ s, P s = ∑ i ∈ additions x, potential t lam i (row x i) := by
    rw [Fin.sum_univ_castSucc, hpEnd, add_zero, additions, sum_filter]
    apply sum_congr rfl
    intro i _
    change (if row x i < prev x i then potential t lam i (row x i) else 0) =
      if Addable x i then potential t lam i (row x i) else 0
    by_cases hs : row x i < prev x i
    · by_cases ha : row x i < lam[i.val]!
      · rw [ite_eq_left hs, ite_eq_left (show Addable x i from ⟨ha, hs⟩)]
      · rw [ite_eq_left hs, ite_eq_right (show ¬ Addable x i from fun h => ha h.1)]
        exact forbidden_potential t hp hb hx i hs ha
    · rw [ite_eq_right hs, ite_eq_right (show ¬ Addable x i from fun h => hs h.2)]
  have hmSum : ∑ s, M s = ∑ i ∈ removals x, potential t lam (i.val+1) (row x i) := by
    rw [Fin.sum_univ_succ, hmStart, zero_add, removals, sum_filter]
    apply sum_congr rfl
    intro i _
    change (if row x (i.val+1) < prev x (i.val+1) then
      potential t lam (i.val+1) (prev x (i.val+1)) else 0) = _
    simp only [prev_succ, Removable]
    by_cases h : row x (i.val + 1) < row x i
    · simp only [ite_eq_left h]
      exact (ite_eq_left h).symm
    · simp only [ite_eq_right h]
      exact (ite_eq_right h).symm
  rw [← hpSum, ← hmSum, ← sum_sub_distrib]
  have hd (s : Fin (height lam + 1)) :
      P s - M s = t ^ (v lam * (width lam - prev x s)) -
        t ^ (v lam * (width lam - row x s)) := by
    dsimp only [P, M]
    by_cases hs : row x s < prev x s
    · rw [ite_eq_left hs, ite_eq_left hs]
      unfold potential
      ring
    · rw [ite_eq_right hs, ite_eq_right hs, sub_self]
      have hle : row x s ≤ prev x s := by
        by_cases h : s.val < height lam
        · exact (hx ⟨s.val,h⟩).2
        · have he : s.val = height lam := by have := s.isLt; omega
          rw [he, row_end]
          exact Nat.zero_le _
      rw [le_antisymm hle (Nat.le_of_not_gt hs), sub_self]
  simp_rw [hd]
  rw [sum_sub_distrib]
  rw [Fin.sum_univ_succ (f := fun s : Fin (height lam + 1) =>
    t ^ (v lam * (width lam - prev x s)))]
  rw [Fin.sum_univ_castSucc (f := fun s : Fin (height lam + 1) =>
    t ^ (v lam * (width lam - row x s)))]
  simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last, prev_zero,
    prev_succ, row_end, Nat.sub_self, Nat.sub_zero, Nat.mul_zero, pow_zero, ← area_eq]
  ring

noncomputable def rankSum (t : K) (lam : List ℕ) : K :=
  ∑ x ∈ interval lam, t ^ (v lam * size x)

noncomputable def downSum (t : K) (lam : List ℕ) : K :=
  ∑ x ∈ interval lam, ∑ i ∈ removals x, t ^ (u lam * i.val + v lam * (size x - 1))

private theorem paired_cover (t : K) {lam : List ℕ} {y : Rows lam}
    {i : Fin (height lam)} (hi : Addable y i) :
    t ^ (v lam * size y) * potential t lam i (row y i) -
      t ^ (v lam * size (addRow y i)) *
        potential t lam (i.val+1) (row (addRow y i) i) =
      (1 - t ^ perimeter lam) * t ^ (u lam * i.val + v lam * size y) := by
  have hwall : row y i + 1 ≤ width lam := by
    have h := row_le (addRow y i) i
    rwa [row_add hi, ite_eq_left rfl] at h
  have he : v lam * size (addRow y i) + v lam * (width lam - row (addRow y i) i) =
      v lam * size y + v lam * (width lam - row y i) := by
    rw [size_add hi, row_add hi, ite_eq_left rfl, ← Nat.mul_add, ← Nat.mul_add]
    congr 1
    omega
  rw [potential, potential, mul_sub, mul_sub, ← pow_add, ← pow_add, ← pow_add, ← pow_add, he]
  rw [show v lam * size (addRow y i) + u lam * (i.val + 1) =
      (u lam * i.val + v lam * size y) + perimeter lam by
    rw [size_add hi, perimeter_eq]
    ring, pow_add, Nat.add_comm (v lam * size y)]
  ring

private theorem reindex_additions (lam : List ℕ) (f : Rows lam → Fin (height lam) → K) :
    (∑ x ∈ interval lam, ∑ i ∈ additions x, f x i) =
      ∑ x ∈ interval lam, ∑ i ∈ removals x, f (delRow x i) i := by
  classical
  simp only [additions, removals, sum_filter]
  rw [sum_comm, sum_comm (s := interval lam)]
  apply sum_congr rfl
  intro i _
  rw [← sum_filter, ← sum_filter]
  refine sum_bij (fun y hy => addRow y i) ?_ ?_ ?_ ?_
  · intro y hy
    have hy' := mem_filter.mp hy
    have hyi := mem_interval.mp hy'.1
    exact mem_filter.mpr ⟨mem_interval.mpr (add_interval hyi hy'.2), add_removable hyi hy'.2⟩
  · intro y hy z hz e
    have h := congrArg (fun x => delRow x i) e
    rwa [del_add (mem_filter.mp hy).2, del_add (mem_filter.mp hz).2] at h
  · intro x hx
    have hx' := mem_filter.mp hx
    have hxi := mem_interval.mp hx'.1
    exact ⟨delRow x i, mem_filter.mpr ⟨mem_interval.mpr (del_interval hxi hx'.2),
      del_addable hxi hx'.2⟩, add_del hxi hx'.2⟩
  · intro y hy
    rw [del_add (mem_filter.mp hy).2]

theorem corner_telescoping (t : K) {lam : List ℕ} (hp : IsPartition lam) (hb : Balanced lam) :
    (1 - t ^ perimeter lam) * downSum t lam = (1 - t ^ area lam) * rankSum t lam := by
  classical
  let f (x : Rows lam) (i : Fin (height lam)) :=
    t ^ (v lam * size x) * potential t lam i (row x i)
  let g (x : Rows lam) (i : Fin (height lam)) :=
    t ^ (v lam * size x) * potential t lam (i.val+1) (row x i)
  have h (x : Rows lam) (hx : x ∈ interval lam) :
      (∑ i ∈ additions x, f x i) - (∑ i ∈ removals x, g x i) =
        (1 - t ^ area lam) * t ^ (v lam * size x) := by
    simp only [f, g, ← mul_sum, ← mul_sub, seam_identity t hp hb (mem_interval.mp hx)]
    exact mul_comm _ _
  have hy :
      (∑ x ∈ interval lam, ∑ i ∈ additions x, f x i) -
        (∑ x ∈ interval lam, ∑ i ∈ removals x, g x i) =
        (1 - t ^ area lam) * rankSum t lam := by
    rw [← sum_sub_distrib, rankSum, mul_sum]
    exact sum_congr rfl h
  rw [reindex_additions, ← sum_sub_distrib] at hy
  rw [← hy, downSum, mul_sum]
  apply sum_congr rfl
  intro x hx
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  have hxi := mem_interval.mp hx
  have hir := mem_removals.mp hi
  have ha := del_addable hxi hir
  have he := paired_cover t ha
  rw [add_del hxi hir] at he
  have hs : size (delRow x i) = size x - 1 := by have := size_del hxi hir; omega
  rw [hs] at he
  dsimp only [f, g]
  rw [hs]
  exact he.symm

#check corner_telescoping
#print axioms corner_telescoping
end BalancedPartition
```

### `BalancedExpectation.lean`

```lean
import BalancedTelescoping
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.FieldSimp

open scoped BigOperators
open Finset
noncomputable section
namespace BalancedPartition

abbrev Poly := MvPolynomial (Fin 2) ℚ
abbrev K := FractionRing Poly

def embed : Poly →+* K := algebraMap Poly K
def a : K := embed (MvPolynomial.X 0)
def q : K := embed (MvPolynomial.X 1)

def Waq (b t : K) (n : ℕ) : K :=
  (1 - b * t ^ (1 + 2 * n)) / (1 - b * t) * t ^ (-(n : ℤ))

def aqInt (b t : K) (n : ℕ) : K :=
  (1 - t ^ n) * (1 - b * t ^ n) / ((1 - t) * (1 - b * t)) * t ^ (1 - (n : ℤ))

/-- The weight of the cover marked by row i+1, with i zero-based. -/
def wt {lam : List ℕ} (x : Rows lam) (i : Fin (height lam)) : K :=
  Waq (a * q ^ perimeter lam) q
    ((width lam * i.val + height lam * (size x - 1)) / gcd lam)

def ddeg {lam : List ℕ} (x : Rows lam) : K :=
  ∑ i ∈ removals x, wt x i

def R (lam : List ℕ) : K :=
  ∑ x ∈ interval lam, Waq (a * q ^ area lam) q (height lam * size x / gcd lam)

def Eaq (lam : List ℕ) : K :=
  (∑ x ∈ interval lam, ddeg x) / R lam

def coverRow {lam : List ℕ} {y x : Rows lam} (h : Covers y x) : Fin (height lam) :=
  Classical.choose ((covers_iff_removal h.2.1).mp h)

theorem coverRow_spec {lam : List ℕ} {y x : Rows lam} (h : Covers y x) :
    Removable x (coverRow h) ∧ y = delRow x (coverRow h) :=
  Classical.choose_spec ((covers_iff_removal h.2.1).mp h)

def coverWeight {lam : List ℕ} (x y : Rows lam) : K :=
  open Classical in if h : Covers y x then wt x (coverRow h) else 0

def lowerCovers {lam : List ℕ} (x : Rows lam) : Finset (Rows lam) :=
  open Classical in (interval lam).filter (fun y => Covers y x)

theorem ddeg_eq_sum_covers {lam : List ℕ} {x : Rows lam} (hx : InInterval x) :
    ddeg x = ∑ y ∈ lowerCovers x, coverWeight x y := by
  classical
  unfold ddeg lowerCovers
  refine sum_bij (fun i _ => delRow x i) ?_ ?_ ?_ ?_
  · intro i hi
    have h := removal_covers hx (mem_removals.mp hi)
    exact mem_filter.mpr ⟨mem_interval.mpr h.1, h⟩
  · intro i hi j _ he
    exact delRow_injective_on_removable (mem_removals.mp hi) he
  · intro y hy
    have h := (mem_filter.mp hy).2
    exact ⟨coverRow h, mem_removals.mpr (coverRow_spec h).1, (coverRow_spec h).2.symm⟩
  · intro i hi
    have h := removal_covers hx (mem_removals.mp hi)
    rw [coverWeight, dite_eq_left h]
    exact congrArg (wt x)
      (delRow_injective_on_removable (mem_removals.mp hi) (coverRow_spec h).2)

private theorem embed_ne_zero {p : Poly} (hp : p ≠ 0) : embed p ≠ 0 := by
  intro h
  apply hp
  apply IsFractionRing.injective Poly K
  exact h.trans (map_zero embed).symm

private def ev (t : ℚ) : Poly →+* ℚ :=
  MvPolynomial.eval (fun i => if i = 0 then 0 else t)

@[simp] private theorem ev_a (t : ℚ) : ev t (MvPolynomial.X 0) = 0 := by
  simp [ev]

@[simp] private theorem ev_q (t : ℚ) : ev t (MvPolynomial.X 1) = t := by
  simp [ev]

theorem q_ne_zero : q ≠ 0 := by
  apply embed_ne_zero
  intro h
  have he := congrArg (ev 1) h
  simp only [ev_q, map_zero, one_ne_zero] at he

theorem one_sub_aq_ne (k : ℕ) : 1 - a * q ^ k ≠ 0 := by
  unfold a q
  rw [← map_pow, ← map_mul, ← map_one embed, ← map_sub]
  apply embed_ne_zero
  intro h
  have he := congrArg (ev 1) h
  simp only [map_sub, map_mul, map_pow, map_one, map_zero, ev_a, zero_mul, sub_zero,
    one_ne_zero] at he

theorem one_sub_q_ne {k : ℕ} (hk : 0 < k) : 1 - q ^ k ≠ 0 := by
  unfold q
  rw [← map_pow, ← map_one embed, ← map_sub]
  apply embed_ne_zero
  intro h
  have he := congrArg (ev 0) h
  simp only [map_sub, map_pow, map_one, map_zero, ev_q, zero_pow (Nat.ne_of_gt hk),
    sub_zero, one_ne_zero] at he

private theorem v_pos {lam : List ℕ} (hp : IsPartition lam) : 0 < v lam := by
  by_contra h
  have hz : v lam = 0 := by omega
  have he := v_mul_gcd lam
  rw [hz, zero_mul] at he
  exact (Nat.ne_of_gt hp.1) he.symm

theorem area_pos {lam : List ℕ} (hp : IsPartition lam) : 0 < area lam := by
  rw [area_eq]
  exact Nat.mul_pos (v_pos hp) (hp.2.1 0 hp.1)

theorem perimeter_pos {lam : List ℕ} (hp : IsPartition lam) : 0 < perimeter lam := by
  rw [perimeter_eq]
  have := v_pos hp
  omega

private theorem Waq_expand (j n : ℕ) :
    Waq (a * q ^ j) q n = ((q⁻¹) ^ n - a * q ^ (j+1) * q ^ n) / (1 - a * q ^ (j+1)) := by
  unfold Waq
  rw [show a * q ^ j * q = a * q ^ (j+1) by rw [pow_succ, mul_assoc]]
  rw [zpow_neg, zpow_natCast, inv_pow]
  rw [div_mul_eq_mul_div, sub_mul, one_mul]
  congr 1
  have he : a * q ^ j * q ^ (1 + 2 * n) * (q ^ n)⁻¹ =
      (a * q ^ (j+1) * q ^ n) * (q ^ n * (q ^ n)⁻¹) := by
    rw [show 1 + 2 * n = 1 + n + n by omega]
    simp only [pow_add, pow_one]
    ring
  rw [he, mul_inv_cancel₀ (pow_ne_zero _ q_ne_zero), mul_one]

private def negativePart (j : ℕ) (minus plus : K) : K :=
  minus - a * q ^ (j+1) * plus

private theorem numerator_expand (lam : List ℕ) :
    (∑ x ∈ interval lam, ddeg x) =
      negativePart (perimeter lam) (downSum q⁻¹ lam) (downSum q lam) /
        (1 - a * q ^ (perimeter lam + 1)) := by
  simp only [ddeg, wt, degreeExponent, Waq_expand, negativePart, downSum, mul_sum,
    ← sum_sub_distrib, div_eq_mul_inv, sum_mul]

private theorem R_expand (lam : List ℕ) :
    R lam = negativePart (area lam) (rankSum q⁻¹ lam) (rankSum q lam) /
      (1 - a * q ^ (area lam + 1)) := by
  simp only [R, rankExponent, Waq_expand, negativePart, rankSum, mul_sum,
    ← sum_sub_distrib, div_eq_mul_inv, sum_mul]

private theorem rank_part_ne (lam : List ℕ) :
    negativePart (area lam) (rankSum q⁻¹ lam) (rankSum q lam) ≠ 0 := by
  classical
  let n (x : Rows lam) := v lam * size x
  let M := ∑ x ∈ interval lam, n x
  let p : Poly := (∑ x ∈ interval lam, (MvPolynomial.X 1) ^ (M - n x)) -
    MvPolynomial.X 0 * (MvPolynomial.X 1) ^ (area lam + 1) *
      ∑ x ∈ interval lam, (MvPolynomial.X 1) ^ (M + n x)
  have he : q ^ M * negativePart (area lam) (rankSum q⁻¹ lam) (rankSum q lam) = embed p := by
    unfold negativePart rankSum
    change q ^ M * ((∑ x ∈ interval lam, (q⁻¹) ^ n x) -
      a * q ^ (area lam + 1) * ∑ x ∈ interval lam, q ^ n x) = embed p
    simp only [p, map_sub, map_mul, map_sum, map_pow, show embed (MvPolynomial.X 1) = q from rfl,
      show embed (MvPolynomial.X 0) = a from rfl, mul_sub]
    congr 1
    · rw [mul_sum]
      apply sum_congr rfl
      intro x hx
      have hn : n x ≤ M := single_le_sum (f := n) (fun i _ => Nat.zero_le (n i)) hx
      have hm : q ^ M = q ^ (M - n x) * q ^ n x := by
        rw [← pow_add, Nat.sub_add_cancel hn]
      rw [hm, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ q_ne_zero), mul_one]
    · rw [mul_left_comm (q ^ M), mul_sum]
      simp_rw [pow_add]
  have hp : p ≠ 0 := by
    intro h
    have hc : 0 < (interval lam).card := card_pos.mpr ⟨emptyRows lam, empty_mem lam⟩
    have hev := congrArg (ev 1) h
    simp only [p, map_sub, map_mul, map_sum, map_pow, ev_q, ev_a, one_pow, zero_mul,
      sub_zero, sum_const, nsmul_eq_mul, mul_one, map_zero] at hev
    exact (Nat.ne_of_gt hc) (Nat.cast_eq_zero.mp hev)
  exact fun h => embed_ne_zero hp (by rw [← he, h, mul_zero])

theorem R_ne_zero (lam : List ℕ) : R lam ≠ 0 := by
  rw [R_expand]
  exact div_ne_zero (rank_part_ne lam) (one_sub_aq_ne _)

private theorem inverse_relation {A B : ℕ} {S T : K}
    (h : (1 - (q⁻¹) ^ B) * S = (1 - (q⁻¹) ^ A) * T) :
    q ^ A * (1 - q ^ B) * S = q ^ B * (1 - q ^ A) * T := by
  have hpow (n : ℕ) : q ^ n * (1 - (q⁻¹) ^ n) = -(1 - q ^ n) := by
    rw [inv_pow, mul_sub, mul_one, mul_inv_cancel₀ (pow_ne_zero _ q_ne_zero)]
    ring
  have hh := congrArg (fun z : K => -(q ^ A * q ^ B) * z) h
  calc
    q ^ A * (1 - q ^ B) * S = -(q ^ A * (q ^ B * (1 - (q⁻¹) ^ B)) * S) := by
      rw [hpow]
      ring
    _ = -(q ^ A * q ^ B) * ((1 - (q⁻¹) ^ B) * S) := by ring
    _ = -(q ^ A * q ^ B) * ((1 - (q⁻¹) ^ A) * T) := hh
    _ = -(q ^ B * (q ^ A * (1 - (q⁻¹) ^ A)) * T) := by ring
    _ = q ^ B * (1 - q ^ A) * T := by rw [hpow]; ring

private theorem lift_relation {A B : ℕ} {Sp Sm Tp Tm : K}
    (hpos : (1 - q ^ B) * Sp = (1 - q ^ A) * Tp)
    (hinv : (1 - (q⁻¹) ^ B) * Sm = (1 - (q⁻¹) ^ A) * Tm) :
    q ^ A * (1 - q ^ B) * negativePart B Sm Sp =
      q ^ B * (1 - q ^ A) * negativePart A Tm Tp := by
  have hneg := inverse_relation hinv
  have he : q ^ A * q ^ (B+1) = q ^ B * q ^ (A+1) := by
    rw [← pow_add, ← pow_add, Nat.add_left_comm A B]
  calc
    q ^ A * (1 - q ^ B) * negativePart B Sm Sp =
        q ^ A * (1 - q ^ B) * Sm - a * (q ^ A * q ^ (B+1)) * ((1 - q ^ B) * Sp) := by
      unfold negativePart
      ring
    _ = q ^ B * (1 - q ^ A) * negativePart A Tm Tp := by
      rw [hneg, he, hpos]
      unfold negativePart
      ring

private theorem aqInt_expand (j n : ℕ) :
    aqInt (a * q ^ j) q n =
      (1 - q ^ n) * (1 - a * q ^ (j+n)) * q /
        ((1 - q) * (1 - a * q ^ (j+1)) * q ^ n) := by
  unfold aqInt
  rw [show a * q ^ j * q = a * q ^ (j+1) by rw [pow_succ, mul_assoc]]
  rw [mul_assoc a, ← pow_add, zpow_sub₀ q_ne_zero, zpow_one, zpow_natCast, div_mul_div_comm]

theorem one_sub_q_ne_one : 1 - q ≠ 0 := by
  simpa only [pow_one] using one_sub_q_ne (k := 1) (by decide)

theorem aqInt_ne (j : ℕ) {n : ℕ} (hn : 0 < n) : aqInt (a * q ^ j) q n ≠ 0 := by
  rw [aqInt_expand]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (one_sub_q_ne hn) (one_sub_aq_ne _)) q_ne_zero)
    (mul_ne_zero (mul_ne_zero one_sub_q_ne_one (one_sub_aq_ne _))
      (pow_ne_zero _ q_ne_zero))

/-- Kim–Schlosser–Yoo, Appendix A, Conjecture A.2, in the two-variable fraction field. -/
theorem ksy_conjA2 (lam : List ℕ) (hp : IsPartition lam) (hb : Balanced lam) :
    Eaq lam = aqInt (a * q ^ ((width lam + height lam) / gcd lam)) q
        (width lam * height lam / gcd lam) /
      aqInt (a * q ^ (width lam * height lam / gcd lam)) q
        ((width lam + height lam) / gcd lam) := by
  change Eaq lam = aqInt (a * q ^ perimeter lam) q (area lam) /
    aqInt (a * q ^ area lam) q (perimeter lam)
  have hl := lift_relation (corner_telescoping q hp hb) (corner_telescoping q⁻¹ hp hb)
  unfold Eaq
  apply (div_eq_div_iff (R_ne_zero lam) (aqInt_ne _ (perimeter_pos hp))).2
  rw [R_expand, numerator_expand, aqInt_expand, aqInt_expand,
    Nat.add_comm (area lam) (perimeter lam)]
  field_simp [q_ne_zero, one_sub_q_ne_one, one_sub_aq_ne]
  simp only [one_div]
  convert hl using 1
  ring

#check ksy_conjA2
#print axioms ksy_conjA2
#check ddeg_eq_sum_covers
#print axioms ddeg_eq_sum_covers
#check R_ne_zero
#print axioms R_ne_zero
end BalancedPartition
```
