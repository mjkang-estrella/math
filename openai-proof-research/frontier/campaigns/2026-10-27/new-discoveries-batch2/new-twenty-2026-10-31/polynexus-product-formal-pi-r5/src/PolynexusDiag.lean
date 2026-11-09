import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal

/-!
# Polynexus coupled diagonal blocks (MathDB 352496) — entry semantics and guards

Faithful zero-based model of the source rook-diagram blocks of arXiv:2111.01863
as independently reviewed: a block is ONE diagonal segment, i.e. all occupied
entries share a single common offset.  The entry of `PBlk n a b e` at bounded
coordinates `r s` is `1` exactly when for one `t ≤ e` we have `r = a + t` and
`s = b + t`; equivalently the interval bounds `a ≤ r ≤ a+e`, `b ≤ s ≤ b+e`
TOGETHER WITH the coupling `s + a = r + b`.  Independent row/column intervals
(rectangles) are NOT the model.

Semantic guards proved here, about the production definition itself:
occupied common-offset entries, the corner entry `(a,b)`, nonvanishing of
every legal block, and the full-length block `B(0,0,n-1)` having identity
(Kronecker) entries with off-diagonal entries zero.
-/

/-- The coupled entry condition: interval bounds plus the same-offset
equality.  `PCnd a b e r s` holds iff the `(r, s)` entry of `B(a,b,e)` is `1`. -/
abbrev PCnd (a b e r s : ℕ) : Prop :=
  a ≤ r ∧ r ≤ a + e ∧ b ≤ s ∧ s ≤ b + e ∧ s + a = r + b

/-- The coupled diagonal block `B(a,b,e)` on `Fin n` coordinates: entry `1`
exactly on one common-offset diagonal segment, `0` elsewhere. -/
def PBlk (n a b e : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun r s => if PCnd a b e (r : ℕ) (s : ℕ) then 1 else 0

theorem PBlk_apply (n a b e : ℕ) (r s : Fin n) :
    PBlk n a b e r s = if PCnd a b e (r : ℕ) (s : ℕ) then 1 else 0 := rfl

/-- Entry dichotomy with the exact condition, instance-free. -/
theorem PBlk_cases (n a b e : ℕ) (r s : Fin n) :
    (PBlk n a b e r s = 1 ∧ PCnd a b e (↑r) (↑s)) ∨
      (PBlk n a b e r s = 0 ∧ ¬ PCnd a b e (↑r) (↑s)) := by
  rw [PBlk_apply]
  by_cases h : PCnd a b e (↑r) (↑s)
  · rw [ite_eq_left h]
    exact Or.inl ⟨rfl, h⟩
  · rw [ite_eq_right h]
    exact Or.inr ⟨rfl, h⟩

theorem PBlk_eq_one {n a b e : ℕ} {r s : Fin n} (h : PCnd a b e ↑r ↑s) :
    PBlk n a b e r s = 1 := by
  rcases PBlk_cases n a b e r s with ⟨h1, _⟩ | ⟨h1, hneg⟩
  · exact h1
  · exact absurd h hneg

theorem PBlk_eq_zero {n a b e : ℕ} {r s : Fin n} (h : ¬ PCnd a b e ↑r ↑s) :
    PBlk n a b e r s = 0 := by
  rcases PBlk_cases n a b e r s with ⟨h1, hc⟩ | ⟨h1, _⟩
  · exact absurd hc h
  · exact h1

theorem PBlk_eq_one_iff (n a b e : ℕ) (r s : Fin n) :
    PBlk n a b e r s = 1 ↔ PCnd a b e ↑r ↑s := by
  constructor
  · intro hval
    rcases PBlk_cases n a b e r s with ⟨_, hc⟩ | ⟨h0, hneg⟩
    · exact hc
    · exfalso
      rw [hval] at h0
      omega
  · intro h
    exact PBlk_eq_one h

theorem PBlk_eq_zero_iff (n a b e : ℕ) (r s : Fin n) :
    PBlk n a b e r s = 0 ↔ ¬ PCnd a b e ↑r ↑s := by
  constructor
  · intro hval
    rcases PBlk_cases n a b e r s with ⟨h1, hc⟩ | ⟨_, hneg⟩
    · exfalso
      rw [hval] at h1
      omega
    · exact hneg
  · intro h
    exact PBlk_eq_zero h

/-- The reviewed equivalence: the coupled condition holds iff both coordinates
are reached by one common offset `t ≤ e`.  No truncated subtraction: the
witness is constructed inside `omega`'s fragment-free bookkeeping. -/
theorem PCnd_iff_t {a b e r s : ℕ} :
    PCnd a b e r s ↔ ∃ t, t ≤ e ∧ a + t = r ∧ b + t = s := by
  constructor
  · rintro ⟨har, hre, hbs, hse, heq⟩
    refine ⟨r - a, ?_, ?_, ?_⟩
    <;> omega
  · rintro ⟨t, hle, hr, hs⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    <;> omega

/-- Semantic guard: every common-offset point in range is occupied with entry `1`. -/
theorem PBlk_occupied_one {n a b e t : ℕ} (hte : t ≤ e) (hr : a + t < n) (hs : b + t < n) :
    PBlk n a b e ⟨a + t, hr⟩ ⟨b + t, hs⟩ = 1 := by
  refine PBlk_eq_one ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_add_right a t
  · exact Nat.add_le_add_left hte a
  · exact Nat.le_add_right b t
  · exact Nat.add_le_add_left hte b
  · show (b + t) + a = (a + t) + b
    omega

/-- Semantic guard: the start corner `(a, b)` of a block carries entry `1`. -/
theorem PBlk_corner_one {n a b e : ℕ} (ha : a < n) (hb : b < n) :
    PBlk n a b e ⟨a, ha⟩ ⟨b, hb⟩ = 1 := by
  refine PBlk_eq_one ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact le_refl a
  · exact Nat.le_add_right a e
  · exact le_refl b
  · exact Nat.le_add_right b e
  · show b + a = a + b
    exact Nat.add_comm b a

/-- Every block with in-range start corner is nonzero. -/
theorem PBlk_ne_zero {n a b e : ℕ} (ha : a < n) (hb : b < n) : PBlk n a b e ≠ 0 := by
  intro hcon
  have h1 : PBlk n a b e ⟨a, ha⟩ ⟨b, hb⟩ = 1 := PBlk_corner_one (e := e) ha hb
  rw [hcon, Matrix.zero_apply] at h1
  omega

/-- Semantic guard: diagonal entries of the full-length block are `1`. -/
theorem PBlkId_diag (n : ℕ) (i : Fin n) : PBlk n 0 0 (n - 1) i i = 1 := by
  have hlt : (i : ℕ) < n := Fin.isLt i
  refine PBlk_eq_one ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.zero_le _
  · omega
  · exact Nat.zero_le _
  · omega
  · rfl

/-- Semantic guard: off-diagonal entries of the full-length block are `0`
(the coupling forces equal coordinates). -/
theorem PBlkId_offdiag (n : ℕ) (r s : Fin n) (hne : (r : ℕ) ≠ (s : ℕ)) :
    PBlk n 0 0 (n - 1) r s = 0 := by
  refine PBlk_eq_zero ?_
  rintro ⟨_, _, _, _, heq⟩
  exact hne (by omega)

/-- The full-length block `B(0,0,n-1)` is exactly the identity matrix. -/
theorem PBlkId (n : ℕ) : PBlk n 0 0 (n - 1) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply, ite_eq_left rfl]
    exact PBlkId_diag _ _
  · rw [Matrix.one_apply, ite_eq_right h]
    refine PBlkId_offdiag n _ _ ?_
    intro hval
    exact h (Fin.val_inj.mp hval)

/-! ### Natural-index entry interface

All later modules access entries through bounded natural coordinates; these
lemmas transport the Fin-indexed definition to plain natural `PCnd`s. -/

/-- Entry value at bounded natural coordinates, with plain natural condition. -/
theorem PBlk_entry_nat (n a b e r s : ℕ) (hr : r < n) (hs : s < n) :
    PBlk n a b e ⟨r, hr⟩ ⟨s, hs⟩ = if PCnd a b e r s then 1 else 0 := by
  show (if PCnd a b e (⟨r, hr⟩ : Fin n).val (⟨s, hs⟩ : Fin n).val then 1 else 0)
      = (if PCnd a b e r s then 1 else 0)
  congr 1

theorem PBlk_one_nat {n a b e r s : ℕ} (hr : r < n) (hs : s < n) (h : PCnd a b e r s) :
    PBlk n a b e ⟨r, hr⟩ ⟨s, hs⟩ = 1 := by
  rw [PBlk_entry_nat n a b e r s hr hs]
  exact ite_eq_left h

theorem PBlk_zero_nat {n a b e r s : ℕ} (hr : r < n) (hs : s < n) (h : ¬ PCnd a b e r s) :
    PBlk n a b e ⟨r, hr⟩ ⟨s, hs⟩ = 0 := by
  rw [PBlk_entry_nat n a b e r s hr hs]
  exact ite_eq_right h

theorem PBlk_one_iff_nat (n a b e r s : ℕ) (hr : r < n) (hs : s < n) :
    PBlk n a b e ⟨r, hr⟩ ⟨s, hs⟩ = 1 ↔ PCnd a b e r s := by
  by_cases h : PCnd a b e r s
  · rw [PBlk_entry_nat n a b e r s hr hs, ite_eq_left h]
    exact iff_of_true rfl h
  · rw [PBlk_entry_nat n a b e r s hr hs, ite_eq_right h]
    exact iff_of_false zero_ne_one h
