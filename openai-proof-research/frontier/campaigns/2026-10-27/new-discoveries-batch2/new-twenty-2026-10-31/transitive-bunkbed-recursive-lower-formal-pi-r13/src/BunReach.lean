/-
# Bunkbed E7 (r2): prefix-state lemmas, part 1

Indicator algebra of the exact new-index closure; the prefix state depends only on the
window restriction (start state and horizontal-entry disjunction included).
-/
import BunState

namespace Bun

/-- Closed form, left component: `A ↔ X ∨ (Z ∧ B)`. -/
theorem ind_fst (x y z : Bool) :
    (ind x y z).1 = true ↔ x = true ∨ (z = true ∧ (ind x y z).2 = true) := by
  cases x <;> cases y <;> cases z <;> simp [ind]

/-- Closed form, right component: `B ↔ Y ∨ (Z ∧ A)`. -/
theorem ind_snd (x y z : Bool) :
    (ind x y z).2 = true ↔ y = true ∨ (z = true ∧ (ind x y z).1 = true) := by
  cases x <;> cases y <;> cases z <;> simp [ind]

theorem ind_fst_or {x y z : Bool} (hx : x = true) : (ind x y z).1 = true :=
  (ind_fst x y z).mpr (Or.inl hx)

theorem ind_fst_vert {x y z : Bool} (hz : z = true) (hb : (ind x y z).2 = true) :
    (ind x y z).1 = true :=
  (ind_fst x y z).mpr (Or.inr ⟨hz, hb⟩)

theorem ind_snd_or {x y z : Bool} (hy : y = true) : (ind x y z).2 = true :=
  (ind_snd x y z).mpr (Or.inl hy)

theorem ind_snd_vert {x y z : Bool} (hz : z = true) (hb : (ind x y z).1 = true) :
    (ind x y z).2 = true :=
  (ind_snd x y z).mpr (Or.inr ⟨hz, hb⟩)

theorem startST_congr (n j : Nat) {w w' : Asg n j} (hw : ∀ t : Win n j, w t = w' t) :
    startST n j w = startST n j w' := by
  unfold startST
  split
  · rename_i hj
    rw [hw (fresV (n := n) (m := j) hj)]
  · rfl

theorem hor_congr {n m : Nat} (hm : m < n) {R R' : Finset Nat} (hR : R = R')
    {w w' : Asg n m} (hw : ∀ t : Win n m, w t = w' t) (l : Bool) :
    hor hm R l w = hor hm R' l w' := by
  unfold hor
  apply congrArg (fun S : Finset _ => decide S.Nonempty)
  apply Finset.filter_congr
  intro t _hc
  have hwt : w (fresH hm t.1 (Finset.mem_range.mp t.2) l) =
      w' (fresH hm t.1 (Finset.mem_range.mp t.2) l) := hw _
  by_cases hmem : t.1 ∈ R
  · have hmem' : t.1 ∈ R' := by rw [← hR]; exact hmem
    simp only [decide_eq_true hmem, decide_eq_true hmem', hwt]
  · have hmem' : ¬ (t.1 ∈ R') := fun hc => hmem (by rw [hR]; exact hc)
    simp only [decide_eq_false hmem, decide_eq_false hmem', hwt]

/-- The prefix state is unchanged when the window assignments agree. -/
theorem stf_congr (n u : Nat) : ∀ j : Nat, ∀ w w' : Asg n j,
    (∀ t : Win n j, w t = w' t) → stf n u j w = stf n u j w' := by
  intro j
  induction j with
  | zero =>
      intro w w' hw
      by_cases hue : u = 0
      · have h1 : stf n u 0 w = startST n 0 w := by
          simp only [stf]; split <;> rfl
        have h2 : stf n u 0 w' = startST n 0 w' := by
          simp only [stf]; split <;> rfl
        rw [h1, h2]
        exact startST_congr n 0 hw
      · have h : ∀ v : Asg n 0, stf n u 0 v = ((∅ : Finset Nat), ∅) := by
          intro v; simp only [stf]; split
          · rename_i hn; exact absurd hn hue
          · rfl
        rw [h w, h w']
  | succ j ih =>
      intro w w' hw
      have hres : ∀ t : Win n j, res n j w t = res n j w' t := fun t =>
        hw ⟨t.1, Nat.le_trans t.2 (Nat.le_succ j)⟩
      simp only [stf]
      split
      · rfl
      split
      · exact startST_congr n (j+1) hw
      · rename_i _ hIEQ
        split
        · rename_i hLT
          rw [ih (res n j w) (res n j w') hres]
          unfold stepU
          rw [hor_congr hLT rfl hw, hor_congr hLT rfl hw, hw (fresV (n := n) (m := j + 1) hLT)]
        · exact ih (res n j w) (res n j w') hres

end Bun
