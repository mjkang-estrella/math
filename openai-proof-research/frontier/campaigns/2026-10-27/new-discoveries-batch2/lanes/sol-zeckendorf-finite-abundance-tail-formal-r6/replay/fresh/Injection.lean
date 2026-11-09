import Boards
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LiteralGame
def SuccessAt (w : List Move) (j : ℕ) : Prop :=
  ∃ u v, u.length=3*j ∧ w=u ++ [.C1,.C1,C2] ++ v
noncomputable def successSlots (J : ℕ) (w : List Move) : Finset ℕ := by
  classical
  exact (Finset.range J).filter (SuccessAt w)
noncomputable def successIndex (w : List Move) (j : ℕ) : ℕ :=
  (compress (w.take (3*j+2))).length

theorem compress_take_mono (w : List Move) {i j : ℕ} (h : i ≤ j) :
    (compress (w.take i)).length ≤ (compress (w.take j)).length := by
  have he : w.take j = w.take i ++ (w.take j).drop i := by
    simpa [List.take_take,Nat.min_eq_left h] using
      (List.take_append_drop i (w.take j)).symm
  conv_rhs => rw [he]
  exact compress_length_mono _ _

theorem success_take {w : List Move} {j : ℕ} (h : SuccessAt w j) :
    ∃ u, w.take (3*j+2) = u ++ [.C1,.C1] ∧
      w.take (3*j+3) = u ++ [.C1,.C1,C2] := by
  obtain ⟨u,v,hl,rfl⟩ := h
  refine ⟨u,?_,?_⟩
  · rw [← hl]
    simp [List.take_append,List.take_append_of_le_length,List.append_assoc]
  · rw [← hl]
    simp [List.take_append,List.append_assoc]

theorem successIndex_strict {w : List Move} {j k : ℕ}
    (hj : SuccessAt w j) (hjk : j<k) : successIndex w j < successIndex w k := by
  obtain ⟨u,h2,h3⟩ := success_take hj
  have hm := compress_take_mono w (show 3*j+3 ≤ 3*k+2 by omega)
  rw [h3] at hm
  have he : u ++ [.C1,.C1,C2] = (u ++ [.C1,.C1]) ++ [C2] := by
    simp [List.append_assoc]
  rw [he,compress_append_C2] at hm
  simp only [List.length_append,List.length_cons,List.length_nil,compress] at hm
  dsimp [successIndex]
  rw [h2]
  omega

theorem successIndex_marked {a c : Board} {w : List Move} {j : ℕ}
    (hw : Executes a w c) (hj : SuccessAt w j) :
    successIndex w j ∈ markedSlots a (compress w) := by
  obtain ⟨u,v,hl,he⟩ := hj
  have ht : w.take (3*j+2) = u ++ [.C1,.C1] := by
    rw [he,← hl]
    simp [List.take_append,List.append_assoc]
  rw [he] at hw ⊢
  obtain ⟨b,hu,hrest⟩ := executes_split (u:=u) (by simpa [List.append_assoc] using hw)
  cases hrest with
  | cons h1 hr => cases hr with
    | cons h2 hr => cases hr with
      | cons h3 _ =>
        have hm := successful_triple_mark (v:=v) hu h1 h2 h3
        simpa [successIndex,← he,ht] using hm

theorem success_count_le_marks {a c : Board} {w : List Move}
    (hw : Executes a w c) (J : ℕ) :
    (successSlots J w).card ≤ (markedSlots a (compress w)).card := by
  classical
  apply Finset.card_le_card_of_injOn (f:=successIndex w)
  · intro j hj
    exact successIndex_marked hw (Finset.mem_filter.mp hj).2
  · intro j hj k hk he
    have hs := (Finset.mem_filter.mp hj).2
    have ht := (Finset.mem_filter.mp hk).2
    rcases lt_trichotomy j k with h | h | h
    · exact False.elim ((ne_of_lt (successIndex_strict hs h)) he)
    · exact h
    · exact False.elim ((ne_of_lt (successIndex_strict ht h)) he.symm)
end LiteralGame
