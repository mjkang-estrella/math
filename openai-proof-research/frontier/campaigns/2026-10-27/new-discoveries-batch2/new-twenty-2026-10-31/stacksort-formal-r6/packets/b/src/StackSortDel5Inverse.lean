import StackSortDel5Core
namespace StackSort.Del5
open Seeds2 Round4

/-- All root insertions into a specified suffix. Unary orientation is retained. -/
def childChoices : List (List ℕ) → Finset Children
  | [] => {.leaf}
  | [w] => if h : w = [] then ∅ else
      {.unary false ⟨w,h⟩, .unary true ⟨w,h⟩}
  | [L,R] => if hL : L = [] then ∅ else if hR : R = [] then ∅ else
      {.binary ⟨L,hL⟩ ⟨R,hR⟩}
  | _ => ∅

theorem child_mem_choices (c : Children) : c ∈ childChoices (childrenTuple c) := by
  cases c with
  | leaf => simp [childrenTuple, childChoices]
  | unary b w => cases b <;> simp [childrenTuple, childChoices, w.property]
  | binary L R => simp [childrenTuple, childChoices, L.property, R.property]

theorem choices_tuple {F : List (List ℕ)} {c : Children}
    (h : c ∈ childChoices F) : childrenTuple c = F := by
  cases F with
  | nil =>
    have he : c = .leaf := by simpa [childChoices] using h
    subst c; rfl
  | cons w F =>
    cases F with
    | nil =>
      by_cases hw : w = []
      · simp [childChoices,hw] at h
      · simp only [childChoices, dite_eq_right hw, Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl <;> rfl
    | cons v F =>
      cases F with
      | nil =>
        by_cases hw : w = []
        · simp [childChoices,hw] at h
        · by_cases hv : v = []
          · simp [childChoices,hw,hv] at h
          · simp only [childChoices,dite_eq_right hw,dite_eq_right hv,Finset.mem_singleton] at h
            subst c; rfl
      | cons u F => simp [childChoices] at h

theorem mem_childChoices_iff {F : List (List ℕ)} {c : Children} :
    c ∈ childChoices F ↔ childrenTuple c = F := by
  constructor
  · exact choices_tuple
  · rintro rfl; exact child_mem_choices c

/-- The actual suffix fibers have the required 1,2,1 multiplicities. -/
theorem childChoices_card {F : List (List ℕ)} (hn : NonemptyWords F)
    (hl : F.length ≤ 2) : (childChoices F).card = mu F.length := by
  cases F with
  | nil => simp [childChoices,mu]
  | cons w F =>
    have hw := hn w (by simp)
    cases F with
    | nil => simp [childChoices,hw,mu]
    | cons v F =>
      have hv := hn v (by simp)
      have hF : F = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hl; omega)
      subst F
      simp [childChoices,hw,hv,mu]

/-- Prefix length fixes the split uniquely; the finite suffix fiber retains its orientations. -/
theorem reduced_split_unique {A B : List (List ℕ)} {c d : Children}
    (hl : A.length = B.length)
    (he : A ++ childrenTuple c = B ++ childrenTuple d) :
    A = B ∧ childrenTuple c = childrenTuple d := List.append_inj he hl

/-- Every short nonempty-word suffix has a root reconstruction. -/
theorem choices_nonempty {F : List (List ℕ)} (hn : NonemptyWords F)
    (hl : F.length ≤ 2) : (childChoices F).Nonempty := by
  apply Finset.card_pos.mp
  rw [childChoices_card hn hl]
  unfold mu
  split_ifs <;> omega

/-- Recover the deleted root from precisely the final t reduced words. -/
theorem reconstruct_suffix (F : List (List ℕ)) (k t : ℕ)
    (hn : NonemptyWords F) (hl : F.length = k+t) (ht : t ≤ 2) :
    ∃ c ∈ childChoices (F.drop k),
      childrenArity c = t ∧ F.take k ++ childrenTuple c = F := by
  have hd : NonemptyWords (F.drop k) := fun w hw => hn w (List.mem_of_mem_drop hw)
  have hlen : (F.drop k).length = t := by simp [hl]
  obtain ⟨c,hc⟩ := choices_nonempty hd (by omega)
  have he := choices_tuple hc
  refine ⟨c,hc,?_,?_⟩
  · rw [← childrenTuple_length,he,hlen]
  · rw [he]; exact List.take_append_drop k F
end StackSort.Del5
