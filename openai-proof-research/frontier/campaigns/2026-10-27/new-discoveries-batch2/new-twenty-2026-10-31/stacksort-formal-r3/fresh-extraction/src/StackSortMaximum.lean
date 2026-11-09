import StackSortSplit
noncomputable section
namespace StackSort
open BigOperators

def family (n : ℕ) : Finset (List ℕ) := Nat.rec {[]} (fun k F =>
    F.image (List.cons k) ∪ F.image (fun w => w ++ [k])) n
@[simp] theorem family_zero : family 0 = {[]} := rfl
 theorem family_succ (n : ℕ) : family (n+1) =
    (family n).image (List.cons n) ∪ (family n).image (fun w => w ++ [n]) := rfl

theorem family_perm (n : ℕ) (w : List ℕ) (hw : w ∈ family n) : w.Perm (List.range n) := by
  induction n generalizing w with
  | zero => simpa [family_zero, family_succ] using hw
  | succ n ih =>
    simp only [family_succ, Finset.mem_union, Finset.mem_image] at hw
    rw [List.range_succ]
    rcases hw with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · exact ((ih v hv).cons n).trans (by simpa using List.perm_append_comm (l₁ := [n]) (l₂ := List.range n))
    · exact (ih v hv).append_right [n]

theorem family_sorts (n : ℕ) (w : List ℕ) (hw : w ∈ family n) : s w = List.range n := by
  induction n generalizing w with
  | zero =>
    have : w = [] := by simpa [family_zero, family_succ] using hw
    subst w
    rfl
  | succ n ih =>
    simp only [family_succ, Finset.mem_union, Finset.mem_image] at hw
    rcases hw with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · have hb : ∀ x ∈ v, x ≤ n := fun x hx =>
        (List.mem_range.mp ((family_perm n v hv).mem_iff.mp hx)).le
      have hs := s_split [] v n (by simp) hb
      simpa only [List.nil_append, show s [] = [] from rfl, ih v hv, List.range_succ] using hs
    · have hb : ∀ x ∈ v, x < n := fun x hx =>
        List.mem_range.mp ((family_perm n v hv).mem_iff.mp hx)
      have hs := s_split v [] n hb (by simp)
      simpa only [List.append_nil, show s [] = [] from rfl, ih v hv, List.range_succ] using hs

theorem family_length (n : ℕ) (w : List ℕ) (hw : w ∈ family n) : w.length = n := by
  simpa using (family_perm n w hw).length_eq

theorem family_card_succ (n : ℕ) : (family (n + 1)).card = 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hdis : Disjoint ((family (n+1)).image (List.cons (n+1)))
        ((family (n+1)).image (fun w => w ++ [n+1])) := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      rcases Finset.mem_image.mp h1 with ⟨v, hv, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨u, hu, he⟩
      have hul : u ≠ [] := by
        intro hz; have hl := family_length (n+1) u hu; simp [hz] at hl
      cases u with
      | nil => contradiction
      | cons x xs =>
        have hx : x = n+1 := List.cons.inj he |>.1
        have hp := family_perm (n+1) (x :: xs) hu
        have hmem : x < n+1 := List.mem_range.mp (hp.mem_iff.mp (by simp))
        omega
    rw [family_succ, Finset.card_union_of_disjoint hdis,
      Finset.card_image_of_injective _ (fun _ _ h => List.cons.inj h |>.2),
      Finset.card_image_of_injective _ (fun _ _ h => List.append_cancel_right h), ih, pow_succ]
    omega

theorem max_family_bound (n : ℕ) : 2 ^ (n - 1) ≤ maxFib n := by
  have hnon : (family n).Nonempty := by
    cases n with
    | zero => simp [family_zero]
    | succ n => rw [← Finset.card_pos, family_card_succ]; positivity
  obtain ⟨w, hw⟩ := hnon
  have hsub : family n ⊆ fibre n (s w) := by
    intro v hv
    simp only [fibre, Finset.mem_filter]
    exact ⟨mem_words.mpr (family_perm n v hv), (family_sorts n v hv).trans (family_sorts n w hw).symm⟩
  have hb := Finset.card_le_card hsub
  have hm : (fibre n (s w)).card ≤ maxFib n := Finset.le_sup (f := fun w => (fibre n (s w)).card)
    (mem_words.mpr (family_perm n w hw))
  have hc : (family n).card = 2 ^ (n - 1) := by
    cases n with
    | zero => decide
    | succ n => simpa using family_card_succ n
  rw [hc] at hb
  exact hb.trans hm
end StackSort
