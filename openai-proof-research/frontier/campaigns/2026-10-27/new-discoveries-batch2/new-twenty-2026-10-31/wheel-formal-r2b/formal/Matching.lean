import CycleBounds
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
open scoped BigOperators
namespace WheelFormal

/-- A finite edge pairing, allowing fixed vertices, bounds every independent set. -/
theorem pairing_bound {V : Type} [DecidableEq V]
    (S I : Finset V) (p : V → V) (hp : Function.Involutive p)
    (hS : ∀ x ∈ S, p x ∈ S) (hI : I ⊆ S)
    (hInd : ∀ x ∈ I, p x ∈ I → p x = x) :
    2*I.card ≤ S.card + (S.filter (fun x => p x = x)).card := by
  classical
  have hc : (I.image p).card = I.card := Finset.card_image_of_injective _ hp.injective
  have hu : I ∪ I.image p ⊆ S := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hI hx
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact hS y (hI hy)
  have hi : I ∩ I.image p ⊆ S.filter (fun x => p x = x) := by
    intro x hx
    obtain ⟨hx,hy⟩ := Finset.mem_inter.mp hx
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hy
    have hpx : p x ∈ I := by rw [← he, hp]; exact hy
    exact Finset.mem_filter.mpr ⟨hI hx,hInd x hx hpx⟩
  have h₁ := Finset.card_le_card hu
  have h₂ := Finset.card_le_card hi
  have h₃ := Finset.card_union_add_card_inter I (I.image p)
  omega

/-- Delete vertices from a pairing by fixing their partners. -/
def deletePair {V : Type} [DecidableEq V] (A : Finset V) (p : V → V) (x : V) : V :=
  if x ∈ A ∨ p x ∈ A then x else p x

theorem deletePair_involutive {V : Type} [DecidableEq V]
    (A : Finset V) (p : V → V) (hp : Function.Involutive p) :
    Function.Involutive (deletePair A p) := by
  intro x
  by_cases hx : p x ∈ A
  · simp [deletePair, hx]
  · by_cases ha : x ∈ A
    · simp only [deletePair, hx, ha, hp x, or_self, ite_false, ite_true, false_or, or_false]
    · simp only [deletePair, hx, ha, hp x, or_self, ite_false, ite_true, false_or, or_false]

/-- On the complement, deletion introduces at most |A|-1 fixed points
when the original pairing's only fixed point is an element of A. -/
theorem deletePair_fixed_bound {V : Type} [Fintype V] [DecidableEq V]
    (A : Finset V) (p : V → V) (hp : Function.Involutive p)
    (a : V) (ha : a ∈ A) (hfix : ∀ x, p x = x ↔ x = a) :
    (Aᶜ.filter (fun x => deletePair A p x = x)).card ≤ A.card-1 := by
  classical
  have hm : ∀ x ∈ Aᶜ.filter (fun x => deletePair A p x = x), p x ∈ A.erase a := by
    intro x hx
    obtain ⟨hx,hq⟩ := Finset.mem_filter.mp hx
    have hn : x ∉ A := Finset.mem_compl.mp hx
    have hpa : p x ∈ A := by
      by_contra hh
      have hpx : p x = x := by simpa [deletePair, hn, hh] using hq
      have hxa := (hfix x).mp hpx
      exact hn (hxa ▸ ha)
    refine Finset.mem_erase.mpr ⟨?_,hpa⟩
    intro he
    have haa : p a = a := (hfix a).mpr rfl
    have hxa : x = a := by simpa [hp x, haa] using congrArg p he
    exact hn (hxa ▸ ha)
  have hc := Finset.card_le_card_of_injOn p hm (fun _ _ _ _ h => hp.injective h)
  simpa [Finset.card_erase_of_mem ha] using hc

/-- Rotate the near-perfect cycle matching so its only fixed vertex is a. -/
def anchoredPair (t : ℕ) (a x : ZMod (2*t+1)) : ZMod (2*t+1) :=
  cyclePair t (x-a)+a

theorem anchoredPair_involutive (t : ℕ) (a : ZMod (2*t+1)) :
    Function.Involutive (anchoredPair t a) := by
  intro x
  simp only [anchoredPair, add_sub_cancel_right, (cyclePair_spec t _).1, sub_add_cancel]

theorem anchoredPair_fixed (t : ℕ) (a x : ZMod (2*t+1)) :
    anchoredPair t a x = x ↔ x = a := by
  have hf := (cyclePair_spec t (x-a)).2.1
  constructor
  · intro h
    have hh : cyclePair t (x-a) = x-a := by unfold anchoredPair at h; linear_combination h
    exact sub_eq_zero.mp (hf.mp hh)
  · intro h; subst x; simp [anchoredPair, cyclePair]

theorem anchoredPair_edge (t : ℕ) (a x : ZMod (2*t+1))
    (hx : x ≠ a) : rimAdj (2*t+1) x (anchoredPair t a x) := by
  have he := (cyclePair_spec t (x-a)).2.2 (sub_ne_zero.mpr hx)
  rcases he with ⟨hn, he | he⟩
  · constructor
    · intro hh; apply hn; unfold anchoredPair at hh; linear_combination hh
    · left; unfold anchoredPair; linear_combination he
  · constructor
    · intro hh; apply hn; unfold anchoredPair at hh; linear_combination hh
    · right; unfold anchoredPair; linear_combination he

/-- A deletion matching of a cycle, with the advertised fixed-point bound. -/
theorem cycle_deletion_pairing (t : ℕ) (A : Finset (ZMod (2*t+1))) (hA : A.Nonempty) :
    ∃ p : ZMod (2*t+1) → ZMod (2*t+1), Function.Involutive p ∧
      (∀ x ∈ Aᶜ, p x ∈ Aᶜ) ∧
      (∀ x ∈ Aᶜ, p x ≠ x → rimAdj (2*t+1) x (p x)) ∧
      (Aᶜ.filter (fun x => p x = x)).card ≤ A.card-1 := by
  classical
  obtain ⟨a,ha⟩ := hA
  let p := anchoredPair t a
  have hp := anchoredPair_involutive t a
  refine ⟨deletePair A p, deletePair_involutive A p hp, ?_, ?_, ?_⟩
  · intro x hx
    have hn := Finset.mem_compl.mp hx
    by_cases hh : p x ∈ A
    · simpa [deletePair, hn, hh] using hx
    · simpa [deletePair, hn, hh] using hh
  · intro x hx hne
    have hn := Finset.mem_compl.mp hx
    have hxa : x ≠ a := fun h => hn (h ▸ ha)
    by_cases hh : p x ∈ A
    · exact (hne (by simp [deletePair, hh])).elim
    · simpa [deletePair, hn, hh, p] using anchoredPair_edge t a x hxa
  · exact deletePair_fixed_bound A p hp a ha (anchoredPair_fixed t a)
end WheelFormal
