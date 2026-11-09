import CMDRRRowDomain
import Mathlib.Logic.Equiv.Fin.Basic

namespace CMDRR
/-- Canonical three spouses, with singles 3 and 4 (zero-based labels). -/
def canonical : Matching (Fin 5) (Fin 5) where
  spouse m w := m = w ∧ m.val < 3
  right_unique _ _ _ h k := h.1.symm.trans k.1
  left_unique _ _ _ h k := h.1.trans k.1.symm

@[simp] theorem canonical_singleWoman (w : Fin 5) :
    canonical.SingleWoman w ↔ 3 ≤ w.val := by
  change (¬ ∃ m : Fin 5, m = w ∧ m.val < 3) ↔ _
  simp only [exists_eq_left]
  omega
@[simp] theorem canonical_singleMan (m : Fin 5) :
    canonical.SingleMan m ↔ 3 ≤ m.val := by
  change (¬ ∃ w : Fin 5, m = w ∧ m.val < 3) ↔ _
  constructor
  · intro h
    by_contra hn
    exact h ⟨m,rfl,by omega⟩
  · rintro hm ⟨w,_,hlt⟩
    omega

theorem canonical_singleWomen (w : Fin 5) (hw : canonical.SingleWoman w) :
    w = 3 ∨ w = 4 := by
  rw [canonical_singleWoman] at hw
  have hlt := w.isLt
  have he : w.val = 3 ∨ w.val = 4 := by omega
  rcases he with he | he
  · exact Or.inl (Fin.ext he)
  · exact Or.inr (Fin.ext he)

theorem canonical_singleMen (m : Fin 5) (hm : canonical.SingleMan m) :
    m = 3 ∨ m = 4 := canonical_singleWomen m ((canonical_singleMan m).mp hm |>
      (canonical_singleWoman m).mpr)

/-- Synchronized spouse labels give a genuine Fin5 relabeling. -/
theorem Matching.canonical_labels {M W : Type} [Fintype M] [Fintype W]
    (s : Matching M W) (hm : Fintype.card M = 5) (hw : Fintype.card W = 5)
    (hs : count (fun p : M × W => s.spouse p.1 p.2) = 3) :
    ∃ (e : M ≃ Fin 5) (f : W ≃ Fin 5),
      ∀ m w, s.spouse m w ↔ canonical.spouse (e m) (f w) := by
  obtain ⟨e,f,h⟩ := s.normalized_labels hm hw hs
  let g : (Fin 3 ⊕ Fin 2) ≃ Fin 5 := finSumFinEquiv
  refine ⟨e.trans g,f.trans g,?_⟩
  intro m w
  rw [h]
  change (∃ i : Fin 3, e m = Sum.inl i ∧ f w = Sum.inl i) ↔
    g (e m) = g (f w) ∧ (g (e m)).val < 3
  generalize e m = a
  generalize f w = b
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      simp only [Sum.inl.injEq]
      constructor
      · rintro ⟨i,rfl,rfl⟩
        exact ⟨rfl,by simp [g,finSumFinEquiv]⟩
      · rintro ⟨he,_⟩
        exact ⟨a,rfl,(Sum.inl.inj (g.injective he)).symm⟩
    | inr b =>
      have ha := a.isLt
      simp [g,finSumFinEquiv,Fin.ext_iff]
      omega
  | inr a =>
    cases b <;> simp [g,finSumFinEquiv]
end CMDRR
