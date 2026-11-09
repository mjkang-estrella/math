import ChordModel2Orbit
import Mathlib.Data.Finset.Sort
namespace Chord.Model2

/-- Transport a pairing to the increasing enumeration of a closed position set. -/
noncomputable def induced {n k} (D : Diagram n) (s : Finset (Fin (2*n)))
    (hc : s.card = 2*k) (hs : ∀ i ∈ s, D.partner i ∈ s) : Diagram k :=
  let e := s.orderIsoOfFin hc
  { partner := fun i => e.symm ⟨D.partner (e i).val, hs _ (e i).property⟩
    involutive := by
      intro i
      apply e.injective
      apply Subtype.ext
      simp only [OrderIso.apply_symm_apply]
      exact D.involutive _
    noFixed := by
      intro i h
      have he := congrArg (fun j => (e j).val) h
      simp only [OrderIso.apply_symm_apply] at he
      exact D.noFixed _ he }

noncomputable def inducedSubdiagram {n k} (D : Diagram n) (s : Finset (Fin (2*n)))
    (hc : s.card = 2*k) (hs : ∀ i ∈ s, D.partner i ∈ s) :
    Subdiagram (induced D s hc hs) D where
  positions i := (s.orderIsoOfFin hc i).val
  increasing := by
    intro i j h
    exact (s.orderIsoOfFin hc).strictMono h
  closed i := by
    change D.partner _ = ((s.orderIsoOfFin hc) ((s.orderIsoOfFin hc).symm _)).val
    simp only [OrderIso.apply_symm_apply]

/-- Restricting endpoint sides is surjective: each assignment extends. -/
theorem sides_extend {k n} {A : Diagram k} {D : Diagram n}
    (S : Subdiagram A D) (a : Sides k) : ∃ c, restrictSides S c = a := by
  classical
  let c : Sides n := fun j => if h : ∃ i, S.positions i = j then a h.choose else false
  refine ⟨c, ?_⟩
  funext i
  have h : ∃ x, S.positions x = S.positions i := ⟨i, rfl⟩
  simp only [restrictSides, Function.comp_apply, c, dite_eq_left h]
  exact congrArg a (S.increasing.injective h.choose_spec)

/-- A pairing on a subset factors through its increasing enumeration. -/
noncomputable def factorSubdiagram {k n m} {A : Diagram k} {D : Diagram n}
    (S : Subdiagram A D) (s : Finset (Fin (2*n))) (hc : s.card = 2*m)
    (hs : ∀ i ∈ s, D.partner i ∈ s) (hin : ∀ i, S.positions i ∈ s) :
    Subdiagram A (induced D s hc hs) where
  positions i := (s.orderIsoOfFin hc).symm ⟨S.positions i, hin i⟩
  increasing := by
    intro i j h
    exact (s.orderIsoOfFin hc).symm.strictMono (S.increasing h)
  closed i := by
    apply (s.orderIsoOfFin hc).injective
    apply Subtype.ext
    simp only [induced, OrderIso.apply_symm_apply]
    exact S.closed i

theorem subdiagram_size {k n} {A : Diagram k} {D : Diagram n}
    (S : Subdiagram A D) : k ≤ n := by
  have h := Fintype.card_le_of_injective S.positions S.increasing.injective
  simp only [Fintype.card_fin] at h
  omega

/-- Remove a chord outside the retained positions. -/
theorem factor_one {k n} {A : Diagram k} {D : Diagram (n+1)}
    (S : Subdiagram A D) (hkn : k < n+1) :
    ∃ B : Diagram n, Nonempty (Subdiagram A B) ∧ Nonempty (Subdiagram B D) ∧
      ∃ (T : Subdiagram A B) (U : Subdiagram B D),
        ∀ i, U.positions (T.positions i) = S.positions i := by
  classical
  have hnot : ¬Function.Surjective S.positions := by
    intro h
    have hh := Fintype.card_le_of_surjective _ h
    simp only [Fintype.card_fin] at hh
    omega
  obtain ⟨p, hp⟩ : ∃ p, ∀ i, S.positions i ≠ p := by
    simpa only [Function.Surjective, not_forall, not_exists] using hnot
  let q := D.partner p
  have hqp : q ≠ p := D.noFixed p
  have hq : ∀ i, S.positions i ≠ q := by
    intro i hi
    have hh := S.closed i
    rw [hi] at hh
    change D.partner (D.partner p) = _ at hh
    rw [D.involutive] at hh
    exact hp _ hh.symm
  let s := (Finset.univ.erase p).erase q
  have hc : s.card = 2*n := by
    have hp' : p ∈ (Finset.univ : Finset (Fin (2*(n+1)))) := Finset.mem_univ _
    have hq' : q ∈ (Finset.univ.erase p) := Finset.mem_erase.mpr ⟨hqp, Finset.mem_univ _⟩
    simp only [s, Finset.card_erase_of_mem hq', Finset.card_erase_of_mem hp',
      Finset.card_univ, Fintype.card_fin]
    omega
  have hs : ∀ i ∈ s, D.partner i ∈ s := by
    intro i hi
    have hi' : i ≠ q ∧ i ≠ p := by simpa [s] using hi
    simp only [s, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro h
      have hh := congrArg D.partner h
      rw [D.involutive, D.involutive] at hh
      exact hi'.2 hh
    · intro h
      have hh := congrArg D.partner h
      rw [D.involutive] at hh
      exact hi'.1 hh
  have hin : ∀ i, S.positions i ∈ s := by intro i; simp [s, hp i, hq i]
  let T := factorSubdiagram S s hc hs hin
  let U := inducedSubdiagram D s hc hs
  refine ⟨induced D s hc hs, ⟨T⟩, ⟨U⟩, T, U, ?_⟩
  intro i
  change ((s.orderIsoOfFin hc) ((s.orderIsoOfFin hc).symm _)).val = _
  simp only [OrderIso.apply_symm_apply]
end Chord.Model2
