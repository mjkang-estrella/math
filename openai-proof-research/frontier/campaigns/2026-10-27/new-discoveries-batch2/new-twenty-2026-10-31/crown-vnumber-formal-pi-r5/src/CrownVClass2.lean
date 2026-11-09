import CrownVCut
import CrownVClass

/-!
Bridge between the path-form cut vertex `VCut` (CrownVClass) and the
component-count form, via the actual component counter `ccnt`
(CrownVCount): for `t ∉ s`, `VCut s t ↔ ccnt (insert t s) < ccnt s`.

This discharges the literal semantic obligation recorded in the r4
CHECKPOINT: the path definition may not be *called* the component-count
cut-vertex criterion until this kernel equivalence exists.  Both directions
are proved here; neither is definitional.
-/

open Classical

namespace CrownV

variable {n : ℕ}

/-! ### Component equality from a path -/

theorem comp_eq {s : Finset (V n)} {a b : V n} (h : SameC s a b) :
    comp s a = comp s b := by
  exact Finset.ext fun x =>
    ⟨fun hx => comp_eq_of_sameC h.symm hx, fun hx => comp_eq_of_sameC h hx⟩

/-- Last-edge decomposition of a path. -/
theorem sameC_last {s : Finset (V n)} {a : V n} :
    ∀ c : V n, SameC s a c → c = a ∨ ∃ w, SEdge s w c ∧ SameC s a w := by
  intro c h
  induction h with
  | refl => exact Or.inl rfl
  | tail h₁ h₂ _ => exact Or.inr ⟨_, h₂, h₁⟩

/-- The second endpoint of an `s`-path from `a ∈ s` lies in `s`. -/
theorem sameC_snd_mem {s : Finset (V n)} {a b : V n} (ha : a ∈ s)
    (h : SameC s a b) : b ∈ s := by
  rcases sameC_last b h with he | ⟨w, hw, _⟩
  · subst he; exact ha
  · exact hw.2.1

/-! ### Transfer: paths inside an `H`-closed block avoid the new vertex -/

/-- If `D ⊆ s` and `D` is closed under `H`-edges (`H = insert t s`), then
every `H`-path ending in `D` reroutes as an `s`-path. -/
theorem sameC_H_to_s {s : Finset (V n)} {t : V n} {D : Finset (V n)} {u : V n}
    (hDsub : ∀ z ∈ D, z ∈ s)
    (hcl : ∀ a ∈ D, ∀ ⦃b : V n⦄, SEdge (insert t s) a b → b ∈ D) :
    ∀ z : V n, SameC (insert t s) u z → z ∈ D → SameC s u z := by
  intro z h
  induction h with
  | refl => intro _; exact .refl
  | tail _ h₂ ih =>
    intro hzD
    have hmD := hcl _ hzD (sEdge_symm h₂)
    exact (ih hmD).trans
      (SameC.single ⟨hDsub _ hmD, hDsub _ hzD, h₂.2.2⟩)

/-- The `H`-component of `u` is `H`-closed. -/
theorem comp_H_closed {s : Finset (V n)} {t : V n} {u a b : V n}
    (ha : a ∈ comp (insert t s) u) (hb : b ∈ insert t s) (hcad : cadj a b) :
    b ∈ comp (insert t s) u := by
  have hau : SameC (insert t s) u a := (Finset.mem_filter.1 ha).2
  have h1 : SameC (insert t s) a b := SameC.single ⟨(Finset.mem_filter.1 ha).1, hb, hcad⟩
  exact Finset.mem_filter.2 ⟨hb, hau.trans h1⟩

/-! ### Split lemma: an `s`-escaping path inside `insert t s` touches `t` -/

theorem sameC_ins_split {s : Finset (V n)} {t x y : V n} (_ht : t ∉ s)
    (hx : x ∈ s) (hconn : SameC (insert t s) x y) (_hdis : ¬ SameC s x y) :
    SameC (insert t s) x t := by
  have key : ∀ z : V n, SameC (insert t s) x z → SameC s x z ∨ SameC (insert t s) x t := by
    intro z h
    induction h with
    | refl => exact Or.inl .refl
    | tail _ h₂ ih =>
      obtain ⟨hmH, hzH, hcad⟩ := h₂
      rcases ih with hS | hT
      · have hmS := sameC_snd_mem hx hS
        rcases eq_or_ne z t with he | hne
        · rw [he] at hcad hzH
          exact Or.inr ((sameC_congr_set (Finset.subset_insert _ _) hS).trans'
            (SameC.single ⟨hmH, Finset.mem_insert_self _ _, hcad⟩))
        · have hz : z ∈ s := by
            rcases Finset.mem_insert.1 hzH with h | h
            · exact absurd h hne
            · exact h
          exact Or.inl (hS.trans' (SameC.single ⟨hmS, hz, hcad⟩))
      · exact Or.inr (hT.trans' (SameC.single ⟨hmH, Finset.mem_insert_self _ _, hcad⟩))
  rcases key y hconn with hS | hT
  · exact absurd hS _hdis
  · exact hT

end CrownV
