import CMDRRFiveOrbit
open scoped Classical
namespace CMDRR
theorem Matching.eq_of_spouse {M W : Type} (s t : Matching M W)
    (he : s.spouse = t.spouse) : s = t := by
  cases s
  cases t
  cases he
  rfl

theorem canonical_swap_eq : canonical.swap = canonical := by
  apply Matching.eq_of_spouse
  funext m w
  apply propext
  change (w = m ∧ w.val < 3) ↔ (m = w ∧ m.val < 3)
  constructor <;> rintro ⟨rfl,h⟩ <;> exact ⟨rfl,h⟩

noncomputable def canonicalTranspose : Cell canonical ≃ Cell canonical where
  toFun x := ⟨x.1.swap,by
    intro hs
    apply x.2
    change x.1.1 = x.1.2 ∧ x.1.1.val < 3
    change x.1.2 = x.1.1 ∧ x.1.2.val < 3 at hs
    rcases hs with ⟨he,hm⟩
    exact ⟨he.symm,he ▸ hm⟩⟩
  invFun x := ⟨x.1.swap,by
    intro hs
    apply x.2
    change x.1.1 = x.1.2 ∧ x.1.1.val < 3
    change x.1.2 = x.1.1 ∧ x.1.2.val < 3 at hs
    rcases hs with ⟨he,hm⟩
    exact ⟨he.symm,he ▸ hm⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

namespace Game
variable {M W : Type}
theorem other_swap (g : Game M W) (a : {p // p ∈ g.teams}) :
    (g.swap.other ⟨a.1.swap,by
      change (a.1.2,a.1.1) ∈ g.swap.teams
      exact (g.swap_partners a.1.1 a.1.2).mpr a.2⟩).1 =
      (g.other a).1.swap := by
  apply (Equiv.prodComm W M).injective
  have ho := (g.swap).opposite_unique (show a.1.swap ∈ g.swap.teams from
    (g.swap_partners a.1.1 a.1.2).mpr a.2)
  have hb : (g.other a).1.swap ∈ g.swap.teams :=
    (g.swap_partners _ _).mpr (g.other a).2
  have hn : (g.other a).1.swap ≠ a.1.swap :=
    fun he => g.other_ne a (Subtype.ext ((Equiv.prodComm M W).injective he))
  have he := ho.choose_spec.2 _ ⟨hb,hn⟩
  change (g.other a).1.swap =
    (g.swap.other ⟨a.1.swap,(g.swap_partners _ _).mpr a.2⟩).1 at he
  exact congrArg Prod.swap he.symm
end Game

namespace Source
variable {O : Type} [Fintype O] {d : Schedule (Fin 5) (Fin 5) O}
variable (h : Source canonical d)
include h in
theorem canonical_swap_source : Source canonical d.swap := by
  have hs := h.swap
  rw [canonical_swap_eq] at hs
  exact hs

/-- Explicit sex-swap correspondence: a swapped partner-to-opponent row
is precisely the original partner-to-opponent column after transposition. -/
theorem swapped_U_is_C (x : Cell canonical) :
    h.canonical_swap_source.U (canonicalTranspose x) =
      canonicalTranspose (h.C x) := by
  obtain ⟨a,rfl⟩ := h.cellsEquiv.surjective x
  let b : Incidence d.swap := ⟨a.1,⟨a.2.1.swap,
    ((d.game a.1).swap_partners _ _).mpr a.2.2⟩⟩
  have he : h.canonical_swap_source.cellsEquiv b =
      canonicalTranspose (h.cellsEquiv a) := rfl
  rw [← he,h.canonical_swap_source.U_incidence]
  apply Subtype.ext
  have hc := h.C_incidence a
  change (b.2.1.1,((d.swap.game b.1).other b.2).1.2) = (h.C (h.cellsEquiv a)).1.swap
  rw [hc]
  have hh := (d.game a.1).other_swap a.2
  change ((d.swap.game b.1).other b.2).1 = ((d.game a.1).other a.2).1.swap at hh
  rw [hh]
  rfl

/-- Original column action, expressed on its actual allowed male domain.
The full swapped-source incidence and elimination apply to this same map. -/
noncomputable def columnPerm (w : Fin 5) :
    Equiv.Perm (Row (s := canonical) w) := h.canonical_swap_source.rowPerm w

theorem column_cell_correspondence (w : Fin 5) (m : Row (s := canonical) w) :
    canonicalTranspose (rowCell w (h.columnPerm w m)) =
      h.C (canonicalTranspose (rowCell w m)) := by
  have he := h.canonical_swap_source.rowCell_perm w m
  have hc := h.swapped_U_is_C (canonicalTranspose (rowCell w m))
  have hi : canonicalTranspose (canonicalTranspose (rowCell w m)) = rowCell w m := by
    apply Subtype.ext; rfl
  rw [hi] at hc
  rw [hc] at he
  have ht := congrArg canonicalTranspose he
  have hinv : ∀ c : Cell canonical, canonicalTranspose (canonicalTranspose c) = c := by
    intro c
    apply Subtype.ext
    rfl
  rw [hinv] at ht
  exact ht
end Source
end CMDRR
