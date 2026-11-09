import Literal
import Mathlib.GroupTheory.Index
namespace XorMagic

/-- The cardinality step needs neither injectivity of D nor surjectivity of B. -/
theorem translation_exists {A E : Type} [AddCommGroup A] [AddCommGroup E]
    [Fintype A] [Fintype E] (D : A →+ E) (B : E →+ A)
    (large : Fintype.card A * Fintype.card A ≤ Fintype.card E)
    (nonzero : ∃ a, B (D a) ≠ 0) :
    ∃ c : E, B c = 0 ∧ c ∉ D.range := by
  classical
  by_contra h
  have contained : ∀ c : B.ker, (c : E) ∈ D.range := by
    intro c
    by_contra hc
    exact h ⟨c, c.property, hc⟩
  let f : B.ker → D.range := fun c => ⟨c, contained c⟩
  have inj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : D.range => (z : E)) hxy)
  obtain ⟨a, ha⟩ := nonzero
  have missing : (⟨D a, ⟨a, rfl⟩⟩ : D.range) ∉ Set.range f := by
    rintro ⟨c, hc⟩
    have eq : (c : E) = D a := congrArg Subtype.val hc
    exact ha (eq ▸ c.property)
  have strict := Fintype.card_lt_of_injective_of_notMem f inj missing
  have rangeD : Fintype.card D.range ≤ Fintype.card A :=
    Fintype.card_le_of_surjective D.rangeRestrict D.rangeRestrict_surjective
  have rangeB : Fintype.card B.range ≤ Fintype.card A :=
    Fintype.card_le_of_injective Subtype.val Subtype.coe_injective
  have product : Fintype.card B.ker * Fintype.card B.range = Fintype.card E := by
    have hc := B.ker.card_mul_index
    rw [AddSubgroup.index_ker] at hc
    simpa only [Nat.card_eq_fintype_card] using hc
  have pos : 0 < Fintype.card A := Fintype.card_pos
  nlinarith
end XorMagic
