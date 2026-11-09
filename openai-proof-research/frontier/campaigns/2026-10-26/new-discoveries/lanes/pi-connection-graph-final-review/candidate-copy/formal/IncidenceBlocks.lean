import GraphMatrices

open Finset Matrix

namespace ConnectionGraph
noncomputable section
variable {V : Type*} [Fintype V] [LinearOrder V]

omit [Fintype V] in
theorem pair_inter_nonempty (a b c d : V) :
    ({a, b} ∩ {c, d} : Finset V).Nonempty ↔
      a = c ∨ a = d ∨ b = c ∨ b = d := by
  simp only [Finset.Nonempty, mem_inter, mem_insert, mem_singleton]
  aesop

theorem unsigned_gram_entry (E : Finset (V × V)) (e f : E) :
    ((unsignedIncidence E)ᵀ * unsignedIncidence E) e f =
      (if e.val.1 = f.val.1 then 1 else 0) +
      (if e.val.1 = f.val.2 then 1 else 0) +
      (if e.val.2 = f.val.1 then 1 else 0) +
      (if e.val.2 = f.val.2 then 1 else 0) := by
  simp [Matrix.mul_apply, unsignedIncidence, mul_add, sum_add_distrib, eq_comm]
  ring

theorem connection_eq_blocks {E : Finset (V × V)} (hE : ValidEdges E) :
    connectionMatrix E = blockConnection E := by
  ext (a | e) (b | f)
  · by_cases h : a = b <;> simp [connectionMatrix, blockConnection, simplex, h]
  · have hn := edge_ne hE f
    by_cases h1 : a = f.val.1 <;> by_cases h2 : a = f.val.2 <;>
      simp_all [connectionMatrix, blockConnection, simplex, unsignedIncidence,
        Finset.Nonempty]
  · have hn := edge_ne hE e
    change (if ({e.val.1, e.val.2} ∩ {b} : Finset V).Nonempty then 1 else 0) =
      unsignedIncidence E b e
    rw [inter_comm]
    by_cases h1 : b = e.val.1 <;> by_cases h2 : b = e.val.2 <;>
      simp_all [unsignedIncidence, Finset.Nonempty]
  · have he := hE e.val e.property
    have hf := hE f.val f.property
    have heq : e = f ↔ e.val.1 = f.val.1 ∧ e.val.2 = f.val.2 := by
      constructor
      · intro h
        cases h
        exact ⟨rfl, rfl⟩
      · rintro ⟨h1, h2⟩
        exact Subtype.ext (Prod.ext h1 h2)
    have hcross : ¬ (e.val.1 = f.val.2 ∧ e.val.2 = f.val.1) := by
      rintro ⟨h1, h2⟩
      rw [h1, h2] at he
      exact lt_asymm he hf
    simp only [connectionMatrix, simplex, pair_inter_nonempty, blockConnection,
      fromBlocks_apply₂₂, Matrix.sub_apply, unsigned_gram_entry, Matrix.one_apply]
    by_cases h1 : e.val.1 = f.val.1 <;>
      by_cases h2 : e.val.1 = f.val.2 <;>
      by_cases h3 : e.val.2 = f.val.1 <;>
      by_cases h4 : e.val.2 = f.val.2 <;>
      simp_all

end
end ConnectionGraph
