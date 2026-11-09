import Character
namespace Nut8
open Matrix
variable {m : ℕ} [NeZero m]
variable (G : SimpleGraph (Fin 8 × ZMod m)) [DecidableRel G.Adj]

/-- Adjacency in coordinates is invariant under simultaneous cyclic translation. -/
def TranslationInvariant : Prop := ∀ i j a b,
  G.Adj (i,a) (j,b) ↔ G.Adj (i,0) (j,b-a)

lemma signedQuotient_symmetric (ht : TranslationInvariant G) (ε : ℤ)
    (hp : ε ^ m = 1) (hε : ε = 1 ∨ ε = -1) :
    (signedQuotient m G ε).IsSymm := by
  apply Matrix.ext
  intro i j
  unfold signedQuotient
  calc
    _ = ∑ b : ZMod m, if G.Adj (i,0) (j,-b) then character m ε (-b) else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      have ha : G.Adj (j,0) (i,b) ↔ G.Adj (i,0) (j,-b) := by
        rw [G.adj_comm, ht i j b 0, zero_sub]
      simp only [ha, character_neg m ε hp hε]
    _ = _ := Equiv.sum_comp (Equiv.neg (ZMod m))
      (fun b => if G.Adj (i,0) (j,b) then character m ε b else 0)

/-- The restriction to orbit representatives solves the signed quotient equation.
This lemma asks for the coordinate character formula, not for any quotient kernel claim. -/
lemma signedQuotient_kernel (ε : ℤ) (u : (Fin 8 × ZMod m) → ℝ)
    (hu : adjacency G u = 0)
    (hchar : ∀ i b, u (i,b) = (character m ε b : ℝ) * u (i,0)) :
    (signedQuotient m G ε).map (Int.castRingHom ℝ) *ᵥ (fun i => u (i,0)) = 0 := by
  funext i
  have hi := congrFun hu (i,0)
  change (∑ j, ((∑ b : ZMod m, if G.Adj (i,0) (j,b) then character m ε b else 0 : ℤ) : ℝ) * u (j,0)) = 0
  change (∑ p, G.adjMatrix ℝ (i,0) p * u p) = 0 at hi
  rw [Fintype.sum_prod_type] at hi
  simp only [Int.cast_sum, Int.cast_ite, Int.cast_zero, Finset.sum_mul]
  convert hi using 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  rw [SimpleGraph.adjMatrix_apply, hchar j b]
  split_ifs <;> simp
end Nut8
