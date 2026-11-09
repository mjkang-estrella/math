import GraphCoordinates
namespace Nut8
open Matrix
variable {m : ℕ} [NeZero m]

/-- The graph-specific Fourier lift; evaluation at a representative is its left inverse. -/
def characterLift (ε : ℤ) : (Fin 8 → ℝ) →ₗ[ℝ] ((Fin 8 × ZMod m) → ℝ) where
  toFun v p := (character m ε p.2 : ℝ) * v p.1
  map_add' v w := by ext p; simp [mul_add]
  map_smul' c v := by ext p; simp [mul_left_comm]

omit [NeZero m] in
lemma characterLift_injective (ε : ℤ) : Function.Injective (characterLift (m := m) ε) := by
  intro v w h
  ext i
  have hi := congrFun h (i,0)
  simpa [characterLift, character_zero] using hi

lemma adjacency_characterLift (G : SimpleGraph (Fin 8 × ZMod m)) [DecidableRel G.Adj]
    (ht : TranslationInvariant G) (ε : ℤ) (hp : ε ^ m = 1) (v : Fin 8 → ℝ)
    (i : Fin 8) (a : ZMod m) :
    adjacency G (characterLift ε v) (i,a) =
      (character m ε a : ℝ) *
        ((signedQuotient m G ε).map (Int.castRingHom ℝ) *ᵥ v) i := by
  change (∑ p, G.adjMatrix ℝ (i,a) p * ((character m ε p.2 : ℝ) * v p.1)) = _
  rw [Fintype.sum_prod_type]
  change (∑ j, ∑ b, G.adjMatrix ℝ (i,a) (j,b) * ((character m ε b : ℝ) * v j)) =
    (character m ε a : ℝ) * (∑ j, ((∑ b, if G.Adj (i,0) (j,b) then character m ε b else 0 : ℤ) : ℝ) * v j)
  simp only [Int.cast_sum, Int.cast_ite, Int.cast_zero, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ∑ b : ZMod m, G.adjMatrix ℝ (i,a) (j,b+a) *
          ((character m ε (b+a) : ℝ) * v j) :=
      (Equiv.sum_comp (Equiv.addRight a) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      simp only [SimpleGraph.adjMatrix_apply, ht i j a (b+a), add_sub_cancel_right, character_add m ε hp,
        Int.cast_mul]
      split_ifs <;> simp [mul_left_comm, mul_assoc]

/-- Every quotient nullvector lifts to an actual adjacency nullvector. -/
def quotientKernelLift (G : SimpleGraph (Fin 8 × ZMod m)) [DecidableRel G.Adj]
    (ht : TranslationInvariant G) (ε : ℤ) (hp : ε ^ m = 1) :
    LinearMap.ker (Matrix.mulVecLin ((signedQuotient m G ε).map (Int.castRingHom ℝ))) →ₗ[ℝ]
      LinearMap.ker (adjacency G) :=
  (characterLift ε).restrict (by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    ext p
    rw [adjacency_characterLift G ht ε hp v p.1 p.2]
    change (character m ε p.2 : ℝ) * (Matrix.mulVecLin _ v) p.1 = 0
    rw [hv]
    simp)

lemma quotientKernelLift_injective (G : SimpleGraph (Fin 8 × ZMod m))
    [DecidableRel G.Adj] (ht : TranslationInvariant G) (ε : ℤ) (hp : ε ^ m = 1) :
    Function.Injective (quotientKernelLift G ht ε hp) := by
  intro v w h
  apply Subtype.ext
  exact characterLift_injective ε (congrArg Subtype.val h)
end Nut8
