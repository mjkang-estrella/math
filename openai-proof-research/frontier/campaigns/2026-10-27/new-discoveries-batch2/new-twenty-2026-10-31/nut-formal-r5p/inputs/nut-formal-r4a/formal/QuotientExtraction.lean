import KernelLift
namespace Nut8
open Matrix
variable {V : Type} [Fintype V] {m : ℕ} [NeZero m]

/-- Transporting kernel vectors back to original vertices loses no information. -/
def coordinateKernelEmbedding (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : Fin 8 × ZMod m ≃ V) :
    LinearMap.ker (adjacency (coordinateGraph G L)) →ₗ[ℝ] LinearMap.ker (adjacency G) where
  toFun v := ⟨v ∘ L.symm, by
    ext w
    have h := coordinateGraph_adjacency G L (v ∘ L.symm) (L.symm w)
    have hv := congrFun v.property (L.symm w)
    simp only [Function.comp_def, L.symm_apply_apply, L.apply_symm_apply] at h
    exact h.symm.trans hv⟩
  map_add' v w := by rfl
  map_smul' c v := by rfl

lemma coordinateKernelEmbedding_injective (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : Fin 8 × ZMod m ≃ V) : Function.Injective (coordinateKernelEmbedding G L) := by
  intro v w h
  apply Subtype.ext
  ext p
  have hp := congrFun (congrArg Subtype.val h) (L p)
  simpa [coordinateKernelEmbedding] using hp

/-- A2 directly from the original graph: no coordinate or lift hypotheses remain. -/
theorem nut_circulant_quotient [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Nut G) (hc : Circulant 8 G) :
    ∃ (m : ℕ) (_ : NeZero m) (L : Fin 8 × ZMod m ≃ V) (ε : ℤ),
      (ε = 1 ∨ ε = -1 ∧ Even m) ∧ ε ^ m = 1 ∧
      TranslationInvariant (coordinateGraph G L) ∧
      (signedQuotient m (coordinateGraph G L) ε).IsSymm ∧
      Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin
        ((signedQuotient m (coordinateGraph G L) ε).map (Int.castRingHom ℝ)))) = 1 ∧
      ∃ v : Fin 8 → ℝ, (∀ i, v i ≠ 0) ∧
        (signedQuotient m (coordinateGraph G L) ε).map (Int.castRingHom ℝ) *ᵥ v = 0 := by
  have hV : 0 < Fintype.card V := lt_of_lt_of_le (by decide : 0 < 2) hn.1
  let : Nonempty V := Fintype.card_pos_iff.mp hV
  obtain ⟨σ, hq, m, hm⟩ := hc
  let : NeZero m := ⟨Nat.ne_of_gt (orbit_size_pos σ.toEquiv m hm)⟩
  let L := globalLabel8 σ.toEquiv m hm hq
  have hL := globalLabel8_translate σ.toEquiv m hm hq
  have ht := coordinateGraph_translation G σ L hL
  obtain ⟨u, ε, hu, hf, he, hp, hchar⟩ := nut_coordinate_character G hn σ
    (pow_eq_one_of_equal_orbits σ.toEquiv m hm) L hL
  have hk : adjacency (coordinateGraph G L) (u ∘ L) = 0 := by
    ext p
    rw [coordinateGraph_adjacency, hu]
    rfl
  have hqk := signedQuotient_kernel (coordinateGraph G L) ε (u ∘ L) hk hchar
  let C := (signedQuotient m (coordinateGraph G L) ε).map (Int.castRingHom ℝ)
  let K := LinearMap.ker (Matrix.mulVecLin C)
  let f := (coordinateKernelEmbedding G L).comp
    (quotientKernelLift (coordinateGraph G L) ht ε hp)
  have hfi : Function.Injective f :=
    (coordinateKernelEmbedding_injective G L).comp
      (quotientKernelLift_injective (coordinateGraph G L) ht ε hp)
  have hle : Module.finrank ℝ K ≤ 1 := by
    have h := LinearMap.finrank_le_finrank_of_injective hfi
    simpa only [hn.2.1] using h
  have hpos : 0 < Module.finrank ℝ K := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨fun i => u (L (i,0)), hqk⟩, ?_⟩
    intro hz
    exact hf (L (0,0)) (congrFun (congrArg Subtype.val hz) 0)
  refine ⟨m, inferInstance, L, ε, he, hp, ht,
    signedQuotient_symmetric (coordinateGraph G L) ht ε hp (he.imp_right And.left),
    Nat.le_antisymm hle hpos, fun i => u (L (i,0)), fun i => hf _, hqk⟩
end Nut8
