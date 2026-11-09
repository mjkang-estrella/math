import QuotientExtraction
import FullCofactor
import FiniteGrammar
namespace Nut8
open Matrix

theorem integer_full_kernel_det_adjugate (C : QuotientMatrix)
    (hs : C.IsSymm)
    (hd : Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (C.map (Int.castRingHom ℝ)))) = 1)
    (u : Fin 8 → ℝ) (hu : C.map (Int.castRingHom ℝ) *ᵥ u = 0) (hf : ∀ i, u i ≠ 0) :
    C.det = 0 ∧ ∀ i, C.adjugate i i ≠ 0 := by
  have hsr : (C.map (Int.castRingHom ℝ)).IsSymm := by
    ext i j
    exact congrArg (fun z : ℤ => (z : ℝ)) (congrFun (congrFun hs i) j)
  obtain ⟨hdet,hcof⟩ := full_kernel_det_adjugate (n := 7) _ hsr hd u hu hf
  have hmapdet := (Int.castRingHom ℝ).map_det C
  have hmapadj := (Int.castRingHom ℝ).map_adjugate C
  constructor
  · have hz : (C.det : ℝ) = 0 := hmapdet.trans hdet
    exact_mod_cast hz
  · intro i hz
    have h := congrFun (congrFun hmapadj i) i
    have : (C.map (Int.castRingHom ℝ)).adjugate i i = 0 := by
      apply h.symm.trans
      change (C.adjugate i i : ℝ) = 0
      rw [hz, Int.cast_zero]
    exact hcof i this

/-- The actual graph yields the algebraic obstruction signature; A3 is still separate. -/
theorem nut_circulant_matrix {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Nut G) (hc : Circulant 8 G) :
    ∃ (C : QuotientMatrix) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ C.IsSymm ∧
      C.det = 0 ∧ ∀ i, C.adjugate i i ≠ 0 := by
  obtain ⟨m, hm, L, ε, he, _, _, hs, hd, v, hf, hk⟩ := nut_circulant_quotient G hn hc
  exact ⟨_, ε, he.imp_right And.left, hs, integer_full_kernel_det_adjugate _ hs hd v hk hf⟩
end Nut8
