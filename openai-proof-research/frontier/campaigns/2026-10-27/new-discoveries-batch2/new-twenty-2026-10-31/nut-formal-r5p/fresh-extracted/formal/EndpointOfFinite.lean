import AdmissibleDiagonal
namespace Nut8
open Matrix
variable {m : ℕ} [NeZero m]

/-- All grammar fields refer to the same signed quotient, without normalizing or
replacing its entries. -/
theorem coordinate_signedQuotient_admissible {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Nut G) (hcu : Cubic G)
    (L : Fin 8 × ZMod m ≃ V) (ht : TranslationInvariant (coordinateGraph G L))
    (ε : ℤ) (he : ε = 1 ∨ ε = -1) (hp : ε ^ m = 1)
    (u : (Fin 8 × ZMod m) → ℝ) (hu : adjacency (coordinateGraph G L) u = 0)
    (hf : ∀ v, u v ≠ 0)
    (hchar : ∀ i b, u (i,b) = (character m ε b : ℝ) * u (i,0)) :
    Admissible (signedQuotient m (coordinateGraph G L) ε) ε (ε ^ (m/2)) := by
  have hc := coordinateGraph_cubic G L hcu
  have hs := signedQuotient_symmetric (coordinateGraph G L) ht ε hp he
  have hsym : ∀ i j, signedQuotient m (coordinateGraph G L) ε i j =
      signedQuotient m (coordinateGraph G L) ε j i := fun i j => by
    exact (congrFun (congrFun hs i) j).symm
  have hr := signedQuotient_abs_row (coordinateGraph G L) hc ε he u hu hf hchar
  have hconn := signedQuotient_supportConnected G hn L ht ε he hc u hu hf hchar
  have hb := connected_cubic_entry_bound _ hsym hr hconn
  refine ⟨he, ?_, hsym, hr, hb,
    signedQuotient_diagonal (coordinateGraph G L) ht hc ε he u hu hf hchar hb, ?_, hconn⟩
  · rcases he with rfl | rfl
    · simp
    · exact neg_one_pow_eq_or ℤ (m/2)
  · intro h; subst ε
    exact signedQuotient_nonneg _

/-- The assumed finite obstruction closes the graph statement with no residual
hypotheses or abstract bridge assumptions. -/
theorem endpoint_of_finite (h : Nut8.FiniteObstruction) : Nut8.Target := by
  intro V _ _ G _ ⟨hcu, hn, hcir⟩
  obtain ⟨m, hm, L, ε, he, hp, ht, hs, hd, v, hf, hk⟩ := nut_circulant_quotient G hn hcir
  let : NeZero m := hm
  let u := characterLift (m := m) ε v
  have hu : adjacency (coordinateGraph G L) u = 0 := by
    ext p
    rw [adjacency_characterLift _ ht ε hp v p.1 p.2, hk]
    simp
  have hfull : ∀ p, u p ≠ 0 := by
    intro p
    change (character m ε p.2 : ℝ) * v p.1 ≠ 0
    apply mul_ne_zero _ (hf p.1)
    rcases character_sign m ε (he.imp_right And.left) p.2 with hh | hh <;> simp [hh]
  have hchar : ∀ i b, u (i,b) = (character m ε b : ℝ) * u (i,0) := by
    intro i b
    simp [u, characterLift, character_zero]
  have ha := coordinate_signedQuotient_admissible G hn hcu L ht ε
    (he.imp_right And.left) hp u hu hfull hchar
  exact h _ _ _ ha (integer_full_kernel_det_adjugate _ hs hd v hk hf)
end Nut8
