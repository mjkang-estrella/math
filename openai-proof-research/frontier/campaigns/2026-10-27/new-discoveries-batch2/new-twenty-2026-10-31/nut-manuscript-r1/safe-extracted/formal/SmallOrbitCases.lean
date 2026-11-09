import EndpointOfFinite
namespace Nut8

/-- With one vertex in an orbit there is no internal edge at all. -/
theorem diagonal_m_one (G : SimpleGraph (Fin 8 × ZMod 1))
    [DecidableRel G.Adj] (ε : ℤ) (i : Fin 8) : signedQuotient 1 G ε i i = 0 := by
  unfold signedQuotient
  apply Finset.sum_eq_zero
  intro b _
  have hb : b = 0 := Subsingleton.elim _ _
  simp [hb]

/-- With two vertices in an orbit the only internal edge is the semi-edge,
whose shared character is ε^(2/2) = ε. No loop pair is possible. -/
theorem diagonal_m_two (G : SimpleGraph (Fin 8 × ZMod 2))
    [DecidableRel G.Adj] (ε : ℤ) (i : Fin 8) :
    signedQuotient 2 G ε i i = if G.Adj (i,0) (i,1) then ε else 0 := by
  have hvone : (1 : ZMod 2).val = 1 := by decide
  unfold signedQuotient
  rw [Finset.sum_eq_single (1 : ZMod 2)]
  · simp [character, hvone]
  · intro b _ hb
    have hz : b = 0 := by
      have hv := b.val_lt
      have hone : b.val ≠ 1 := by
        intro he
        apply hb
        apply ZMod.val_injective 2
        simpa only [hvone] using he
      have hbval : b.val = 0 := by omega
      apply ZMod.val_injective 2
      simpa only [ZMod.val_zero] using hbval
    simp [hz]
  · simp

example : (2 : ℕ) / 2 = 1 := by decide
example : (1 : ℕ) / 2 = 0 := by decide
end Nut8
