import Literal
namespace XorMagic

def binaryLabel (n : ℕ) (v : Fin (2^n)) : Bits n :=
  fun i => if v.val.testBit i.val then 1 else 0

theorem connected_of_descent {N : ℕ} (G : SimpleGraph (Fin N))
    (root : Fin N) (parent : Fin N → Fin N) (rank : Fin N → ℕ)
    (h : ∀ v, v ≠ root → G.Adj v (parent v) ∧ rank (parent v) < rank v) :
    G.Connected := by
  have hr : ∀ k v, rank v = k → G.Reachable root v := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hv
      by_cases he : v = root
      · subst v; exact SimpleGraph.Reachable.refl root
      · obtain ⟨ha, hl⟩ := h v he
        exact (ih (rank (parent v)) (by omega) (parent v) rfl).trans ha.symm.reachable
  exact G.connected_iff_exists_forall_reachable.mpr ⟨root, fun v => hr (rank v) v rfl⟩

def maskGraph {N : ℕ} (mask : Fin N → ℕ)
    (sym : ∀ u v, (mask u).testBit v.val = (mask v).testBit u.val)
    (loop : ∀ u, (mask u).testBit u.val = false) : SimpleGraph (Fin N) where
  Adj u v := (mask u).testBit v.val = true
  symm := ⟨by intro u v h; rw [sym v u]; exact h⟩
  loopless := ⟨by intro u h; simp [loop u] at h⟩

instance maskGraphDecidable {N : ℕ} (mask : Fin N → ℕ) (sym) (loop) :
    DecidableRel (maskGraph mask sym loop).Adj := fun _ _ => inferInstanceAs (Decidable (_ = true))

end XorMagic
