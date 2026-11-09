import TotalBits
namespace XorMagic
variable {V : Type} [Fintype V] [DecidableEq V]

theorem no_closed_top_four {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph V)
    [DecidableRel G.Adj] (reg : G.IsRegularOfDegree (2^n-4))
    (magic : ClosedMagic G n) : False := by
  classical
  obtain ⟨_, l, hl⟩ := magic
  have hc := card_of_label l
  have power : 4 ≤ 2^n := by
    calc
      4 = 2^2 := by decide
      _ ≤ 2^n := Nat.pow_le_pow_right (by decide) hn
  have hr : Gᶜ.IsRegularOfDegree 3 := by
    have hh := reg.compl
    have degree : Fintype.card V-1-(2^n-4) = 3 := by omega
    simpa only [degree] using hh
  apply cubic_obstruction Gᶜ hr l
  intro v
  rw [complement_identity G l (total_labels hn l) v]
  exact hl v

theorem not_closed_top_four {n : ℕ} (hn : 2 ≤ n) : ¬ ClosedExists n (2^n-4) := by
  rintro ⟨V,f,e,G,dec,reg,magic⟩
  exact no_closed_top_four hn G reg magic
end XorMagic
