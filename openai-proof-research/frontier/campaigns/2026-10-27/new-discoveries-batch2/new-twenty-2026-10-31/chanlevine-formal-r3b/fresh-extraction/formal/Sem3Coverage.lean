import SemFinal
namespace ChanLevine.Sem3
variable {n : ℕ}

/-- Potential at an unfired vertex, including its predecessor rotor. -/
def edgePotential (c : SignedConfig n) (v : ZMod n) : ℤ :=
  2 * c.x (v+1) + if c.q v then 0 else 1

theorem edgePotential_fire (c : SignedConfig n) (v a : ZMod n)
    (ha : a ≠ v+1) :
    edgePotential c v + (if a = v then 1 else 0) ≤ edgePotential (fire c a) v := by
  by_cases hav : a = v
  · subst a
    have hne : v+1 ≠ v := Ne.symm ha
    cases hq : c.q v <;>
      simp [edgePotential, fire, target, hq, hne] <;> (try split_ifs) <;> omega
  · have hne : v+1 ≠ a := Ne.symm ha
    simp only [edgePotential, fire, hne, ite_false, sub_zero,
      Function.update_of_ne (Ne.symm hav), hav]
    split_ifs <;> omega

theorem LegalWord.potential {c d : SignedConfig n} {w : List (ZMod n)}
    (h : LegalWord c w d) (v : ZMod n) (hv : v+1 ∉ w) :
    edgePotential c v + (w.count v : ℤ) ≤ edgePotential d v := by
  induction h with
  | nil => simp
  | @cons c d w a ha hw ih =>
    have hnot : a ≠ v+1 := by intro he; apply hv; simp [he]
    have htail : v+1 ∉ w := by intro he; apply hv; simp [he]
    have hs := edgePotential_fire c v a hnot
    have ht := ih htail
    by_cases he : a = v
    · subst a; simp only [List.count_cons_self, Nat.cast_add, Nat.cast_one, ite_true] at *; omega
    · simp only [List.count_cons_of_ne he, he, ite_false] at *; omega

theorem closed_successor {c : SignedConfig n} {w : List (ZMod n)}
    (h : LegalWord c w c) {v : ZMod n} (hv : v ∈ w) : v+1 ∈ w := by
  by_contra hn
  have hp := LegalWord.potential h v hn
  have hc : 0 < w.count v := List.count_pos_iff.mpr hv
  have : (0 : ℤ) < w.count v := by exact_mod_cast hc
  omega

theorem closedCoverage : ClosedCoverage := by
  intro n inst hn c w hw h k
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil w hw
  have hall : ∀ t : ℕ, v + (t : ZMod n) ∈ w := by
    intro t
    induction t with
    | zero => simpa using hv
    | succ t ih => simpa [Nat.cast_add, add_assoc] using closed_successor h ih
  have hh := hall (k-v).val
  simpa using hh

 theorem ambientBridge : AmbientBridge := ambientBridge_of_coverage closedCoverage
end ChanLevine.Sem3
