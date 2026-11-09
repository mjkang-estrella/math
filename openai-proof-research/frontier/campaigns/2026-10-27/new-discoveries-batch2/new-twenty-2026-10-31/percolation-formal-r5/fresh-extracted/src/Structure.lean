import Plane5
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

def erase {q : Nat} (a : Infection q) (v : Points q) : Infection q :=
  fun p => a p && decide (p ≠ v)

theorem percolates_mono {q : Nat} (P : Plane q) (r : Nat) {a b : Infection q}
    (hab : Subset a b) (ha : Percolates P r a) : Percolates P r b := by
  obtain ⟨n, hn⟩ := ha
  exact ⟨n, fun p => rounds_mono P r hab n p (hn p)⟩

theorem rounds_step {q : Nat} (P : Plane q) (r : Nat) (a : Infection q) (n : Nat) :
    rounds P r (step P r a) n = rounds P r a (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step P r (rounds P r (step P r a) n) = step P r (rounds P r a (n+1))
    rw [ih]

theorem percolates_of_step {q : Nat} (P : Plane q) (r : Nat) (a : Infection q)
    (h : Percolates P r (step P r a)) : Percolates P r a := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n+1, by rw [← rounds_step]; exact hn⟩

theorem minimal_no_redundant {q : Nat} (P : Plane q) (r : Nat) (a : Infection q)
    (hm : Minimal P r a) (v : Points q) (hv : a v = true) :
    ¬ Subset a (step P r (erase a v)) := by
  intro h
  apply hm.2 (erase a v) (fun p hp => by simp only [erase, Bool.and_eq_true] at hp; exact hp.1)
  · intro he
    have hp := congrFun he v
    simp [erase, hv] at hp
  · exact percolates_of_step P r _ (percolates_mono P r h hm.1)

theorem line_deletion_count : ∀ l v : Points 5, incidence v l = true →
    5 ≤ countOn PG5 (erase (fun p => incidence p l) v) l := by decide

-- Every initially infected line of a minimal set has at most five initial points.
theorem no_full_initial_line (a : Infection 5) (hm : Minimal PG5 5 a)
    (l v : Points 5) (hv : incidence v l = true)
    (ha : ∀ p, incidence p l = true → a p = true) : False := by
  apply minimal_no_redundant PG5 5 a hm v (ha v hv)
  intro p hp
  by_cases he : p = v
  · subst p
    simp only [step, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    right
    refine ⟨l, by simp, hv, ?_⟩
    apply Nat.le_trans (line_deletion_count l v hv)
    apply card_mono
    intro x hx
    simp only [erase, Bool.and_eq_true, decide_eq_true_eq] at *
    exact ⟨⟨ha x hx.1.1, hx.1.2⟩, hx.2⟩
  · simp only [step, Bool.or_eq_true]
    left
    simp [erase, hp, he]
end Percolation
