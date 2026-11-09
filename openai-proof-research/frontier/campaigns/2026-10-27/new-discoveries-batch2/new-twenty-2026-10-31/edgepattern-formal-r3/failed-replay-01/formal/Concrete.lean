import Definitions
namespace EdgePattern.Concrete
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev V := Fin 8

def edges : List (V × V) := [(0,1),(0,2),(0,3),(1,5),(1,7),(3,4),(4,6),(5,6)]

def adj (v w : V) : Prop := (v,w) ∈ edges ∨ (w,v) ∈ edges
instance : DecidableRel adj := fun v w => inferInstanceAs (Decidable ((v,w) ∈ edges ∨ (w,v) ∈ edges))

def graph : SimpleGraph V where
  Adj := adj
  symm := ⟨by intro v w h; exact h.symm⟩
  loopless := ⟨by intro v; fin_cases v <;> decide⟩

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel adj)

def pattern : Rooted V := ⟨graph,0,1,by decide⟩

def independent (s : Finset V) : Prop := ∀ e ∈ edges, ¬(e.1 ∈ s ∧ e.2 ∈ s)
instance (s : Finset V) : Decidable (independent s) := inferInstanceAs (Decidable (∀ e ∈ edges, ¬(e.1 ∈ s ∧ e.2 ∈ s)))

theorem independent_iff (s : Finset V) : independent s ↔ Independent graph s := by
  constructor
  · intro h v hv w hw hadj
    rcases hadj with h' | h'
    · exact h (v,w) h' ⟨hv,hw⟩
    · exact h (w,v) h' ⟨hw,hv⟩
  · intro h e he ⟨ha,hb⟩
    exact h e.1 ha e.2 hb (Or.inl he)

def candidates : Finset (Finset V) := Finset.univ.powerset

theorem card_bound : ∀ s ∈ candidates, independent s → s.card ≤ 4 := by decide

def listed : Finset (Finset V) :=
  {{1,2,3,6},{2,3,5,7},{0,4,5,7},{2,4,5,7},{2,3,6,7}}

theorem listed_exact : candidates.filter (fun s => independent s ∧ s.card = 4) = listed := by decide

theorem maximum_iff (s : Finset V) : Maximum graph s ↔ independent s ∧ s.card = 4 := by
  have hs : s ∈ candidates := Finset.mem_powerset.mpr (Finset.subset_univ s)
  constructor
  · intro h
    have hi := (independent_iff s).mpr h.1
    have hl : Independent graph ({1,2,3,6} : Finset V) := (independent_iff _).mp (by decide)
    have hh := h.2 _ hl
    have hc : ({1,2,3,6} : Finset V).card = 4 := by decide
    exact ⟨hi, Nat.le_antisymm (card_bound s hs hi) (hc ▸ hh)⟩
  · rintro ⟨hi,hc⟩
    refine ⟨(independent_iff s).mp hi, ?_⟩
    intro t ht
    rw [hc]
    exact card_bound t (Finset.mem_powerset.mpr (Finset.subset_univ t)) ((independent_iff t).mpr ht)

theorem maxima_eq : maxima graph = listed := by
  classical
  rw [maxima]
  change candidates.filter (Maximum graph) = listed
  simp_rw [maximum_iff]
  exact listed_exact

def layers : Fin 3 → Finset V := ![{0,1},{2,3,5,7},{4,6}]

def totals (i : Fin 3) : ℕ := ∑ s ∈ listed, (s ∩ layers i).card

theorem totals_values : totals 0 = 2 ∧ totals 1 = 14 ∧ totals 2 = 4 := by decide

theorem listed_count : listed.card = 5 := by decide

def occupancy (i : Fin 3) : ℚ := (totals i : ℚ) / listed.card

theorem occupancy_values : occupancy 0 = 2/5 ∧ occupancy 1 = 14/5 ∧ occupancy 2 = 4/5 := by
  simp only [occupancy, totals_values.1, totals_values.2.1, totals_values.2.2, listed_count]
  norm_num

def alpha : Fin 3 → ℚ := ![1/1000,7/27,1/3]

theorem alpha_positive : ∀ i, 0 < alpha i := by
  intro i; fin_cases i <;> norm_num [alpha]

theorem separating_value : (∑ i, alpha i * occupancy i) = 67027/67500 := by
  have h := occupancy_values
  simp only [Fin.sum_univ_succ]
  norm_num [alpha, h.1, h.2.1, h.2.2]

theorem separating_lt_one : (∑ i, alpha i * occupancy i) < 1 := by
  rw [separating_value]
  norm_num
end EdgePattern.Concrete
