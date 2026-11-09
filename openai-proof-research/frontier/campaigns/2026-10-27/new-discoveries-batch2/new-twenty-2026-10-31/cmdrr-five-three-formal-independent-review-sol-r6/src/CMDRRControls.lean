import CMDRRNonexistence
namespace CMDRR.Controls

def noneMatching : Matching (Fin 2) (Fin 2) where
  spouse _ _ := False
  right_unique _ _ _ h := False.elim h
  left_unique _ _ _ h := False.elim h

def game (i : Fin 2) : Game (Fin 2) (Fin 2) where
  teams := if i = 0 then {(0,0),(1,1)} else {(0,1),(1,0)}
  two := by fin_cases i <;> decide
  men_distinct := by fin_cases i <;> decide
  women_distinct := by fin_cases i <;> decide

def schedule : Schedule (Fin 2) (Fin 2) (Fin 2) := ⟨game⟩

/-- Positive source control: the two-game strict MMDRR(2), allowing the
genuine single-pair repeated opposition on both sides. -/
theorem positive_source : Source noneMatching schedule := by
  simp only [Source,noneMatching,Matching.SingleMan,Matching.SingleWoman,
    Game.Partners,Game.Opposes,Game.Men,Game.Women,Game.Shares]
  simp only [count_as_sum]
  simp; decide

theorem unordered_team_swap :
    (game 0).teams = {(1,1),(0,0)} := by decide

theorem two_distinct_occurrences : schedule.game 0 ≠ schedule.game 1 := by
  intro he
  have hh := congrArg Game.teams he
  have hn : (schedule.game 0).teams ≠ (schedule.game 1).teams := by decide
  exact hn hh

theorem partner_count_one :
    count (fun i => (schedule.game i).Partners 0 0) = 1 := by
  simp only [Game.Partners,count_as_sum]
  decide

theorem repeat_count_two :
    count (fun i => (schedule.game i).Men 0 1) = 2 := by
  simp only [Game.Men,count_as_sum]
  decide

/-- Positive adversarial control: the two singles oppose twice, so replacing
the source multiplicity by one would reject this valid source object. -/
theorem repeat_is_not_one :
    count (fun i => (schedule.game i).Men 0 1) ≠ 1 := by
  rw [repeat_count_two]
  decide

theorem duplicate_partnership_detected :
    count (fun _ : Fin 2 => (game 0).Partners 0 0) = 2 := by
  simp only [Game.Partners,count_as_sum]
  decide

/-- A game with a forbidden spouse sharing the court is not source-admissible. -/
def oneMatching : Matching (Fin 2) (Fin 2) where
  spouse m w := m = 0 ∧ w = 0
  right_unique _ _ _ h k := h.2.trans k.2.symm
  left_unique _ _ _ h k := h.1.trans k.1.symm

theorem spouse_violation : ¬ Source oneMatching schedule := by
  intro h
  exact h.1 0 0 ⟨rfl,rfl⟩ 0 ((game 0).partner_shares (by change (0,0) ∈ (game 0).teams; decide))
end CMDRR.Controls
