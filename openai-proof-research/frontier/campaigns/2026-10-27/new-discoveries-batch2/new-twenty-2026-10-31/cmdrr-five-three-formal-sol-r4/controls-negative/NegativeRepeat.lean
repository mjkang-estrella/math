import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-! Literal occurrence model of Berman–Wakeling Definition 1.2.
Games are sets of two mixed teams. There is no order, round assignment,
or injectivity requirement on the schedule's occurrence map. -/
namespace NegativeRepeat

structure Game (M W : Type) where
  teams : Finset (M × W)
  two : teams.card = 2
  men_distinct : ∀ a ∈ teams, ∀ b ∈ teams, a ≠ b → a.1 ≠ b.1
  women_distinct : ∀ a ∈ teams, ∀ b ∈ teams, a ≠ b → a.2 ≠ b.2

namespace Game
variable {M W : Type}
def Partners (g : Game M W) (m : M) (w : W) : Prop := (m,w) ∈ g.teams
def Men (g : Game M W) (m n : M) : Prop :=
  ∃ a ∈ g.teams, ∃ b ∈ g.teams, a.1 = m ∧ b.1 = n ∧ a ≠ b
def Women (g : Game M W) (w v : W) : Prop :=
  ∃ a ∈ g.teams, ∃ b ∈ g.teams, a.2 = w ∧ b.2 = v ∧ a ≠ b
def Opposes (g : Game M W) (m : M) (w : W) : Prop :=
  ∃ a ∈ g.teams, ∃ b ∈ g.teams, a.1 = m ∧ b.2 = w ∧ a ≠ b
def Shares (g : Game M W) (m : M) (w : W) : Prop :=
  (∃ a ∈ g.teams, a.1 = m) ∧ (∃ b ∈ g.teams, b.2 = w)
end Game

structure Matching (M W : Type) where
  spouse : M → W → Prop
  right_unique : ∀ m w v, spouse m w → spouse m v → w = v
  left_unique : ∀ m n w, spouse m w → spouse n w → m = n

namespace Matching
variable {M W : Type}
def SingleMan (s : Matching M W) (m : M) : Prop := ¬ ∃ w, s.spouse m w
def SingleWoman (s : Matching M W) (w : W) : Prop := ¬ ∃ m, s.spouse m w
end Matching

noncomputable def count {O : Type} [Fintype O] (p : O → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter p).card

structure Schedule (M W O : Type) where
  game : O → Game M W

/-- Exact source multiplicities. A single's repeated opponent is existential,
not fixed by a label, and is required to be another single. -/
def Source {M W O : Type} [Fintype O]
    (s : Matching M W) (d : Schedule M W O) : Prop :=
  (∀ m w, s.spouse m w → ∀ o, ¬ (d.game o).Shares m w) ∧
  (∀ m w, ¬ s.spouse m w →
    count (fun o => (d.game o).Partners m w) = 1 ∧
    count (fun o => (d.game o).Opposes m w) = 1) ∧
  (∀ m, (∃ w, s.spouse m w) → ∀ n, n ≠ m →
    count (fun o => (d.game o).Men m n) = 1) ∧
  (∀ w, (∃ m, s.spouse m w) → ∀ v, v ≠ w →
    count (fun o => (d.game o).Women w v) = 1) ∧
  (∀ m, s.SingleMan m → ∃ n, n ≠ m ∧ s.SingleMan n ∧
    count (fun o => (d.game o).Men m n) = 1 ∧
    ∀ t, t ≠ m → t ≠ n → count (fun o => (d.game o).Men m t) = 1) ∧
  (∀ w, s.SingleWoman w → ∃ v, v ≠ w ∧ s.SingleWoman v ∧
    count (fun o => (d.game o).Women w v) = 1 ∧
    ∀ t, t ≠ w → t ≠ v → count (fun o => (d.game o).Women w t) = 1)

/-- The intended endpoint denies this proposition; no nonexistence result
is asserted in this base module. -/
def ExistsFiveThree (M W : Type) [Fintype M] [Fintype W] : Prop :=
  Fintype.card M = 5 ∧ Fintype.card W = 5 ∧
  ∃ s : Matching M W, count (fun p : M × W => s.spouse p.1 p.2) = 3 ∧
    ∃ (O : Type) (_ : Fintype O) (d : Schedule M W O), Source s d

end NegativeRepeat

namespace NegativeRepeat
theorem count_as_sum {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] :
    count p = ∑ x : α, if p x then 1 else 0 := by
  classical
  simp only [count, Finset.sum_boole]
  congr 1
  ext x
  simp


end NegativeRepeat
namespace NegativeRepeat.Controls

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


end NegativeRepeat.Controls
