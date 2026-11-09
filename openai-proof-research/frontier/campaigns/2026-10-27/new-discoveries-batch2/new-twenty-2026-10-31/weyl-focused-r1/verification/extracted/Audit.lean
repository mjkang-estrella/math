import Std
namespace Misere
/-- A finite impartial game tree: both players have precisely these options. -/
inductive Game where
  | node : List Game → Game

def zero : Game := .node []
def star : Game := .node [zero]

def adjoint : Game → Game
  | .node [] => star
  | .node (x :: xs) => .node ((x :: xs).attach.map fun y => adjoint y.val)
termination_by g => sizeOf g
 decreasing_by
  all_goals have h := List.sizeOf_lt_of_mem y.property
  all_goals simp_all
  all_goals omega

/-- The usual disjunctive sum, allowing a move in either component. -/
def add (a b : Game) : Game :=
  match a, b with
  | .node xs, .node ys => .node
      ((xs.attach.map fun x => add x.val (.node ys)) ++
       (ys.attach.map fun y => add (.node xs) y.val))
termination_by sizeOf a + sizeOf b
 decreasing_by
  all_goals subst_vars
  all_goals first | have h := List.sizeOf_lt_of_mem x.property | have h := List.sizeOf_lt_of_mem y.property
  all_goals simp_all
  all_goals omega

/-- Misere recursion: at a terminal position the player to move wins;
otherwise they win exactly when a move leaves the opponent losing. -/
def nextWins : Game → Bool
  | .node [] => true
  | .node (x :: xs) => (x :: xs).attach.any fun y => !nextWins y.val
termination_by g => sizeOf g
 decreasing_by
  all_goals have h := List.sizeOf_lt_of_mem y.property
  all_goals simp_all
  all_goals omega

/-- The standard winning-strategy recursion, including the misere terminal rule. -/
theorem nextWins_rule (xs : List Game) :
    nextWins (.node xs) = true ↔ xs = [] ∨ ∃ g ∈ xs, nextWins g = false := by
  cases xs <;> simp [nextWins]

/-- The second player wins precisely when there is a legal move and every
legal move hands the opponent a winning position. -/
theorem secondWins_rule (xs : List Game) :
    nextWins (.node xs) = false ↔ xs ≠ [] ∧ ∀ g ∈ xs, nextWins g = true := by
  cases xs <;> simp [nextWins]

/-- Allen Definition 6.3.1 / Conjecture 6.5.1, restricted to impartial games.
Left moving second wins iff the first player (Right) loses. -/
def Arrow (a b : Game) : Prop := nextWins (add b (adjoint a)) = false

def nimTwo : Game := .node [zero, star]
def beta : Game := .node [nimTwo]

theorem first_arrow : Arrow star beta := by simp [Arrow, nextWins, add, adjoint, beta, nimTwo, star, zero]
theorem second_arrow : Arrow beta zero := by simp [Arrow, nextWins, add, adjoint, beta, nimTwo, star, zero]
theorem missing_arrow : ¬ Arrow star zero := by simp [Arrow, nextWins, add, adjoint, star, zero]

theorem not_transitive : ¬ (∀ a b c : Game, Arrow a b → Arrow b c → Arrow a c) := by
  intro h
  exact missing_arrow (h star beta zero first_arrow second_arrow)
#print axioms first_arrow
#print axioms second_arrow
#print axioms missing_arrow
#print axioms not_transitive
end Misere

#print axioms Misere.zero
#print axioms Misere.star
#print axioms Misere.adjoint
#print axioms Misere.add
#print axioms Misere.nextWins
#print axioms Misere.nextWins_rule
#print axioms Misere.secondWins_rule
#print axioms Misere.Arrow
#print axioms Misere.nimTwo
#print axioms Misere.beta
#print axioms Misere.first_arrow
#print axioms Misere.second_arrow
#print axioms Misere.missing_arrow
#print axioms Misere.not_transitive
