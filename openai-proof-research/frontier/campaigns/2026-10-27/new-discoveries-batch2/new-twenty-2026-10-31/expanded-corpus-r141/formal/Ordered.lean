import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Data.List.Sublists
import Mathlib.Data.Fintype.Card
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.DeriveFintype
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 4000
set_option maxHeartbeats 0
namespace OrderedCounterexample
inductive G where
 | e | a | b | c | d | f
 deriving DecidableEq
open G
instance : Fintype G := ⟨{e,a,b,c,d,f}, by intro x; cases x <;> simp⟩
-- e,a,b,c,d,f represent (0,0),(0,1),(1,0),(1,1),(2,0),(2,1)
def mul : G → G → G
 | e, x => x
 | a, e => a | a, a => e | a, b => f | a, c => d | a, d => c | a, f => b
 | b, e => b | b, a => c | b, b => d | b, c => f | b, d => e | b, f => a
 | c, e => c | c, a => b | c, b => a | c, c => e | c, d => f | c, f => d
 | d, e => d | d, a => f | d, b => e | d, c => a | d, d => b | d, f => c
 | f, e => f | f, a => d | f, b => c | f, c => b | f, d => a | f, f => e
def inv : G → G | e => e | a => a | b => d | c => c | d => b | f => f
instance : Group G where
 mul := mul
 one := e
 inv := inv
 mul_assoc := by decide
 one_mul := by decide
 mul_one := by decide
 inv_mul_cancel := by decide

def HasOne {H : Type*} [Group H] (s : List H) : Prop :=
 ∃ t : List H, t.Sublist s ∧ t ≠ [] ∧ t.prod = 1
def HasLongOne {H : Type*} [Group H] (s : List H) (r : ℕ) : Prop :=
 ∃ t : List H, t.Sublist s ∧ t.length = r ∧ t.prod = 1
noncomputable def D (H : Type*) [Group H] : ℕ :=
 sInf {n : ℕ | 0 < n ∧ ∀ s : List H, s.length = n → HasOne s}
noncomputable def E (H : Type*) [Group H] [Fintype H] : ℕ :=
 sInf {n : ℕ | 0 < n ∧ ∀ s : List H, s.length = n → HasLongOne s (Fintype.card H)}
def check (s : List G) : Bool := s.sublists.any fun t => !t.isEmpty && t.prod == 1
def checkLong (s : List G) (r : ℕ) : Bool := s.sublists.any fun t => t.length == r && t.prod == 1
lemma check_sound (s : List G) : check s = true ↔ HasOne s := by
 simp [check, HasOne, List.any_eq_true, List.mem_sublists]
lemma checkLong_sound (s : List G) (r : ℕ) : checkLong s r = true ↔ HasLongOne s r := by
 simp [checkLong, HasLongOne, List.any_eq_true, List.mem_sublists]
lemma four_check : ∀ x y z w : G, check [x,y,z,w] = true := by decide
lemma four : ∀ s : List G, s.length = 4 → HasOne s := by
 intro s h
 rcases s with _ | ⟨x,s⟩ <;> simp only [List.length_cons, List.length_nil] at h <;> try omega
 rcases s with _ | ⟨y,s⟩ <;> simp only [List.length_cons, List.length_nil] at h <;> try omega
 rcases s with _ | ⟨z,s⟩ <;> simp only [List.length_cons, List.length_nil] at h <;> try omega
 rcases s with _ | ⟨w,s⟩ <;> simp only [List.length_cons, List.length_nil] at h <;> try omega
 have hs : s = [] := List.length_eq_zero_iff.mp (by omega)
 subst s
 exact (check_sound _).mp (four_check x y z w)
lemma free_three : ¬ HasOne [a,b,b] := by
 rw [← check_sound]; decide
lemma D_eq : D G = 4 := by
 change sInf {n : ℕ | 0 < n ∧ ∀ s : List G, s.length = n → HasOne s} = 4
 apply le_antisymm
 · exact csInf_le ⟨0, by intro n hn; omega⟩ ⟨by omega, four⟩
 · apply (le_csInf_iff_of_wellFoundedLT (show ({n : ℕ | 0 < n ∧ ∀ s : List G, s.length = n → HasOne s}).Nonempty from ⟨4, by omega, four⟩)).mpr
   intro n hn
   by_contra h
   have hn3 : n ≤ 3 := by omega
   have hs := hn.2 ([a,b,b].take n) (by simp; omega)
   obtain ⟨t,ht,he,hp⟩ := hs
   exact free_three ⟨t, ht.trans (List.take_sublist _ _), he, hp⟩
def witness : List G := [a,a,a,a,a,b,b,b,b]
lemma witness_no : ¬ HasLongOne witness 6 := by
 rw [← checkLong_sound]; decide
lemma E_ne : E G ≠ 9 := by
 intro h
 let S : Set ℕ := {n | 0 < n ∧ ∀ s : List G, s.length = n → HasLongOne s (Fintype.card G)}
 have hS : S.Nonempty := by
  by_contra he
  have : S = ∅ := Set.not_nonempty_iff_eq_empty.mp he
  change sInf S = 9 at h
  rw [this] at h
  simp at h
 have hh := csInf_mem hS
 change sInf S = 9 at h
 rw [h] at hh
 have hc : Fintype.card G = 6 := by decide
 have bad := hh.2 witness (by decide)
 rw [hc] at bad
 exact witness_no bad
theorem source_refutation : E G ≠ D G + Fintype.card G - 1 := by
 rw [D_eq]
 have hc : Fintype.card G = 6 := by decide
 rw [hc]
 exact E_ne
#print axioms source_refutation
end OrderedCounterexample
