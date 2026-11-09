import StackSortSeeds2Checked
import StackSortSeeds2Maximum
import StackSortSeeds2Domain

namespace StackSort.Seeds2

/-- Literal irreducible tuple-pair count, with no common internal output boundary. -/
noncomputable def II (M r t : ℕ) : ℕ := by
  classical
  exact ((tuples M r ×ˢ tuples M t).filter
    (fun p => output p.1 = output p.2 ∧ Irreducible p.1 p.2)).card

noncomputable def literalX (M r s : ℕ) : ℕ :=
  if M = 0 then (if r = 0 ∧ s = 0 then 1 else 0)
  else if 1 ≤ r ∧ r ≤ bound M ∧ 1 ≤ s ∧ s ≤ bound M then XI M r s else 0

noncomputable def literalI (M r s : ℕ) : ℕ :=
  if M = 0 then 0
  else if 1 ≤ r ∧ r ≤ bound M ∧ 1 ≤ s ∧ s ≤ bound M then II M r s else 0

/-- OPEN T1/T4: the two additive counting identities for the literal finite tuple domain.
T2 and the word-level T3 bijection are proved in the imported modules. -/
def AdditiveRecursion : Prop := ∀ M r s, 1 ≤ M →
    1 ≤ r → r ≤ bound M → 1 ≤ s → s ≤ bound M →
    literalI M r s + correction true literalX literalI M r s = deletion literalX M r s ∧
    literalX M r s = literalI M r s + correction false literalX literalI M r s

 theorem literal_recursion_of_additive (h : AdditiveRecursion) : Recursion literalX literalI := by
  intro M r s
  by_cases hM : M = 0
  · subst M; simp [literalX, literalI, topStep]
  by_cases hB : 1 ≤ r ∧ r ≤ bound M ∧ 1 ≤ s ∧ s ≤ bound M
  · rcases h M r s (by omega) hB.1 hB.2.1 hB.2.2.1 hB.2.2.2 with ⟨hi, hx⟩
    have he : deletion literalX M r s - correction true literalX literalI M r s =
        literalI M r s := by omega
    simp only [topStep, ite_eq_right hM, ite_eq_left hB, he]
    exact Prod.ext hx rfl
  · simp [literalX, literalI, topStep, hM, hB]

/-- Conditional endpoint. The combinatorial identities are explicit arguments, not environment assumptions. -/
 theorem exactSeeds20_of_additiveRecursion (h : AdditiveRecursion) : ExactSeeds20 := by
  intro n hn h20
  have he := recursion_unique literalX literalI tableX tableI
    (literal_recursion_of_additive h) table_recursion n 1 1
  have hb : 1 ≤ bound n := by unfold bound; omega
  have hcount : literalX n 1 1 = P n := by
    simp only [literalX, ite_eq_right (show n ≠ 0 by omega),
      ite_eq_left (show 1 ≤ 1 ∧ 1 ≤ bound n ∧ 1 ≤ 1 ∧ 1 ≤ bound n from ⟨le_rfl, hb, le_rfl, hb⟩)]
    exact XI_one n (by omega)
  rw [hcount] at he
  have hs := table_seeds ⟨n-1, by omega⟩
  have hn' : n-1+1 = n := by omega
  have hs' : tableX n 1 1 = seed20[n]! := by simpa only [Fin.val_mk, hn'] using hs
  exact he.1.trans hs'

 theorem exactSeeds4 : ∀ n : ℕ, 1 ≤ n → n ≤ 4 → P n = seed20[n]! := by
  intro n hn h4
  interval_cases n <;> first | exact P_one | exact P_two | exact P_three | exact P_four

end StackSort.Seeds2
