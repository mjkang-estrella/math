import Mathlib

namespace ReverseMexCounterexample
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

lemma exists_missing (s : Finset ℕ) : ∃ n, n ∉ s := by
  refine ⟨s.sup id + 1, ?_⟩
  intro h
  have hh := Finset.le_sup (f := id) h
  simp only [id_eq] at hh
  omega

def mex (s : Finset ℕ) : ℕ := Nat.find (exists_missing s)

theorem mex_eq_iff (s : Finset ℕ) (n : ℕ) :
    mex s = n ↔ n ∉ s ∧ ∀ j < n, j ∈ s := by
  simp [mex, Nat.find_eq_iff]

def moves (f : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  (if 3 ≤ n then {f (n-3)} else ∅) ∪
  (if 6 ≤ n then {f (n-6)} else ∅) ∪
  (if 10 ≤ n then {f (n-10)} else ∅)

def subtractionSet : Finset ℕ := {3,6,10}

def sourceMoves (f : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  (subtractionSet.filter (fun s => s ≤ n)).image (fun s => f (n-s))

theorem moves_source_bridge (f : ℕ → ℕ) (n : ℕ) : moves f n = sourceMoves f n := by
  unfold moves sourceMoves subtractionSet
  simp only [Finset.filter_insert, Finset.filter_singleton]
  split_ifs <;> simp_all


def SGSequence (f : ℕ → ℕ) : Prop := ∀ n, f n = mex (moves f n)

def tail (r : ℕ) : ℕ := [0,0,2,1,1,0,2,2,1,0,3,2,1].getD r 0

def grundy (n : ℕ) : ℕ :=
  if n < 12 then [0,0,0,1,1,1,2,2,2,0,3,3].getD n 0 else tail (n % 13)

lemma base_recurrence (n : ℕ) (hn : n < 22) : grundy n = mex (moves grundy n) := by
  interval_cases n <;> symm <;> apply (mex_eq_iff _ _).mpr <;>
    norm_num [grundy, tail, moves] <;> omega

lemma tail_recurrence (n : ℕ) (hn : 22 ≤ n) : grundy n = mex (moves grundy n) := by
  have h3 : 12 ≤ n-3 := by omega
  have h6 : 12 ≤ n-6 := by omega
  have h10 : 12 ≤ n-10 := by omega
  have r3 : (n-3)%13 = (n%13+10)%13 := by omega
  have r6 : (n-6)%13 = (n%13+7)%13 := by omega
  have r10 : (n-10)%13 = (n%13+3)%13 := by omega
  have hmod := Nat.mod_lt n (by norm_num : 0 < 13)
  simp only [grundy, moves, ite_eq_right (by omega : ¬ n < 12),
    ite_eq_left (by omega : 3 ≤ n), ite_eq_left (by omega : 6 ≤ n), ite_eq_left (by omega : 10 ≤ n),
    ite_eq_right (by omega : ¬n-3<12), ite_eq_right (by omega : ¬n-6<12),
    ite_eq_right (by omega : ¬n-10<12), r3, r6, r10]
  generalize hrem : n%13 = r at *
  interval_cases r <;> symm <;> apply (mex_eq_iff _ _).mpr <;>
    norm_num [tail] <;> omega

theorem grundy_recurrence : SGSequence grundy := by
  intro n
  by_cases hn : n < 22
  · exact base_recurrence n hn
  · exact tail_recurrence n (by omega)

theorem sg_unique (f : ℕ → ℕ) (hf : SGSequence f) : f = grundy := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [hf n, grundy_recurrence n]
    have h3 : 3 ≤ n → f (n-3) = grundy (n-3) := fun h => ih _ (by omega)
    have h6 : 6 ≤ n → f (n-6) = grundy (n-6) := fun h => ih _ (by omega)
    have h10 : 10 ≤ n → f (n-10) = grundy (n-10) := fun h => ih _ (by omega)
    congr 1
    unfold moves
    split_ifs <;> simp_all

def SourceSGSequence (f : ℕ → ℕ) : Prop := ∀ n, f n = mex (sourceMoves f n)

theorem source_sg_iff (f : ℕ → ℕ) : SourceSGSequence f ↔ SGSequence f := by
  simp only [SourceSGSequence, SGSequence, moves_source_bridge]

theorem source_recurrence (n : ℕ) : grundy n = mex (sourceMoves grundy n) := by
  rw [← moves_source_bridge]
  exact grundy_recurrence n

theorem source_unique (f : ℕ → ℕ) (hf : SourceSGSequence f) : f = grundy :=
  sg_unique f ((source_sg_iff f).mp hf)

theorem eventual_period (n : ℕ) (hn : 12 ≤ n) : grundy (n+13) = grundy n := by
  simp [grundy, show ¬n<12 by omega, show ¬n+13<12 by omega]

def PPosition (w : ℕ) : Prop := grundy w = 0

theorem P_outcome_recurrence (n : ℕ) : PPosition n ↔
    ∀ s ∈ subtractionSet, s ≤ n → ¬ PPosition (n-s) := by
  unfold PPosition
  rw [source_recurrence n, mex_eq_iff]
  simp [sourceMoves]

theorem P_positions (w : ℕ) : PPosition w ↔
    w=0 ∨ w=1 ∨ w=2 ∨ w=9 ∨
      (12 ≤ w ∧ (w%13=0 ∨ w%13=1 ∨ w%13=5 ∨ w%13=9)) := by
  by_cases h : w < 12
  · interval_cases w <;> norm_num [PPosition, grundy, tail]
  · have hm := Nat.mod_lt w (by norm_num : 0 < 13)
    simp only [PPosition, grundy, ite_eq_right h]
    generalize hr : w%13 = r at *
    interval_cases r <;> norm_num [tail] <;> omega

def reduce (z : ℤ) : ℕ :=
  if 12 ≤ z then z.toNat else (12 + (z-12)%13).toNat

theorem reduce_ge (z : ℤ) : 12 ≤ reduce z := by
  have h0 := Int.emod_nonneg (z-12) (by norm_num : (13 : ℤ) ≠ 0)
  unfold reduce
  split_ifs <;> omega

theorem reduce_mod (z : ℤ) : (reduce z : ℤ)%13 = z%13 := by
  have h0 := Int.emod_nonneg (z-12) (by norm_num : (13 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos (z-12) (by norm_num : (0 : ℤ) < 13)
  unfold reduce
  split_ifs <;> omega

theorem reduce_spec (z : ℤ) :
    (12 ≤ z → reduce z = z.toNat) ∧
    (z < 12 → ∃ n : ℕ, 1 ≤ n ∧ (reduce z : ℤ) = z + n*13 ∧
      12 ≤ reduce z ∧ reduce z ≤ 24) := by
  constructor
  · intro hz
    simp [reduce, hz]
  · intro hz
    have h0 := Int.emod_nonneg (z-12) (by norm_num : (13 : ℤ) ≠ 0)
    have h1 := Int.emod_lt_of_pos (z-12) (by norm_num : (0 : ℤ) < 13)
    have hd := Int.emod_add_mul_ediv (z-12) 13
    refine ⟨(-((z-12)/13)).toNat, ?_, ?_, ?_, ?_⟩ <;>
      (try simp only [reduce, ite_eq_right (by omega : ¬12≤z)]) <;> omega

theorem grundy_reduce (z : ℤ) : grundy (reduce z) = tail (z%13).toNat := by
  have hg := reduce_ge z
  have hm := reduce_mod z
  have hn : reduce z % 13 = (z%13).toNat := by omega
  simp [grundy, show ¬reduce z<12 by omega, hn]

theorem reduced_sub_value (w k : ℕ) :
    grundy (reduce ((w : ℤ)-3*k)) = tail ((((w%13 : ℕ) : ℤ)-3*k)%13).toNat := by
  rw [grundy_reduce]
  have hw : (w : ℤ)%13 = ((w%13 : ℕ) : ℤ) := by rfl
  have hm : ((w : ℤ)-3*k)%13 = (((w%13 : ℕ) : ℤ)-3*k)%13 := by omega
  rw [hm]

abbrev Hit (w k : ℕ) : Prop := 1 ≤ k ∧ grundy (reduce ((w : ℤ)-3*k)) = 0

lemma distance_exists (w : ℕ) : ∃ k, Hit w k := by
  refine ⟨9*w+13, ?_⟩
  constructor
  · omega
  · rw [grundy_reduce]
    have hz : (w : ℤ)-3*((9*w+13 : ℕ) : ℤ) = (-2*(w:ℤ)-3)*13 := by push_cast; ring
    rw [hz]
    norm_num [tail]

def dist (w : ℕ) : ℕ := Nat.find (distance_exists w)

theorem dist_eq_iff (w k : ℕ) :
    dist w = k ↔ Hit w k ∧ ∀ j < k, ¬ Hit w j := by
  exact Nat.find_eq_iff (distance_exists w)

def distanceTable (w : ℕ) : ℕ := [4,3,2,1,1,3,2,2,1,3,3,2,1].getD (w%13) 0

theorem distance_exact (w : ℕ) : dist w = distanceTable w := by
  rw [dist_eq_iff]
  have hm := Nat.mod_lt w (by norm_num : 0 < 13)
  unfold distanceTable
  generalize hr : w%13 = r at *
  interval_cases r <;> norm_num only [List.getD_cons_zero, List.getD_cons_succ,
    List.getD_nil] <;> constructor
  all_goals
    first
    | constructor
      · norm_num
      · rw [reduced_sub_value, hr]
        norm_num [tail]
    | intro j hj hjit
      rcases hjit with ⟨hjpos,hzero⟩
      rw [reduced_sub_value, hr] at hzero
      interval_cases j <;> norm_num [tail] at hzero

theorem even_distance_residue (w m : ℕ) (hm : 2 ≤ m) (hd : dist w = 2*m) : w%13 = 0 := by
  rw [distance_exact] at hd
  unfold distanceTable at hd
  have hmod := Nat.mod_lt w (by norm_num : 0 < 13)
  generalize hr : w%13 = r at *
  interval_cases r <;> norm_num at hd ⊢ <;> omega

theorem qualifying_positions (w : ℕ) :
    (PPosition w ∧ ∃ m, 2 ≤ m ∧ dist w = 2*m) ↔
      (w = 0 ∨ (12 ≤ w ∧ w%13 = 0)) := by
  constructor
  · rintro ⟨hw, m, hm, hd⟩
    have hr := even_distance_residue w m hm hd
    rcases (P_positions w).mp hw with h | h | h | h | h
    · exact Or.inl h
    · subst w; norm_num at hr
    · subst w; norm_num at hr
    · subst w; norm_num at hr
    · exact Or.inr ⟨h.1,hr⟩
  · intro hw
    have hp : PPosition w := (P_positions w).mpr (by
      rcases hw with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, Or.inl h.2⟩))))
    refine ⟨hp, 2, by norm_num, ?_⟩
    rw [distance_exact]
    rcases hw with h | h
    · subst w; norm_num [distanceTable]
    · norm_num [distanceTable, h.2]

theorem reduced_add_value (w a : ℕ) :
    grundy (reduce ((w : ℤ)+a)) = tail ((w+a)%13) := by
  rw [grundy_reduce]
  rfl

def ConditionA : Prop := ∀ w : ℕ, PPosition w → ∀ m : ℕ,
  2 ≤ m → dist w = 2*m →
    grundy (reduce ((w:ℤ)+10-3)) ≠ 0 ∧ grundy (reduce ((w:ℤ)+10-3*3)) = 0

theorem condition_A : ConditionA := by
  intro w _ m hm hd
  have hr := even_distance_residue w m hm hd
  have h7 : (w+7)%13 = 7 := by omega
  have h1 : (w+1)%13 = 1 := by omega
  have z7 : (w:ℤ)+10-3 = (w:ℤ)+(7:ℕ) := by omega
  have z1 : (w:ℤ)+10-3*3 = (w:ℤ)+(1:ℕ) := by omega
  rw [z7, z1, reduced_add_value, reduced_add_value, h7, h1]
  norm_num [tail]

theorem nonvacuous_zero : PPosition 0 ∧ dist 0 = 4 := by
  norm_num [PPosition, grundy, distance_exact, distanceTable]

theorem nonvacuous_thirteen : PPosition 13 ∧ dist 13 = 4 := by
  norm_num [PPosition, grundy, tail, distance_exact, distanceTable]

def ReverseMex (f : ℕ → ℕ) : Prop :=
  ∀ x : ℕ, f x = mex {f (x+3), f (x+6), f (x+10)}

theorem failure_at_five : grundy 5 ≠ mex {grundy 8, grundy 11, grundy 15} := by
  have hm : mex {grundy 8, grundy 11, grundy 15} = 0 := by
    apply (mex_eq_iff _ _).mpr
    norm_num [grundy, tail]
  rw [hm]
  norm_num [grundy]

theorem not_reverse_mex : ¬ ReverseMex grundy := by
  intro h
  exact failure_at_five (h 5)

theorem source_counterexample :
    (0 < (3 : ℕ) ∧ 3 < (6 : ℕ) ∧ 6 < (10 : ℕ)) ∧
    SourceSGSequence grundy ∧ (∀ f, SourceSGSequence f → f = grundy) ∧
    (∀ x, 11+1 ≤ x → grundy (x+13) = grundy x) ∧
    ConditionA ∧ (∃ w, PPosition w ∧ dist w = 4) ∧ ¬ ReverseMex grundy := by
  refine ⟨by norm_num, (source_sg_iff grundy).mpr grundy_recurrence, source_unique, ?_, condition_A,
    ⟨13,nonvacuous_thirteen⟩, not_reverse_mex⟩
  intro x hx
  exact eventual_period x hx

end ReverseMexCounterexample
