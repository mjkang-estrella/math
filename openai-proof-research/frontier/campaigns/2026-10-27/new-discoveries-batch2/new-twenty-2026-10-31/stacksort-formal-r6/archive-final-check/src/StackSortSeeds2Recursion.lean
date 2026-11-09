import StackSortSeeds2Tuples

namespace StackSort.Seeds2
open BigOperators
abbrev Counts := ℕ → ℕ → ℕ → ℕ

def bound (M : ℕ) : ℕ := min M (21-M)
def mu (t : ℕ) : ℕ := if t = 1 then 2 else 1

def deletion (X : Counts) (M r s : ℕ) : ℕ :=
  ∑ t ∈ Finset.range 3, ∑ u ∈ Finset.range 3,
    mu t * mu u * X (M-1) (r-1+t) (s-1+u)

def convolution (X I : Counts) (M b r s : ℕ) : ℕ :=
  ∑ a ∈ Finset.Ico 1 r, ∑ c ∈ Finset.Ico 1 s,
    X (M-b) (r-a) (s-c) * I b a c

def correction (fixedMax : Bool) (X I : Counts) (M r s : ℕ) : ℕ :=
  ∑ b ∈ Finset.Ico 1 M,
    (if fixedMax then Nat.choose (M-1) (b-1) else Nat.choose M b) *
      convolution X I M b r s

/-- Executable recurrence; its combinatorial justification remains an explicit obligation. -/
def topStep (X I : Counts) (M r s : ℕ) : ℕ × ℕ :=
  if M = 0 then (if r = 0 ∧ s = 0 then 1 else 0, 0)
  else if 1 ≤ r ∧ r ≤ bound M ∧ 1 ≤ s ∧ s ≤ bound M then
    let i := deletion X M r s - correction true X I M r s
    (i + correction false X I M r s, i)
  else (0,0)

def Recursion (X I : Counts) : Prop :=
  ∀ M r s, (X M r s, I M r s) = topStep X I M r s

 theorem topStep_congr (X I Y J : Counts) (M r s : ℕ)
    (hX : ∀ k, k < M → ∀ r s, X k r s = Y k r s)
    (hI : ∀ k, k < M → ∀ r s, I k r s = J k r s) :
    topStep X I M r s = topStep Y J M r s := by
  unfold topStep
  by_cases hM : M = 0
  · simp [hM]
  simp only [ite_eq_right hM]
  split_ifs with hB
  · have hd : deletion X M r s = deletion Y M r s := by
      unfold deletion
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro u hu
      rw [hX (M-1) (by omega)]
    have hc : ∀ f, correction f X I M r s = correction f Y J M r s := by
      intro f
      unfold correction
      apply Finset.sum_congr rfl
      intro b hb
      have hb := Finset.mem_Ico.mp hb
      congr 1
      unfold convolution
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro c hc
      rw [hX (M-b) (by omega), hI b hb.2]
    rw [hd, hc true, hc false]
  · rfl

 theorem recursion_unique (X I Y J : Counts) (h : Recursion X I) (g : Recursion Y J) :
    ∀ M r s, X M r s = Y M r s ∧ I M r s = J M r s := by
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro r s
    have he := (h M r s).trans ((topStep_congr X I Y J M r s
      (fun k hk r s => (ih k hk r s).1)
      (fun k hk r s => (ih k hk r s).2)).trans (g M r s).symm)
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

end StackSort.Seeds2
