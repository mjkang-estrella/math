import Sem5Classify
set_option linter.unnecessarySeqFocus false
open scoped BigOperators
namespace ChanLevine.Sem5
variable {n : ℕ} [NeZero n]

/-- Departures still missing from a two-firing quota. -/
def residual (c : SignedConfig n) (t : ℕ) (v k : ZMod n) : ℤ :=
  if t = 0 then (if k = v-1 then 1 else 0) + (if k = v+1 then 1 else 0)
  else if t = 1 then (if k = (if c.q v then v+1 else v-1) then 1 else 0)
  else 0

omit [NeZero n] in
theorem residual_cons (c : SignedConfig n) (w : List (ZMod n)) (a v k : ZMod n)
    (hb : ∀ v, (a::w).count v ≤ 2) :
    residual (fire c a) (w.count v) v k = residual c ((a::w).count v) v k +
      (if v = a then (if k = target c a then 1 else 0) else 0) := by
  by_cases hv : v = a
  · subst v
    have h := hb a
    simp only [List.count_cons_self] at h ⊢
    have ht : w.count a = 0 ∨ w.count a = 1 := by omega
    rcases ht with ht | ht <;> cases hq : c.q a <;>
      simp [residual, ht, fire, target, hq] <;> split_ifs <;> omega
  · simp [residual, List.count_cons_of_ne (Ne.symm hv), fire, hv]

/-- The exact residual firing-flux identity for any capped execution. -/
theorem residual_flux {c d : SignedConfig n} {w : List (ZMod n)}
    (h : LegalWord c w d) (hb : ∀ v, w.count v ≤ 2) (k : ZMod n) :
    d.x k = c.x k + (2 - (w.count k : ℤ)) - ∑ v, residual c (w.count v) v k := by
  induction h with
  | nil =>
    simp only [List.count_nil, Nat.cast_zero, sub_zero]
    have he : ∀ v : ZMod n, k = v-1 ↔ v = k+1 := by
      intro v; constructor <;> intro hh <;> linear_combination -hh
    have he' : ∀ v : ZMod n, k = v+1 ↔ v = k-1 := by
      intro v; constructor <;> intro hh <;> linear_combination -hh
    simp [residual, Finset.sum_add_distrib, he, he']
  | @cons c d w a ha hl ih =>
    have ht : ∀ v, w.count v ≤ 2 := by
      intro v; have := hb v
      by_cases hh : a = v <;> simp_all [List.count_cons] <;> omega
    have hs := ih ht
    have he := congrArg (fun f : ZMod n → ℤ => ∑ v, f v)
      (funext (fun v => residual_cons c w a v k hb))
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at he
    change d.x k = (c.x k - (if k = a then 1 else 0) +
      (if k = target c a then 1 else 0)) + (2 - (w.count k : ℤ)) -
      ∑ v, residual (fire c a) (w.count v) v k at hs
    by_cases hk : a = k
    · subst k
      simp only [List.count_cons_self, Nat.cast_add, Nat.cast_one] at *
      simp only [ite_true] at hs
      omega
    · simp only [List.count_cons_of_ne hk] at *
      simp only [Ne.symm hk, ite_false, sub_zero] at hs
      omega

omit [NeZero n] in
theorem residual_nonneg (c : SignedConfig n) (t : ℕ) (v k : ZMod n) :
    0 ≤ residual c t v k := by unfold residual; split_ifs <;> omega

theorem residual_sum (c : SignedConfig n) (t : ℕ) (ht : t ≤ 2) (v : ZMod n) :
    ∑ k, residual c t v k = 2 - (t : ℤ) := by
  have hh : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases hh with rfl | rfl | rfl <;> simp [residual, Finset.sum_add_distrib]
end ChanLevine.Sem5
