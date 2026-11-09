import Sem4RotorSet
open scoped BigOperators
namespace ChanLevine.Sem4
variable {n : ℕ} [NeZero n]

def execute (c : SignedConfig n) (w : List (ZMod n)) : SignedConfig n := w.foldl fire c

omit [NeZero n] in
theorem execute_perm {u v : List (ZMod n)} (h : u.Perm v) (c : SignedConfig n) :
    execute c u = execute c v := by
  induction h generalizing c with
  | nil => rfl
  | cons a h ih => exact ih (fire c a)
  | swap a b w =>
    change execute (fire (fire c b) a) w = execute (fire (fire c a) b) w
    by_cases hab : a = b
    · subst b; rfl
    · rw [Sem3.fire_comm hab]
  | trans h h' ih ih' => exact (ih c).trans (ih' c)

omit [NeZero n] in
theorem double_fire (c : SignedConfig n) (v : ZMod n) :
    fire (fire c v) v = ⟨fun k => c.x k - (if k = v then 2 else 0) +
      (if k = v-1 then 1 else 0) + (if k = v+1 then 1 else 0), c.q⟩ := by
  cases c with
  | mk x q =>
    apply (show ∀ a b : SignedConfig n, a.x = b.x → a.q = b.q → a = b from by
      rintro ⟨x,q⟩ ⟨y,r⟩ hx hq; cases hx; cases hq; rfl)
    · funext k
      cases hq : q v <;> simp [fire, target, hq] <;> split_ifs <;> omega
    · funext k; simp [fire]

def doubleWord (l : List (ZMod n)) : List (ZMod n) := l.flatMap (fun v => [v,v])

omit [NeZero n] in
theorem execute_doubleWord (c : SignedConfig n) (l : List (ZMod n)) :
    execute c (doubleWord l) = ⟨fun k => c.x k +
      (l.map (fun v => -(if k = v then (2 : ℤ) else 0) +
        (if k = v-1 then 1 else 0) + (if k = v+1 then 1 else 0))).sum, c.q⟩ := by
  induction l generalizing c with
  | nil => simp [execute, doubleWord]
  | cons a l ih =>
    simp only [doubleWord, List.flatMap_cons, List.foldl_append, execute,
      List.foldl_cons, List.foldl_nil, List.map_cons, List.sum_cons] at *
    rw [double_fire, ih]
    congr 1
    funext k
    dsimp
    ring

theorem balanced_execute (c : SignedConfig n) (w : List (ZMod n))
    (hw : ∀ v, w.count v = 2) : execute c w = c := by
  classical
  let l := (Finset.univ : Finset (ZMod n)).toList
  have hp : w.Perm (doubleWord l) := by
    apply List.perm_iff_count.mpr
    intro v
    rw [hw v]
    have hc : ∀ l : List (ZMod n), (doubleWord l).count v = 2 * l.count v := by
      intro l
      induction l with
      | nil => rfl
      | cons x l ih =>
        by_cases h : x = v
        · subst x
          simp [doubleWord, List.count_cons_self] at *
          omega
        · simp [doubleWord, List.count_cons_of_ne h, h] at *
          exact ih
    rw [hc]
    simp [l, List.Nodup.count (Finset.nodup_toList _)]
  rw [execute_perm hp, execute_doubleWord]
  have hz : ∀ k : ZMod n, (l.map (fun v => -(if k = v then (2 : ℤ) else 0) +
      (if k = v-1 then 1 else 0) + (if k = v+1 then 1 else 0))).sum = 0 := by
    intro k
    have hleft : ∀ v : ZMod n, k = v-1 ↔ v = k+1 := by intro v; constructor <;> intro h <;> linear_combination -h
    have hright : ∀ v : ZMod n, k = v+1 ↔ v = k-1 := by intro v; constructor <;> intro h <;> linear_combination -h
    simp_rw [hleft, hright]
    simp [l, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  simp_rw [hz, add_zero]

omit [NeZero n] in
theorem legalWord_execute {c d : SignedConfig n} {w : List (ZMod n)}
    (h : LegalWord c w d) : execute c w = d := by
  induction h with
  | nil => rfl
  | cons a ha hl ih => exact ih

/-- Firing each vertex exactly twice restores the entire signed configuration. -/
theorem balanced_return {c d : SignedConfig n} {w : List (ZMod n)}
    (h : LegalWord c w d) (hw : ∀ v, w.count v = 2) : d = c :=
  (legalWord_execute h).symm.trans (balanced_execute c w hw)
end ChanLevine.Sem4
