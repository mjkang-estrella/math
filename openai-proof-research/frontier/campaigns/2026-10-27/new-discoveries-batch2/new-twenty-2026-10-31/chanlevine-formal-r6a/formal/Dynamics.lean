import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Relation
import Mathlib.Tactic

open scoped BigOperators
namespace ChanLevine
structure Config (n : ℕ) where
  x : ZMod n → ℕ
  q : ZMod n → Bool
structure SignedConfig (n : ℕ) where
  x : ZMod n → ℤ
  q : ZMod n → Bool

def Config.lift (c : Config n) : SignedConfig n := ⟨fun k => c.x k, c.q⟩
variable {n : ℕ} [NeZero n]

/-- `true` means the old rotor points right. Advance first, then move. -/
def target (c : SignedConfig n) (v : ZMod n) : ZMod n :=
  if c.q v then v - 1 else v + 1

def fire (c : SignedConfig n) (v : ZMod n) : SignedConfig n :=
  ⟨fun k => c.x k - (if k = v then 1 else 0) +
      (if k = target c v then 1 else 0),
    Function.update c.q v (!c.q v)⟩

def Step (c d : SignedConfig n) : Prop := ∃ v, 0 < c.x v ∧ d = fire c v
abbrev Reach := Relation.ReflTransGen (Step (n := n))
def Related (c d : SignedConfig n) : Prop := ∃ e, Reach c e ∧ Reach d e
/-- Definition 5.2, in its full integer-chip ambient space. -/
def Recurrent (c : SignedConfig n) : Prop :=
  (∃ d, Step c d) ∧ ∀ d, Related c d → Reach d c

def level (c : SignedConfig n) : ℤ := ∑ k, c.x k
def weight (c : SignedConfig n) : ZMod n :=
  (∑ k, k * (c.x k : ZMod n)) + ∑ k, if c.q k then 0 else 1

theorem level_fire (c : SignedConfig n) (v : ZMod n) : level (fire c v) = level c := by
  simp [level, fire, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem rotor_weight_fire (c : SignedConfig n) (v : ZMod n) :
    (∑ k : ZMod n, if (fire c v).q k then (0 : ZMod n) else 1) =
    (∑ k : ZMod n, if c.q k then (0 : ZMod n) else 1) +
      (if c.q v then 1 else -1) := by
  have hp : ∀ k : ZMod n,
      (if (fire c v).q k then (0 : ZMod n) else 1) =
      (if c.q k then 0 else 1) + (if k = v then (if c.q v then 1 else -1) else 0) := by
    intro k
    by_cases hk : k = v
    · subst k; cases h : c.q v <;> simp [fire, h]
    · simp [fire, hk]
  simp_rw [hp]
  simp [Finset.sum_add_distrib]

theorem weight_fire (c : SignedConfig n) (v : ZMod n) : weight (fire c v) = weight c := by
  have hp : ∀ k : ZMod n,
      k * ((fire c v).x k : ZMod n) = k * (c.x k : ZMod n) -
        (if k = v then k else 0) + (if k = target c v then k else 0) := by
    intro k
    simp only [fire, Int.cast_add, Int.cast_sub]
    split_ifs <;> simp <;> ring
  unfold weight
  simp_rw [hp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, rotor_weight_fire]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  cases h : c.q v <;> simp [target, h]
  ring

theorem level_reach {c d : SignedConfig n} (h : Reach c d) : level c = level d := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨v, _, rfl⟩ := hs
    exact ih.trans (level_fire _ v).symm

theorem weight_reach {c d : SignedConfig n} (h : Reach c d) : weight c = weight d := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨v, _, rfl⟩ := hs
    exact ih.trans (weight_fire _ v).symm

omit [NeZero n] in
theorem related_refl (c : SignedConfig n) : Related c c := ⟨c, .refl, .refl⟩
omit [NeZero n] in
theorem related_symm {c d : SignedConfig n} : Related c d → Related d c :=
  fun ⟨e, h, h'⟩ => ⟨e, h', h⟩
theorem level_related {c d : SignedConfig n} (h : Related c d) : level c = level d := by
  obtain ⟨e, h, h'⟩ := h
  exact (level_reach h).trans (level_reach h').symm

theorem weight_related {c d : SignedConfig n} (h : Related c d) : weight c = weight d := by
  obtain ⟨e, h, h'⟩ := h
  exact (weight_reach h).trans (weight_reach h').symm

omit [NeZero n] in
/-- On recurrent configurations the source's legal relation is exactly mutual reachability. -/
theorem recurrent_related_iff {c d : SignedConfig n} (hc : Recurrent c) (hd : Recurrent d) :
    Related c d ↔ Reach c d ∧ Reach d c := by
  constructor
  · intro h; exact ⟨hd.2 c (related_symm h), hc.2 d h⟩
  · intro h; exact ⟨d, h.1, .refl⟩

def component (c : SignedConfig n) : Set (SignedConfig n) := {d | Related c d}

/-- Natural-chip configurations are only the counting domain; recurrence stays ambient. -/
def NatRecurrent (c : Config n) : Prop := Recurrent c.lift

omit [NeZero n] in
/-- A useful definition-level negative control: no legal execution from zero chips. -/
theorem zero_not_recurrent (q : ZMod n → Bool) :
    ¬ Recurrent (SignedConfig.mk (fun _ => 0) q) := by
  rintro ⟨⟨d, v, hv, _⟩, _⟩
  exact (lt_irrefl (0 : ℤ)) hv
end ChanLevine
