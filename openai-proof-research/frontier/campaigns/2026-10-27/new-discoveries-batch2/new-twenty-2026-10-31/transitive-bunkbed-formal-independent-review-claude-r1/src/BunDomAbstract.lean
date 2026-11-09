import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith

namespace BunDom
open Finset
abbrev State := Nat × Nat
def flip (s : State) : State := (s.2, s.1)
@[simp] theorem flip_flip (s : State) : flip (flip s) = s := by cases s; rfl

theorem sum_flip (S : Finset State) (closed : ∀ s ∈ S, flip s ∈ S)
    (f : State → Int) : ∑ s ∈ S, f (flip s) = ∑ s ∈ S, f s := by
  apply Finset.sum_bij (fun s _ => flip s)
  · exact closed
  · intro a _ b _ h
    simpa using congrArg flip h
  · intro b hb
    exact ⟨flip b, closed b hb, flip_flip b⟩
  · intros; rfl

theorem paired_nonneg (S : Finset State) (closed : ∀ s ∈ S, flip s ∈ S)
    (f : State → Int) (h : ∀ s ∈ S, 0 ≤ f s + f (flip s)) :
    0 ≤ ∑ s ∈ S, f s := by
  have hp := Finset.sum_nonneg h
  rw [Finset.sum_add_distrib, sum_flip S closed f] at hp
  omega

def advance (S : Finset State) (F : State → Int) (w : State → State → Int)
    (q : State) : Int := ∑ s ∈ S, F s * w s q

theorem reflection_step (S : Finset State) (closed : ∀ s ∈ S, flip s ∈ S)
    (F : State → Int) (w : State → State → Int)
    (wn : ∀ s q, 0 ≤ w s q)
    (eqv : ∀ s q, w (flip s) (flip q) = w s q)
    (cross : ∀ s q, s.2 < s.1 → q.1 < q.2 → w s q = 0)
    (dom : ∀ s ∈ S, s.2 < s.1 → F (flip s) ≤ F s)
    (q : State) (hq : q.2 < q.1) :
    advance S F w (flip q) ≤ advance S F w q := by
  have he (s : State) : w (flip s) q = w s (flip q) := by
    simpa using eqv s (flip q)
  have hn : 0 ≤ ∑ s ∈ S, (F s * w s q - F s * w s (flip q)) := by
    apply paired_nonneg S closed
    intro s hs
    rw [eqv s q, he s]
    rcases lt_trichotomy s.2 s.1 with ha | ha | ha
    · have hz := cross s (flip q) ha hq
      have hd := dom s hs ha
      have hw := wn s q
      rw [hz]
      nlinarith
    · have hf : flip s = s := by
        exact Prod.ext ha ha.symm
      rw [hf]
      omega
    · have hz := cross (flip s) (flip q) ha hq
      rw [eqv s q] at hz
      have hd := dom (flip s) (closed s hs) ha
      simp only [flip_flip] at hd
      have hw := wn s (flip q)
      rw [hz]
      nlinarith
  unfold advance
  rw [Finset.sum_sub_distrib] at hn
  exact sub_nonneg.mp hn

theorem reflection_time (S : Finset State) (closed : ∀ s ∈ S, flip s ∈ S)
    (F : Nat → State → Int) (w : Nat → State → State → Int)
    (rec : ∀ t q, F (t+1) q = advance S (F t) (w t) q)
    (wn : ∀ t s q, 0 ≤ w t s q)
    (eqv : ∀ t s q, w t (flip s) (flip q) = w t s q)
    (cross : ∀ t s q, s.2 < s.1 → q.1 < q.2 → w t s q = 0)
    (init : ∀ s ∈ S, s.2 < s.1 → F 0 (flip s) ≤ F 0 s) :
    ∀ t, ∀ s ∈ S, s.2 < s.1 → F t (flip s) ≤ F t s := by
  intro t
  induction t with
  | zero => exact init
  | succ t ih =>
    intro s _ hs
    rw [rec, rec]
    exact reflection_step S closed (F t) (w t) (wn t) (eqv t) (cross t) ih s hs

theorem payoff_nonneg (S : Finset State) (closed : ∀ s ∈ S, flip s ∈ S)
    (F g : State → Int)
    (dom : ∀ s ∈ S, s.2 < s.1 → F (flip s) ≤ F s)
    (anti : ∀ s, g (flip s) = -g s)
    (pos : ∀ s, s.2 < s.1 → 0 ≤ g s) :
    0 ≤ ∑ s ∈ S, F s * g s := by
  apply paired_nonneg S closed
  intro s hs
  rw [anti]
  rcases lt_trichotomy s.2 s.1 with ha | ha | ha
  · have hd := dom s hs ha
    have hg := pos s ha
    nlinarith
  · have hf : flip s = s := by
        exact Prod.ext ha ha.symm
    have hg := anti s
    rw [hf] at hg
    have : g s = 0 := by omega
    simp [this]
  · have hd := dom (flip s) (closed s hs) ha
    simp only [flip_flip] at hd
    have hg := pos (flip s) ha
    rw [anti] at hg
    nlinarith
end BunDom
