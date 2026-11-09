import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Find
set_option autoImplicit false
set_option warningAsError true
namespace FourAttractor
abbrev Word := List Bool
def theta (e : Bool) (s : Word) : Word :=
  if e then s.reverse.map Bool.not else s.reverse
@[simp] theorem theta_length (e : Bool) (s : Word) : (theta e s).length = s.length := by
  cases e <;> simp [theta]
@[simp] theorem theta_append (e : Bool) (s t : Word) :
    theta e (s ++ t) = theta e t ++ theta e s := by
  cases e <;> simp [theta]
@[simp] theorem theta_twice (e : Bool) (s : Word) : theta e (theta e s) = s := by
  cases e <;> simp [theta, List.map_reverse, List.map_map, Function.comp_def]
def IsClosure (e : Bool) (s t : Word) : Prop :=
  s.IsPrefix t ∧ theta e t = t ∧
  ∀ u : Word, s.IsPrefix u → theta e u = u → t.length ≤ u.length
theorem extension_determined (e : Bool) (s q : Word)
    (h : theta e (s ++ q) = s ++ q) (hlen : q.length ≤ s.length) :
    q = theta e (s.take q.length) := by
  have a := congrArg (List.take q.length) h
  simp only [theta_append] at a
  have b : (theta e q ++ theta e s).take q.length = theta e q := by
    simpa only [theta_length] using (List.take_left (l₁ := theta e q) (l₂ := theta e s))
  rw [b, List.take_append_of_le_length hlen] at a
  simpa using congrArg (theta e) a
def candidate (e : Bool) (s : Word) (k : Nat) : Word := s ++ theta e (s.take k)
theorem candidate_full (e : Bool) (s : Word) :
    theta e (candidate e s s.length) = candidate e s s.length := by
  simp [candidate]
def good (e : Bool) (s : Word) (k : Nat) : Prop :=
  theta e (candidate e s k) = candidate e s k
instance (e : Bool) (s : Word) (k : Nat) : Decidable (good e s k) := inferInstanceAs (Decidable (_ = _))
def least (e : Bool) (s : Word) : Nat := Nat.find (show ∃ k, good e s k from ⟨s.length, candidate_full e s⟩)
def closure (e : Bool) (s : Word) : Word := candidate e s (least e s)
theorem least_le (e : Bool) (s : Word) : least e s ≤ s.length :=
  Nat.find_min' _ (candidate_full e s)
theorem closure_spec (e : Bool) (s : Word) : IsClosure e s (closure e s) := by
  refine ⟨⟨theta e (s.take (least e s)), rfl⟩, ?_, ?_⟩
  · exact Nat.find_spec (show ∃ k, good e s k from ⟨s.length, candidate_full e s⟩)
  intro u hu hf
  obtain ⟨q, rfl⟩ := hu
  by_cases hq : q.length ≤ s.length
  · have hd := extension_determined e s q hf hq
    have hg : good e s q.length := by simpa [good, candidate, ← hd] using hf
    have hk : least e s ≤ q.length := Nat.find_min' _ hg
    simp only [closure, candidate, List.length_append, theta_length, List.length_take]
    omega
  · have hk := least_le e s
    simp only [closure, candidate, List.length_append, theta_length, List.length_take]
    omega
theorem closure_unique (e : Bool) (s t : Word) (h : IsClosure e s t) : closure e s = t := by
  have hc := closure_spec e s
  obtain ⟨q, hq⟩ := h.1
  obtain ⟨r, hr⟩ := hc.1
  have lens := hc.2.2 t h.1 h.2.1
  have lent := h.2.2 _ hc.1 hc.2.1
  have len : (closure e s).length = t.length := by omega
  have qt : q.length ≤ s.length := by
    rw [← hq] at len
    have hl := least_le e s
    simp [closure, candidate] at len
    omega
  have qr : r.length ≤ s.length := by
    have := congrArg List.length hr
    simp [closure, candidate] at this
    omega
  have eqLen : q.length = r.length := by rw [← hq, ← hr] at len; simpa using len.symm
  have dq := extension_determined e s q (by simpa [hq] using h.2.1) qt
  have dr := extension_determined e s r (by simpa [hr] using hc.2.1) qr
  rw [← hr, dr, ← eqLen, ← dq, hq]
theorem closure_eq_checked (e : Bool) (s : Word) (k : Nat)
    (hk : good e s k) (hm : ∀ j < k, ¬ good e s j) :
    closure e s = candidate e s k := by
  have hle : least e s ≤ k := Nat.find_min' _ hk
  have hge : k ≤ least e s := by
    by_contra hn
    have hs : good e s (least e s) := Nat.find_spec _
    exact hm (least e s) (by omega) hs
  have he : least e s = k := by omega
  simp [closure, he]
end FourAttractor
