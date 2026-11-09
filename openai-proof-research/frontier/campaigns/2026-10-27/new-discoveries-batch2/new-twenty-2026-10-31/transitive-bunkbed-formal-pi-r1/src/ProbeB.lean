import Mathlib.Logic.Relation
structure HToken (n : Nat) where
  fst : Fin n
  snd : Fin n
  hlt : (fst : Nat) < (snd : Nat)
  layer : Bool
abbrev Vert (n : Nat) := Fin n × Bool
def Out (n : Nat) := HToken n ⊕ Fin n → Bool
def htok {n : Nat} (i j : Fin n) (h : (i : Nat) < (j : Nat)) (l : Bool) := Sum.inl (HToken.mk i j h l)
example {n : Nat} (x y : Vert n) (ω ω' : Out n) (h2 : ∃ hh : (x.1 : Nat) < (y.1 : Nat), ω (htok x.1 y.1 hh x.2) = true) : True := by
  obtain ⟨hlt, hw⟩ := h2
  trivial
