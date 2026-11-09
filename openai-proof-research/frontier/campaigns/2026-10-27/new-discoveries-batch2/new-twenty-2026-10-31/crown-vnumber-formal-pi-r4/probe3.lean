import Mathlib.Data.Fintype.Basic
#check @Sum.instFintype
example (n : ℕ) : Fintype (Fin n ⊕ Fin n) := Sum.instFintype
