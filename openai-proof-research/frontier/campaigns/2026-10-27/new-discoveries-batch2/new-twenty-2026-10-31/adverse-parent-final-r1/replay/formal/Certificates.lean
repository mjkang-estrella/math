import Definitions
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

open scoped BigOperators
namespace Adverse381433

abbrev Line := Fin 3 × ZMod 6

def onLine (l : Line) (p : Cell) : Prop :=
  if l.1 = 0 then p.1 = l.2 else if l.1 = 1 then p.2 = l.2 else p.1 + p.2 = l.2

instance (l : Line) (p : Cell) : Decidable (onLine l p) := by unfold onLine; infer_instance

def incidenceQ (l : Line) (p : Cell) : ℚ := if onLine l p then 1 else 0

def adjQ (p q : Cell) : ℚ :=
  if p ≠ q ∧ (p.1 = q.1 ∨ p.2 = q.2 ∨ p.1 + p.2 = q.1 + q.2) then 1 else 0

def translate (v p : Cell) : Cell := (p.1 + v.1, p.2 + v.2)
def untranslate (v p : Cell) : Cell := (p.1 - v.1, p.2 - v.2)

theorem translate_adj (v p q : Cell) :
    latinGraph.Adj (translate v p) (translate v q) ↔ latinGraph.Adj p q := by
  simp only [latinGraph, translate, Prod.mk.injEq, ne_eq]
  constructor <;> intro h
  · rcases h with ⟨hne, hr | hc | hs⟩
    · exact ⟨by aesop, Or.inl (add_right_cancel hr)⟩
    · exact ⟨by aesop, Or.inr (Or.inl (add_right_cancel hc))⟩
    · exact ⟨by aesop, Or.inr (Or.inr (by linear_combination hs))⟩
  · rcases h with ⟨hne, hr | hc | hs⟩
    · exact ⟨by aesop, Or.inl (by simpa using hr)⟩
    · exact ⟨by aesop, Or.inr (Or.inl (by simpa using hc))⟩
    · exact ⟨by aesop, Or.inr (Or.inr (by linear_combination hs))⟩

def fractionalBase : Cell → ℚ := fun p =>
  (![1,0,0,0,0,0,0,1/4,0,3/4,0,0,0,1/4,0,0,0,3/4,0,1/4,3/4,0,0,0,0,1/4,0,0,1/2,1/4,0,0,1/4,1/4,1/2,0] : Fin 36 → ℚ) ⟨p.1.val * 6 + p.2.val, by have := p.1.val_lt; have := p.2.val_lt; omega⟩

def kernelBase : Cell → ℚ := fun p =>
  (![0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] : Fin 36 → ℚ) ⟨p.1.val * 6 + p.2.val, by have := p.1.val_lt; have := p.2.val_lt; omega⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem incidence_identityQ : ∀ p q : Cell,
    (∑ l : Line, incidenceQ l p * incidenceQ l q) = adjQ p q + if p = q then 3 else 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem base_certificates :
    (∀ p, 0 ≤ fractionalBase p) ∧
    (∀ p, latinGraph.Adj (0,0) p → fractionalBase p = 0 ∧ kernelBase p = 0) ∧
    (∀ l, ∑ p : Cell, incidenceQ l p * fractionalBase p = 1) ∧
    (∀ l, ∑ p : Cell, incidenceQ l p * kernelBase p = 0) ∧ kernelBase (1,2) ≠ 0 := by
  unfold latinGraph
  decide +kernel

def fractionalAt (v : Cell) (p : Cell) : ℚ := fractionalBase (untranslate v p)
def kernelAt (v : Cell) (p : Cell) : ℚ := kernelBase (untranslate v p)

def CertificateAt (v : Cell) : Prop :=
    (∀ p, 0 ≤ fractionalAt v p) ∧
    (∀ p, latinGraph.Adj v p → fractionalAt v p = 0 ∧ kernelAt v p = 0) ∧
    (∀ l, ∑ p : Cell, incidenceQ l p * fractionalAt v p = 1) ∧
    (∀ l, ∑ p : Cell, incidenceQ l p * kernelAt v p = 0) ∧
    kernelAt v (translate v (1,2)) ≠ 0

end Adverse381433
