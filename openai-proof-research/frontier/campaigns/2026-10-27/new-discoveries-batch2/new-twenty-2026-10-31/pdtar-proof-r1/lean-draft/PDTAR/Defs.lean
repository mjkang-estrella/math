/-
DRAFT — NOT COMPILED, NOT A CERTIFICATE.  Lane pdtar-proof-r1 (MathDB 353203).
Written without running Lean/lake (lane memory restriction).  Names of Mathlib API are best guesses
against a recent Mathlib and must be checked by the Sol worker / root before use.
`sorry` marks the proof obligations listed in LEAN-PLAN.md; an accepted certificate must contain none.
-/
import Mathlib

open Finset

namespace PDTAR

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- closed neighbourhood of a finset -/
def cnbhd (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  S ∪ S.biUnion (fun v => G.neighborFinset v)

/-- one observation round of the source (arXiv:2201.01798 §1): add every `u` that is the unique
unobserved neighbour of some observed `v`. -/
def step (G : SimpleGraph V) [DecidableRel G.Adj] (O : Finset V) : Finset V :=
  O ∪ univ.filter (fun u => ∃ v ∈ O, G.neighborFinset v \ O = {u})

/-- `P^i[S]` exactly as in the source: `P^0 = S`, `P^1 = N[S]`, `P^{i} = step P^{i-1}` for `i ≥ 2`. -/
def obs (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ → Finset V
  | 0 => S
  | 1 => cnbhd G S
  | (i + 2) => step G (obs G S (i + 1))

/-- power dominating set (source definition) -/
def IsPD (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  ∃ i, obs G S i = univ

/-- fort (survey arXiv:2406.05509 line 411) -/
def IsFort (G : SimpleGraph V) [DecidableRel G.Adj] (F : Finset V) : Prop :=
  F.Nonempty ∧ ∀ v, v ∉ F → (G.neighborFinset v ∩ F).card ≠ 1

/-- PD-TAR reconfiguration graph: PD sets, adjacent iff they differ in exactly one vertex. -/
def tar (G : SimpleGraph V) [DecidableRel G.Adj] : SimpleGraph {S : Finset V // IsPD G S} where
  Adj S T := (symmDiff S.1 T.1).card = 1
  symm := fun S T h => by simpa [symmDiff_comm] using h
  loopless := fun S h => by simp at h

/-- no isolated vertices -/
def NoIsolated {W : Type*} (H : SimpleGraph W) : Prop := ∀ w, ∃ w', H.Adj w w'

/-- uniqueness, verbatim from the source §3.3 (quantifying over all finite simple graphs `H`
with no isolated vertices, on an arbitrary finite vertex type in universe 0). -/
def TARUnique (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    NoIsolated H → Nonempty (tar H ≃g tar G) → Nonempty (H ≃g G)

/-- K_{s,t} on `Fin s ⊕ Fin t` (Mathlib's `completeBipartiteGraph`). -/
abbrev K (s t : ℕ) : SimpleGraph (Fin s ⊕ Fin t) := completeBipartiteGraph (Fin s) (Fin t)

/-- LITERAL ENDPOINT for MathDB 353203 (the source's Conjecture, all positive part sizes). -/
theorem mathdb_353203 (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    TARUnique (K s t) ↔ (s ≠ 2 ∧ t ≠ 2) := by
  sorry

end PDTAR
