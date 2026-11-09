import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Max
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring

namespace Sigma365710
open Finset

def sigmaT {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℤ :=
  ∑ u : Fin n, ∑ v ∈ univ.filter (u < ·), ((G.degree u : ℤ) - (G.degree v : ℤ)) ^ 2

def F (n a : ℕ) : ℤ := (a : ℤ) * ((n : ℤ) - a) * ((n : ℤ) - 2 * a) ^ 2

def completeBipartite (n a : ℕ) : SimpleGraph (Fin n) where
  Adj u v := (u.val < a ∧ ¬ v.val < a) ∨ (¬ u.val < a ∧ v.val < a)
  symm := ⟨by intros; tauto⟩
  loopless := ⟨by intro; simp⟩

instance (n a : ℕ) : DecidableRel (completeBipartite n a).Adj :=
  fun _ _ => inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

theorem completeBipartite_cliqueFree (n a : ℕ) :
    (completeBipartite n a).CliqueFree 3 := by
  intro s hs
  obtain ⟨u, v, w, huv, huw, hvw, _⟩ := SimpleGraph.is3Clique_iff.mp hs
  change ((_ ∧ _) ∨ (_ ∧ _)) at huv huw hvw
  tauto

theorem completeBipartite_connected {n a : ℕ} (ha : 1 ≤ a) (han : a < n) :
    (completeBipartite n a).Connected := by
  let z : Fin n := ⟨0, by omega⟩
  let t : Fin n := ⟨a, han⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨z, fun v => ?_⟩
  by_cases hv : v.val < a
  · have hzt : (completeBipartite n a).Adj z t := by
      change (0 < a ∧ ¬a < a) ∨ (¬0 < a ∧ a < a)
      omega
    have htv : (completeBipartite n a).Adj t v := by
      change (a < a ∧ ¬v.val < a) ∨ (¬a < a ∧ v.val < a)
      exact Or.inr ⟨Nat.lt_irrefl _, hv⟩
    exact hzt.reachable.trans htv.reachable
  · apply SimpleGraph.Adj.reachable
    change (0 < a ∧ ¬v.val < a) ∨ (¬0 < a ∧ v.val < a)
    exact Or.inl ⟨by omega, hv⟩

theorem exists_maximizing_part {n : ℕ} (hn : 2 ≤ n) :
    ∃ a : ℕ, 1 ≤ a ∧ a < n ∧ ∀ b : ℕ, 1 ≤ b → b < n → F n b ≤ F n a := by
  have hne : (Icc 1 (n - 1)).Nonempty := ⟨1, by simp; omega⟩
  obtain ⟨a, ha, hmax⟩ := exists_max_image (Icc 1 (n - 1)) (F n) hne
  refine ⟨a, (mem_Icc.mp ha).1, by have := (mem_Icc.mp ha).2; omega, ?_⟩
  intro b hb hbn
  exact hmax b (mem_Icc.mpr ⟨hb, by omega⟩)

theorem sigmaT_singleton (G : SimpleGraph (Fin 1)) [DecidableRel G.Adj] : sigmaT G = 0 := by
  simp [sigmaT]

theorem F_symmetry {n a : ℕ} (ha : a ≤ n) : F n (n - a) = F n a := by
  unfold F
  rw [Nat.cast_sub ha]
  ring

end Sigma365710
