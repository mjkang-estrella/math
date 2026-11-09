import Sigma.Identity
import Sigma.PathExtension

namespace Sigma365710
open Finset

def orderedDefect {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℤ :=
  ∑ u : Fin n, ∑ v : Fin n, if G.Adj u v then
    ∑ w : Fin n, if ¬ G.Adj u w ∧ ¬ G.Adj v w then 1 else 0 else 0

theorem sum_adj_indicator {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) : (∑ v : Fin n, if G.Adj u v then (1 : ℤ) else 0) = G.degree u := by
  rw [← G.card_neighborFinset_eq_degree u]
  have heq : G.neighborFinset u = univ.filter (G.Adj u) := by ext; simp
  rw [heq]
  simp

theorem neither_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) {u v : Fin n} (huv : G.Adj u v) :
    (∑ w : Fin n, if ¬ G.Adj u w ∧ ¬ G.Adj v w then (1 : ℤ) else 0) =
      (n : ℤ) - G.degree u - G.degree v := by
  have h : ∀ w : Fin n,
      (if ¬ G.Adj u w ∧ ¬ G.Adj v w then (1 : ℤ) else 0) =
      1 - (if G.Adj u w then 1 else 0) - (if G.Adj v w then 1 else 0) := by
    intro w
    have hn : ¬ (G.Adj u w ∧ G.Adj v w) := fun h => no_triangle G ht huv h.1 h.2
    split_ifs <;> tauto
  simp_rw [h, sum_sub_distrib]
  rw [sum_adj_indicator, sum_adj_indicator]
  simp

theorem orderedDefect_eq_twice_deficit {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (ht : G.CliqueFree 3) : orderedDefect G = 2 * deficit G := by
  have weighted : ∀ u : Fin n, ∀ k : ℤ,
      (∑ v : Fin n, if G.Adj u v then k else 0) = (G.degree u : ℤ) * k := by
    intro u k
    calc
      _ = ∑ v : Fin n, (if G.Adj u v then (1 : ℤ) else 0) * k := by
        apply sum_congr rfl; intro v _; split_ifs <;> simp
      _ = _ := by rw [← sum_mul, sum_adj_indicator]
  have first : (∑ u : Fin n, ∑ v : Fin n,
      if G.Adj u v then ((n : ℤ) - G.degree u) else 0) =
      (n : ℤ) * (2 * edgeCount G) - degreeSquares G := by
    simp_rw [weighted, mul_sub, sum_sub_distrib, ← sum_mul]
    have hs : (∑ u : Fin n, (G.degree u : ℤ)) = 2 * edgeCount G := by
      unfold edgeCount
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    rw [hs]
    unfold degreeSquares
    congr 1
    · ring
    · apply sum_congr rfl; intro u _; ring
  have second : (∑ u : Fin n, ∑ v : Fin n,
      if G.Adj u v then (G.degree v : ℤ) else 0) = degreeSquares G := by
    rw [sum_comm]
    simp_rw [G.adj_comm, weighted]
    unfold degreeSquares
    apply sum_congr rfl; intro u _; ring
  calc
    orderedDefect G = ∑ u : Fin n, ∑ v : Fin n,
        ((if G.Adj u v then ((n : ℤ) - G.degree u) else 0) -
         (if G.Adj u v then (G.degree v : ℤ) else 0)) := by
      apply sum_congr rfl; intro u _
      apply sum_congr rfl; intro v _
      by_cases h : G.Adj u v
      · simp only [h, ↓reduceIte, neither_count G ht h]
      · simp [h]
    _ = _ := by
      simp only [sum_sub_distrib]
      rw [first, second]
      unfold deficit
      ring

theorem deficit_nonneg {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (ht : G.CliqueFree 3) : 0 ≤ deficit G := by
  have h : 0 ≤ orderedDefect G := by
    apply sum_nonneg; intro u _
    apply sum_nonneg; intro v _
    split_ifs
    · apply sum_nonneg; intro w _; split_ifs <;> omega
    · omega
  rw [orderedDefect_eq_twice_deficit G ht] at h
  omega

end Sigma365710
