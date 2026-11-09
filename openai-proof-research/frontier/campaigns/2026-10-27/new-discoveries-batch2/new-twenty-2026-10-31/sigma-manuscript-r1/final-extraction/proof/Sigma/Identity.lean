import Sigma.Basic

namespace Sigma365710
open Finset

theorem pair_variance {n : ℕ} (d : Fin n → ℤ) :
    (∑ u : Fin n, ∑ v ∈ univ.filter (u < ·), (d u - d v)^2) =
    (n : ℤ) * ∑ u, d u ^ 2 - (∑ u, d u)^2 := by
  let U := ∑ u : Fin n, ∑ v ∈ univ.filter (u < ·), (d u - d v)^2
  have hdouble : (∑ u : Fin n, ∑ v : Fin n, (d u - d v)^2) = U + U := by
    have hsplit : ∀ u v : Fin n, (d u - d v)^2 =
        (if u < v then (d u - d v)^2 else 0) +
        (if v < u then (d u - d v)^2 else 0) := by
      intro u v
      rcases lt_trichotomy u v with h | h | h
      · simp [h, not_lt_of_ge h.le]
      · subst v; simp
      · simp [h, not_lt_of_ge h.le]
    calc
      _ = ∑ u : Fin n, ∑ v : Fin n,
          ((if u < v then (d u - d v)^2 else 0) +
          (if v < u then (d u - d v)^2 else 0)) := by
        apply sum_congr rfl; intro u _
        apply sum_congr rfl; intro v _
        exact hsplit u v
      _ = _ := by
        simp only [sum_add_distrib]
        dsimp [U]
        simp only [sum_filter]
        congr 1
        rw [sum_comm]
        apply sum_congr rfl
        intro u _
        apply sum_congr rfl
        intro v _
        split_ifs <;> ring

  have hexpand : (∑ u : Fin n, ∑ v : Fin n, (d u - d v)^2) =
      2 * ((n : ℤ) * ∑ u, d u ^ 2 - (∑ u, d u)^2) := by
    simp_rw [sub_sq, sum_add_distrib, sum_sub_distrib]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp_rw [← mul_sum, ← sum_mul]
    have scale : (∑ x : Fin n, 2 * d x) = 2 * (∑ x, d x) := by rw [mul_sum]
    rw [scale]
    ring
  dsimp [U] at hdouble
  omega

def edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℤ :=
  G.edgeFinset.card

def degreeSquares {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℤ :=
  ∑ u : Fin n, (G.degree u : ℤ)^2

def deficit {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℤ :=
  (n : ℤ) * edgeCount G - degreeSquares G

theorem sigmaT_degree_identity {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    sigmaT G = (n : ℤ) * degreeSquares G - 4 * edgeCount G ^ 2 := by
  have h := G.sum_degrees_eq_twice_card_edges
  have hi : (∑ u : Fin n, (G.degree u : ℤ)) = 2 * edgeCount G := by
    unfold edgeCount
    exact_mod_cast h
  rw [sigmaT, pair_variance, hi]
  unfold degreeSquares
  ring

theorem sigmaT_deficit_identity {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    sigmaT G = edgeCount G * ((n : ℤ)^2 - 4 * edgeCount G) - (n : ℤ) * deficit G := by
  rw [sigmaT_degree_identity]
  unfold deficit
  ring

end Sigma365710
