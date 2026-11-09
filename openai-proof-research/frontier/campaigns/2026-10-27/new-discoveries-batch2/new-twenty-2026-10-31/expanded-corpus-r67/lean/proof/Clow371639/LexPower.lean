import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Lexicographic powers of the five-cycle

`lexAdj k` is adjacency in the `k`-th lexicographic power `C₅[C₅[⋯]]`: two words are adjacent when
their first differing letters are adjacent in `C₅`.  Every independent set and every clique has at
most `2 ^ k` vertices, while there are `5 ^ k` vertices.
-/

namespace Clow371639

open Finset

/-- Adjacency in the five-cycle on `Fin 5`. -/
def c5Adj (a b : Fin 5) : Prop := b = a + 1 ∨ a = b + 1

instance : DecidableRel c5Adj := fun a b => by unfold c5Adj; infer_instance

lemma c5Adj_symm {a b : Fin 5} (h : c5Adj a b) : c5Adj b a := h.symm

lemma c5Adj_irrefl (a : Fin 5) : ¬ c5Adj a a := by revert a; decide

lemma c5_indep_card_le (T : Finset (Fin 5))
    (hT : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → ¬ c5Adj a b) : T.card ≤ 2 := by
  revert T; decide

lemma c5_clique_card_le (T : Finset (Fin 5))
    (hT : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → c5Adj a b) : T.card ≤ 2 := by
  revert T; decide

/-- Adjacency in the `k`-th lexicographic power of `C₅`. -/
noncomputable def lexAdj : (k : ℕ) → (Fin k → Fin 5) → (Fin k → Fin 5) → Prop
  | 0, _, _ => False
  | k + 1, u, v => c5Adj (u 0) (v 0) ∨ (u 0 = v 0 ∧ lexAdj k (Fin.tail u) (Fin.tail v))

lemma lexAdj_succ (k : ℕ) (u v : Fin (k + 1) → Fin 5) :
    lexAdj (k + 1) u v ↔ c5Adj (u 0) (v 0) ∨ (u 0 = v 0 ∧ lexAdj k (Fin.tail u) (Fin.tail v)) :=
  Iff.rfl

lemma lexAdj_symm : ∀ (k : ℕ) {u v : Fin k → Fin 5}, lexAdj k u v → lexAdj k v u
  | 0, _, _, h => h
  | k + 1, u, v, h => by
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (c5Adj_symm h)
    · exact Or.inr ⟨h1.symm, lexAdj_symm k h2⟩

lemma lexAdj_irrefl : ∀ (k : ℕ) (u : Fin k → Fin 5), ¬ lexAdj k u u
  | 0, _ => fun h => h
  | k + 1, u => by
    rintro (h | ⟨-, h⟩)
    · exact c5Adj_irrefl _ h
    · exact lexAdj_irrefl k _ h

/-- Fibre decomposition by the first letter. -/
lemma card_le_of_fibres {k : ℕ} (s : Finset (Fin (k + 1) → Fin 5)) (B : ℕ)
    (hhead : (s.image (fun u => u 0)).card ≤ 2)
    (hfib : ∀ a, ((s.filter (fun u => u 0 = a)).image Fin.tail).card ≤ B) :
    s.card ≤ 2 * B := by
  classical
  rw [card_eq_sum_card_image (fun u : Fin (k + 1) → Fin 5 => u 0) s]
  calc ∑ a ∈ s.image (fun u => u 0), (s.filter (fun u => u 0 = a)).card
      ≤ ∑ _a ∈ s.image (fun u => u 0), B := by
        refine sum_le_sum fun a _ => ?_
        have hinj : Set.InjOn (Fin.tail : (Fin (k + 1) → Fin 5) → Fin k → Fin 5)
            (s.filter (fun u => u 0 = a) : Set (Fin (k + 1) → Fin 5)) := by
          intro u hu v hv huv
          have hu' := (mem_filter.1 hu).2
          have hv' := (mem_filter.1 hv).2
          rw [← Fin.cons_self_tail u, ← Fin.cons_self_tail v, hu', hv', huv]
        rw [← card_image_of_injOn hinj]
        exact hfib a
    _ = (s.image (fun u => u 0)).card * B := by rw [sum_const, smul_eq_mul]
    _ ≤ 2 * B := Nat.mul_le_mul_right B hhead

/-- Independent sets of the `k`-th lexicographic power have at most `2 ^ k` elements. -/
theorem lex_indep_card_le : ∀ (k : ℕ) (s : Finset (Fin k → Fin 5)),
    (∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬ lexAdj k u v) → s.card ≤ 2 ^ k
  | 0, s, _ => by
    calc s.card ≤ Fintype.card (Fin 0 → Fin 5) := card_le_univ s
      _ = 2 ^ 0 := by simp
  | k + 1, s, hs => by
    classical
    rw [pow_succ, mul_comm]
    refine card_le_of_fibres s _ ?_ ?_
    · refine c5_indep_card_le _ ?_
      intro a ha b hb hab hadj
      obtain ⟨u, hu, rfl⟩ := mem_image.1 ha
      obtain ⟨v, hv, rfl⟩ := mem_image.1 hb
      exact hs u hu v hv (fun h => hab (by rw [h])) (Or.inl hadj)
    · intro a
      refine lex_indep_card_le k _ ?_
      intro t ht t' ht' htt' hadj
      obtain ⟨u, hu, rfl⟩ := mem_image.1 ht
      obtain ⟨v, hv, rfl⟩ := mem_image.1 ht'
      have hu' := mem_filter.1 hu
      have hv' := mem_filter.1 hv
      exact hs u hu'.1 v hv'.1 (fun h => htt' (by rw [h]))
        (Or.inr ⟨hu'.2.trans hv'.2.symm, hadj⟩)

/-- Cliques of the `k`-th lexicographic power have at most `2 ^ k` elements. -/
theorem lex_clique_card_le : ∀ (k : ℕ) (s : Finset (Fin k → Fin 5)),
    (∀ u ∈ s, ∀ v ∈ s, u ≠ v → lexAdj k u v) → s.card ≤ 2 ^ k
  | 0, s, _ => by
    calc s.card ≤ Fintype.card (Fin 0 → Fin 5) := card_le_univ s
      _ = 2 ^ 0 := by simp
  | k + 1, s, hs => by
    classical
    rw [pow_succ, mul_comm]
    refine card_le_of_fibres s _ ?_ ?_
    · refine c5_clique_card_le _ ?_
      intro a ha b hb hab
      obtain ⟨u, hu, rfl⟩ := mem_image.1 ha
      obtain ⟨v, hv, rfl⟩ := mem_image.1 hb
      rcases hs u hu v hv (fun h => hab (by rw [h])) with h | ⟨h, -⟩
      · exact h
      · exact absurd h hab
    · intro a
      refine lex_clique_card_le k _ ?_
      intro t ht t' ht' htt'
      obtain ⟨u, hu, rfl⟩ := mem_image.1 ht
      obtain ⟨v, hv, rfl⟩ := mem_image.1 ht'
      have hu' := mem_filter.1 hu
      have hv' := mem_filter.1 hv
      rcases hs u hu'.1 v hv'.1 (fun h => htt' (by rw [h])) with h | ⟨-, h⟩
      · rw [hu'.2, hv'.2] at h
        exact absurd h (c5Adj_irrefl a)
      · exact h

end Clow371639
