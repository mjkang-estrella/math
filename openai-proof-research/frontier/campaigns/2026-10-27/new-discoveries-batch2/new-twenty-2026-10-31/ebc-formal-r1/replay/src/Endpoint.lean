import Arithmetic
import Control
namespace EBC337062
open SimpleGraph Finset

/-- Remaining BFS correctness obligation: distance and literal shortest-path counts. -/
def DistanceAndCounts : Prop := ∀ x y : ZMod 32,
  G32.dist x y = tabDist x.val y.val ∧ sigma G32 x y = tabCount x.val y.val

/-- Remaining splitting obligation, specialized to the counterexample.
A general connected-graph path-splitting theorem would discharge this. -/
def PathSplitting32 : Prop := ∀ x y u v : ZMod 32, x ≠ y → G32.Adj u v →
  sigmaEdge G32 x y s(u,v) =
    (if G32.dist x u + 1 + G32.dist v y = G32.dist x y then
      sigma G32 x u * sigma G32 v y else 0) +
    (if G32.dist x v + 1 + G32.dist u y = G32.dist x y then
      sigma G32 x v * sigma G32 u y else 0)

noncomputable def pairTerm (x y : ZMod 32) (e : Sym2 (ZMod 32)) : ℚ :=
  if x = y then 0 else (sigmaEdge G32 x y e : ℚ) / sigma G32 x y

theorem betweenness_sum (e : Sym2 (ZMod 32)) :
    edgeBetweenness G32 e = ∑ x : ZMod 32, ∑ y : ZMod 32, pairTerm x y e := by
  unfold edgeBetweenness pairTerm
  simp only [Finset.sum_filter]
  congr 1
  funext x
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : x = y <;> simp [h, Ne.symm]

theorem pairTerm_eq (hc : DistanceAndCounts) (hs : PathSplitting32)
    (x y u v : ZMod 32) (huv : G32.Adj u v) :
    pairTerm x y s(u,v) = rationalTerm x.val y.val u.val v.val := by
  unfold pairTerm rationalTerm
  by_cases h : x = y
  · simp [h]
  · have hval : x.val ≠ y.val := fun e => h (Fin.ext e)
    simp only [ite_eq_right h, ite_eq_right hval]
    rw [hs x y u v h huv, (hc x y).2]
    simp only [oriented, (hc x u).1, (hc v y).1, (hc x y).1,
      (hc x v).1, (hc u y).1, (hc x u).2, (hc v y).2,
      (hc x v).2, (hc u y).2]

theorem sum_zmod (f : ℕ → ℚ) :
    (∑ x : ZMod 32, f x.val) = ((List.range 32).map f).sum := by
  change (∑ x : Fin 32, f x.val) = _
  rw [Fin.sum_univ_eq_sum_range]
  have hr : (List.range 32).toFinset = Finset.range 32 := by ext; simp
  rw [← hr]
  exact List.sum_toFinset f List.nodup_range

theorem betweenness_from_bridges (hc : DistanceAndCounts) (hs : PathSplitting32)
    (u v : ZMod 32) (huv : G32.Adj u v) :
    edgeBetweenness G32 s(u,v) =
      ((List.range 32).map (rationalRow u.val v.val)).sum := by
  rw [betweenness_sum]
  simp_rw [pairTerm_eq hc hs _ _ _ _ huv]
  have inner (x : ZMod 32) :
      (∑ y : ZMod 32, rationalTerm x.val y.val u.val v.val) =
        rationalRow u.val v.val x.val := sum_zmod (fun y => rationalTerm x.val y u.val v.val)
  simp_rw [inner]
  exact sum_zmod _

theorem edge01 : G32.Adj 0 1 := by decide
theorem edge09 : G32.Adj 0 9 := by decide

theorem bprime_01 (hc : DistanceAndCounts) (hs : PathSplitting32) :
    edgeBetweenness G32 s(0,1) = 15169 / 615 := by
  rw [betweenness_from_bridges hc hs 0 1 edge01]
  exact rational_total_1

theorem bprime_09 (hc : DistanceAndCounts) (hs : PathSplitting32) :
    edgeBetweenness G32 s(0,9) = 15172 / 615 := by
  rw [betweenness_from_bridges hc hs 0 9 edge09]
  exact rational_total_9

theorem not_uniform (hc : DistanceAndCounts) (hs : PathSplitting32) :
    ¬ EdgeBetweennessUniform G32 := by
  intro h
  have he := h s(0,1) edge01 s(0,9) edge09
  rw [bprime_01 hc hs, bprime_09 hc hs] at he
  exact fractions_differ he

/-- Conditional endpoint; both remaining propositions are explicit arguments. -/
theorem conjecture21_false (hc : DistanceAndCounts) (hs : PathSplitting32) :
    ¬ Conjecture21 := by
  intro h
  exact not_uniform hc hs (h 1 1 le_rfl).1

#print axioms EBC337062.conjecture21_false
#print axioms EBC337062.control_uniform
end EBC337062
