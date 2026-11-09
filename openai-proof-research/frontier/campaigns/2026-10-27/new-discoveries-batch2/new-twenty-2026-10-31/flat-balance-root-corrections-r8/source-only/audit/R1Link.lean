import FlatBalanceBridges
open BigOperators FlatBalance
namespace Review352972
 theorem source_bound_iff {V : Type} [Fintype V] (G : SimpleGraph V) (N : ℕ)
    (hN : Fintype.card V < N) :
    Balanced G ↔
    |((∑ d ∈ Finset.range N, if d % 2 = 1 then cliqueCount G d else 0 : ℕ) : ℝ) -
      ((∑ d ∈ Finset.range N, if d % 2 = 0 then cliqueCount G d else 0 : ℕ) : ℝ)| ≤ 1 := by
  rw [oddCliqueSum_cutoff G hN, evenCliqueSum_cutoff G hN]
  exact balanced_iff_absReal G
 theorem source_universal_negation :
    ¬ (∀ (V : Type) (hV : Fintype V) (G : SimpleGraph V),
      @Flat V hV G → ∀ N : ℕ, @Fintype.card V hV < N →
      |((∑ d ∈ Finset.range N, if d % 2 = 1 then @cliqueCount V hV G d else 0 : ℕ) : ℝ) -
        ((∑ d ∈ Finset.range N, if d % 2 = 0 then @cliqueCount V hV G d else 0 : ℕ) : ℝ)| ≤ 1) := by
  intro h
  apply not_flat_balanced_conjecture_via_bridges
  intro V hV G hf
  exact (source_bound_iff G (Fintype.card V + 1) (by omega)).mpr
    (h V hV G hf (Fintype.card V + 1) (by omega))
end Review352972
#print axioms Review352972.source_bound_iff
#print axioms Review352972.source_universal_negation
