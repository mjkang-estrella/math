import StackSortShuffle3Labels
import Mathlib.Data.Finset.Sigma

noncomputable section
open BigOperators
namespace StackSort.Shuffle3
/-- The subset is retained as data, before inserting a positional pattern. -/
def shuffleDomain (n i : ℕ) : Finset (Σ _A : Finset ℕ,
    (List ℕ × List ℕ) × (List ℕ × List ℕ)) :=
  ((Finset.range n).powersetCard i).sigma
    (fun A => labelPairs A ×ˢ labelPairs (Finset.range n \ A))

/-- The labelled-subset shuffle cardinality, including empty blocks. -/
theorem shuffleDomain_card (n i : ℕ) :
    (shuffleDomain n i).card = Nat.choose n i * P i * P (n-i) := by
  rw [shuffleDomain, Finset.card_sigma]
  have h : ∀ A ∈ (Finset.range n).powersetCard i,
      (labelPairs A ×ˢ labelPairs (Finset.range n \ A)).card = P i * P (n-i) := by
    intro A hA
    obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp hA
    rw [Finset.card_product, labelPairs_card, labelPairs_card, hcard,
      Finset.card_sdiff_of_subset hsub, Finset.card_range, hcard]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_range, smul_eq_mul]
  exact (Nat.mul_assoc _ _ _).symm

 theorem labelWords_support {A : Finset ℕ} {w : List ℕ} (hw : w ∈ labelWords A) :
    w.toFinset = A := by
  have hp := mem_labelWords.mp hw
  ext x
  simpa using hp.mem_iff

 theorem labelWords_nodup {A : Finset ℕ} {w : List ℕ} (hw : w ∈ labelWords A) :
    w.Nodup := (mem_labelWords.mp hw).nodup_iff.mpr (Finset.sort_nodup A (· ≤ ·))

 theorem labelWords_below {A : Finset ℕ} {n : ℕ} (hA : A ⊆ Finset.range n)
    {w : List ℕ} (hw : w ∈ labelWords A) : ∀ x ∈ w, x < n := by
  intro x hx
  apply Finset.mem_range.mp (hA ?_)
  rw [← labelWords_support hw]
  exact List.mem_toFinset.mpr hx
end StackSort.Shuffle3
