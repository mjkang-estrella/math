import ComplementDecomposition
namespace XorMagic
variable {W I : Type} [Fintype W] [DecidableEq W] [Fintype I]
/-- Graph assembled from disjoint fixed point free involutions. -/
def involutionGraph (f : I → W → W) (hinv : ∀ i, Function.Involutive (f i))
    (hfree : ∀ i w, f i w ≠ w) : SimpleGraph W where
  Adj v w := ∃ i, f i v = w
  symm := ⟨by rintro v w ⟨i,hi⟩; exact ⟨i,hi ▸ hinv i v⟩⟩
  loopless := ⟨by rintro v ⟨i,hi⟩; exact hfree i v hi⟩
noncomputable instance (f : I → W → W) (hinv : ∀ i, Function.Involutive (f i))
    (hfree : ∀ i w, f i w ≠ w) : DecidableRel (involutionGraph f hinv hfree).Adj := Classical.decRel _
theorem involutionGraph_degree (f : I → W → W) (hinv : ∀ i, Function.Involutive (f i))
    (hfree : ∀ i w, f i w ≠ w) (hdis : ∀ w, Function.Injective (fun i => f i w)) :
    (involutionGraph f hinv hfree).IsRegularOfDegree (Fintype.card I) := by
  classical
  intro w
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have he : (involutionGraph f hinv hfree).neighborFinset w = Finset.univ.image (fun i => f i w) := by
    ext v
    rw [SimpleGraph.mem_neighborFinset]
    simp [involutionGraph]
  rw [he, Finset.card_image_of_injective _ (hdis w), Finset.card_univ]

theorem involutionGraph_sum (f : I → W → W) (hinv : ∀ i, Function.Involutive (f i))
    (hfree : ∀ i w, f i w ≠ w) (hdis : ∀ w, Function.Injective (fun i => f i w))
    {A : Type*} [AddCommMonoid A] (l : W → A) (w : W) :
    ∑ v ∈ (involutionGraph f hinv hfree).neighborFinset w, l v = ∑ i, l (f i w) := by
  classical
  have he : (involutionGraph f hinv hfree).neighborFinset w = Finset.univ.image (fun i => f i w) := by
    ext v; rw [SimpleGraph.mem_neighborFinset]
    simp [involutionGraph]
  rw [he, Finset.sum_image]
  exact fun _ _ _ _ h => hdis w h
end XorMagic
