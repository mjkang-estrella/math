import GraphClosure1_000
namespace Nut8
theorem catalogue_closed_1 (a : ℕ) (ha : a ∈ ([0] : List ℕ)) :
    ∃ cs, extensionClosed 1 a GraphClosure1_000.targets cs = true := by
  simp only [List.mem_singleton] at ha
  subst a
  exact ⟨GraphClosure1_000.certificates0, GraphClosure1_000.closed0⟩
end Nut8
