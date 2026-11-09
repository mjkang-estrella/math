module
public import URMatchingMatchingMaximumMap
public import URMatchingURMaximumMap
@[expose] public section
namespace URMatching
universe u v
variable {V : Type u} {W : Type v} [Fintype V] [Fintype W]

def pullbackGraph (e : V ≃ W) (H : SimpleGraph W) : SimpleGraph V where
  Adj x y := H.Adj (e x) (e y)
  symm := ⟨fun _ _ h => H.adj_symm h⟩
  loopless := ⟨fun x => H.loopless.irrefl (e x)⟩

theorem canonical_matching_numbers (G : SimpleGraph V) :
    ∃ H : SimpleGraph (Fin (Fintype.card V)), matchingNumber H = matchingNumber G ∧
      urMatchingNumber H = urMatchingNumber G := by
  classical
  let e := (Fintype.equivFin V).symm
  let H := pullbackGraph e G
  exact ⟨H,matchingNumber_equiv e (fun _ _ => Iff.rfl),
    urMatchingNumber_equiv e (fun _ _ => Iff.rfl)⟩
end URMatching
