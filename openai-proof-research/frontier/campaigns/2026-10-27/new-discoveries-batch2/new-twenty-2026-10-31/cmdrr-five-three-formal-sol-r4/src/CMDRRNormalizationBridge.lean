import CMDRRCanonical

namespace CMDRR
namespace Matching
 theorem ext_spouse {M W : Type} {s t : Matching M W}
    (he : ∀ m w, s.spouse m w ↔ t.spouse m w) : s = t := by
  have hh : s.spouse = t.spouse := by
    funext m w
    exact propext (he m w)
  cases s
  cases t
  cases hh
  rfl
end Matching

namespace Source
variable {M W O : Type} [Fintype M] [Fintype W] [Fintype O]
variable {s : Matching M W} {d : Schedule M W O}

theorem canonical_transport (h : Source s d)
    (hm : Fintype.card M = 5) (hw : Fintype.card W = 5)
    (hs : count (fun p : M × W => s.spouse p.1 p.2) = 3) :
    ∃ (e : M ≃ Fin 5) (f : W ≃ Fin 5),
      (∀ m w, s.spouse m w ↔ canonical.spouse (e m) (f w)) ∧
      Source canonical (d.relabel e f) := by
  obtain ⟨e,f,hlabel⟩ := s.canonical_labels hm hw hs
  refine ⟨e,f,hlabel,?_⟩
  have he : s.relabel e f = canonical := by
    apply Matching.ext_spouse
    intro m w
    obtain ⟨m,rfl⟩ := e.surjective m
    obtain ⟨w,rfl⟩ := f.surjective w
    rw [Matching.relabel_spouse]
    exact hlabel m w
  rw [← he]
  exact h.relabel e f
end Source
end CMDRR
