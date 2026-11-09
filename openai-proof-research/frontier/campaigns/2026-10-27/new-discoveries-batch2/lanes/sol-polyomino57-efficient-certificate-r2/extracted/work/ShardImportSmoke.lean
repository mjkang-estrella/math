import Terminal000
import Terminal001
set_option autoImplicit false
namespace Polyomino57
theorem shardImportSmoke :
    (∀ row, TreeMember row Terminal000 → translate row.2 row.1.toFinset ⊆ witness) ∧
    (∀ row, TreeMember row Terminal001 → translate row.2 row.1.toFinset ⊆ witness) :=
  ⟨Terminal000_sound,Terminal001_sound⟩
end Polyomino57
