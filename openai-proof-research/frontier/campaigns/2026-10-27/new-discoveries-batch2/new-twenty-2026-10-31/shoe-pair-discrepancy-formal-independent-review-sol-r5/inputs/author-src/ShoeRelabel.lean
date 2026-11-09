import ShoeEndpoint

/-! Injective color coding preserves the actual chronological predicates.
The winner identity here deliberately assumes termination: default values need
not commute with an arbitrary injection on the exceptional nonterminating set. -/
namespace Shoe

attribute [local instance] Classical.propDecidable

def relabelSample {α β : Type*} (e : α → β) (ω : Sample α) : Sample β :=
  fun n => e (ω n)

theorem hasMatch_relabel_iff {α β : Type*} (e : α → β)
    (he : Function.Injective e) (ω : Sample α) (n : ℕ) :
    HasMatch (relabelSample e ω) n ↔ HasMatch ω n := by
  constructor
  · rintro ⟨a,b,ha,hb,h⟩
    exact ⟨a,b,ha,hb,he h⟩
  · rintro ⟨a,b,ha,hb,h⟩
    exact ⟨a,b,ha,hb,congrArg e h⟩

theorem firstMatch_relabel_iff {α β : Type*} (e : α → β)
    (he : Function.Injective e) (ω : Sample α) (n : ℕ) :
    FirstMatch (relabelSample e ω) n ↔ FirstMatch ω n := by
  simp only [FirstMatch, hasMatch_relabel_iff e he]

theorem terminates_relabel_iff {α β : Type*} (e : α → β)
    (he : Function.Injective e) (ω : Sample α) :
    Terminates (relabelSample e ω) ↔ Terminates ω := by
  simp only [Terminates, hasMatch_relabel_iff e he]

theorem firstLength_relabel {α β : Type*} (e : α → β)
    (he : Function.Injective e) (ω : Sample α) (ht : Terminates ω) :
    firstLength (relabelSample e ω) ((terminates_relabel_iff e he ω).mpr ht) =
      firstLength ω ht := by
  apply Nat.le_antisymm
  · exact Nat.find_le ((hasMatch_relabel_iff e he ω _).mpr (firstLength_spec ω ht))
  · exact Nat.find_le ((hasMatch_relabel_iff e he ω _).mp
      (firstLength_spec (relabelSample e ω) _))

theorem winner_relabel_of_terminates {α β : Type*} [Inhabited α] [Inhabited β]
    (e : α → β) (he : Function.Injective e) (ω : Sample α) (ht : Terminates ω) :
    winner (relabelSample e ω) = e (winner ω) := by
  have hte := (terminates_relabel_iff e he ω).mpr ht
  simp only [winner, dite_eq_left ht, dite_eq_left hte, firstLength_relabel e he ω ht,
    relabelSample]

/-- Finite alphabets use the genuine inclusion into Nat, without a
positive-coordinate or full-support hypothesis. -/
theorem finite_winner_zeroExtension (n : ℕ) [Inhabited (Fin n)]
    (ω : Sample (Fin n)) (ht : Terminates ω) :
    winner (relabelSample Fin.val ω) = (winner ω).val :=
  winner_relabel_of_terminates Fin.val Fin.val_injective ω ht

end Shoe
