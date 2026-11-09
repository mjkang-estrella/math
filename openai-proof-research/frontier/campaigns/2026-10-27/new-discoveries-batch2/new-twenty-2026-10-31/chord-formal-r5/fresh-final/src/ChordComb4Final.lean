import ChordComb4Representative
import ChordComb4Planarity
namespace Chord.Comb4

/-- UNPROVED graph obligation: an odd-cycle argument should provide five
successive distinct chords unless it already supplies a triangle. The five
chords need not form an induced path. Compression is proved separately. -/
def OddCycleWindow : Prop := ∀ n (D : Diagram n), ¬Bipartite D →
  HasTriangle D ∨ ∃ a : Fin 5 → Fin (2*n), Function.Injective a ∧
    (∀ i, a i < D.partner (a i)) ∧
    Crosses D (a 0) (a 1) ∧ Crosses D (a 1) (a 2) ∧
    Crosses D (a 2) (a 3) ∧ Crosses D (a 3) (a 4)

theorem reduction_of_window (planarity : BipartitePlanarity)
    (window : OddCycleWindow) : TriangleReduction := by
  intro n _ D h0 hf
  have hnb : ¬Bipartite D := fun hb => h0 (planarity n D hb)
  rcases window n D hnb with ht | ⟨a,ha,hl,h01,h12,h23,h34⟩
  · exact ht
  · exact False.elim (no_five_path D hf a ha hl h01 h12 h23 h34)

/-- Only n ≥ 6 remains after the newly discharged n = 5 specialization. -/
def TriangleRigiditySix : Prop := ∀ n (hn : 6 ≤ n), ∀ D : Diagram n,
  HasTriangle D → (∀ A : Diagram 5, Subdiagram A D → FiveProperty A) →
  Equivalent D (r3Block n (by omega))

theorem rigidityLarge_of_six (h : TriangleRigiditySix) : Comb2.TriangleRigidityLarge := by
  intro n hn D ht hf
  by_cases h5 : n = 5
  · subst n
    exact rigidity_five D ht hf
  · exact h n (by omega) D ht hf

/-- CONDITIONAL endpoint. No original Round 4B target Prop is claimed closed. -/
theorem conj34_intended
    (step : Comb2.RepresentativeStep) (heredity : Heredity)
    (triangle : TriangleReduction) (rigidity : TriangleRigiditySix)
    (n : Nat) (hn : 3 ≤ n) (h4 : n ≠ 4) :
    Range12 (r3Block n hn) ∧
    ∀ D : Diagram n, Range12 D → Equivalent D (r3Block n hn) :=
  Comb2.conj34_intended_reduced step heredity triangle (rigidityLarge_of_six rigidity) n hn h4

/-- Alternative endpoint exposing the exact unfinished face and graph obligations. -/
theorem conj34_intended_surgery
    (surgery : EndEdgeSurgery) (split : MonochromaticSplit)
    (window : OddCycleWindow) (heredity : Heredity) (rigidity : TriangleRigiditySix)
    (n : Nat) (hn : 3 ≤ n) (h4 : n ≠ 4) :
    Range12 (r3Block n hn) ∧
    ∀ D : Diagram n, Range12 D → Equivalent D (r3Block n hn) :=
  conj34_intended (step_of_surgery surgery) heredity
    (reduction_of_window (planarity_of_split split) window) rigidity n hn h4

theorem conj34_n4 : ExactlyClasses 4 4 := Comb2.conj34_n4

theorem conj34_literal_false :
    (∀ D : Diagram 1, ¬Range12 D) ∧ (∀ D : Diagram 2, ¬Range12 D) :=
  Comb2.conj34_literal_false

#print axioms conj34_intended
#print axioms conj34_intended_surgery
#print axioms conj34_n4
#print axioms endInvariant_three
#print axioms innermost_monochromatic
#print axioms no_five_path
end Chord.Comb4
