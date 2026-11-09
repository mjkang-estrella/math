import ConcreteMachine
import MachineInvariant
import SpectralWitness

/- Source: Ciobanu--Kolpakov arXiv:1504.02774v3, Conjecture 1.3;
MathDB330264. Spectral equality means equality of actual characteristic
polynomials, as in the source. Growth counts words, not group elements. -/
namespace MathDB330264
open RACGSemantics330264

/-- The three spectral hypotheses, including the intrinsic Mathlib line graph. -/
def TripleCospectral {n m : ℕ} (T : SimpleGraph (Fin n)) (U : SimpleGraph (Fin m))
    [DecidableRel T.Adj] [DecidableRel U.Adj] : Prop :=
  (T.adjMatrix ℚ).charpoly = (U.adjMatrix ℚ).charpoly ∧
  (Tᶜ.adjMatrix ℚ).charpoly = (Uᶜ.adjMatrix ℚ).charpoly ∧
  (by classical exact (T.lineGraph.adjMatrix ℚ).charpoly = (U.lineGraph.adjMatrix ℚ).charpoly)

/-- The universal finite-tree conjecture, with equality of every geodesic coefficient. -/
def Conjecture : Prop := ∀ (n m : ℕ) (T : SimpleGraph (Fin n)) (U : SimpleGraph (Fin m))
    [DecidableRel T.Adj] [DecidableRel U.Adj],
  T.IsTree → U.IsTree → TripleCospectral T U →
  ∀ k : ℕ, geodesicGrowth T k = geodesicGrowth U k

 theorem witness_spectral : TripleCospectral ActualSpectra330264.G ActualSpectra330264.H :=
  ⟨ActualSpectra330264.adjacency_charpoly, ActualSpectra330264.complement_charpoly,
    ActualSpectra330264.intrinsic_line_charpoly⟩

/-- Complete literal counterexample: actual trees, spectra and actual presented-group word counts. -/
 theorem counterexample : ActualSpectra330264.G.IsTree ∧ ActualSpectra330264.H.IsTree ∧
    TripleCospectral ActualSpectra330264.G ActualSpectra330264.H ∧
    geodesicGrowth ActualSpectra330264.G 18 ≠ geodesicGrowth ActualSpectra330264.H 18 :=
  ⟨ActualSpectra330264.treeG, ActualSpectra330264.treeH, witness_spectral,
    ConcreteMachine330264.actual_growth_differ⟩

 theorem conjecture_false : ¬ Conjecture := by
  intro h
  exact ConcreteMachine330264.actual_growth_differ
    (h 19 19 ActualSpectra330264.G ActualSpectra330264.H
      ActualSpectra330264.treeG ActualSpectra330264.treeH witness_spectral 18)

#print axioms witness_spectral
#print axioms counterexample
#print axioms conjecture_false
end MathDB330264
