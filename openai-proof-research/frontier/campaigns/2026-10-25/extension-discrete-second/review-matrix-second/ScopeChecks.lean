import QuadraticDifference
import SymplecticOrbits

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

open Matrix

example (M : QuadraticDifferenceCounterexample.Mat) :
    QuadraticDifferenceCounterexample.EndBAlternating (Matrix.toLinAlgEquiv' M) ↔
    QuadraticDifferenceCounterexample.BAlternating M := Iff.rfl

example (f : Module.End ℝ QuadraticDifferenceCounterexample.V) :
    ∃ M : QuadraticDifferenceCounterexample.Mat, Matrix.toLinAlgEquiv' M = f :=
  Matrix.toLinAlgEquiv'.surjective f

example : StrictMono SymplecticOrbitCounterexample.keep01 := by decide
example : StrictMono SymplecticOrbitCounterexample.keep02 := by decide
example : StrictMono SymplecticOrbitCounterexample.keep12 := by decide
example : StrictMono SymplecticOrbitCounterexample.pair0 := by decide
example : StrictMono SymplecticOrbitCounterexample.pair1 := by decide
example : StrictMono SymplecticOrbitCounterexample.pair2 := by decide

example : (Finset.univ.image SymplecticOrbitCounterexample.keep01) =
    (Finset.univ.filter fun i : Fin 6 => i.val/2 ≠ 2) := by decide
example : (Finset.univ.image SymplecticOrbitCounterexample.keep02) =
    (Finset.univ.filter fun i : Fin 6 => i.val/2 ≠ 1) := by decide
example : (Finset.univ.image SymplecticOrbitCounterexample.keep12) =
    (Finset.univ.filter fun i : Fin 6 => i.val/2 ≠ 0) := by decide
example : (Finset.univ.image SymplecticOrbitCounterexample.pair0) =
    (Finset.univ.filter fun i : Fin 6 => i.val/2 = 0) := by decide
example : (Finset.univ.image SymplecticOrbitCounterexample.pair1) =
    (Finset.univ.filter fun i : Fin 6 => i.val/2 = 1) := by decide
example : (Finset.univ.image SymplecticOrbitCounterexample.pair2) =
    (Finset.univ.filter fun i : Fin 6 => i.val/2 = 2) := by decide

example : ((Finset.univ : Finset (Fin 3)).powersetCard 1) =
    {({0} : Finset (Fin 3)), {1}, {2}} := by decide
example : ((Finset.univ : Finset (Fin 3)).powersetCard 2) =
    {({0,1} : Finset (Fin 3)), {0,2}, {1,2}} := by decide

example : SymplecticOrbitCounterexample.rawInvariant SymplecticOrbitCounterexample.A0Z 0 = (96:ℤ) := by decide
example : SymplecticOrbitCounterexample.rawInvariant SymplecticOrbitCounterexample.A0Z 1 = (40:ℤ) := by decide
example : SymplecticOrbitCounterexample.rawInvariant SymplecticOrbitCounterexample.A0Z 2 = (8:ℤ) := by decide
