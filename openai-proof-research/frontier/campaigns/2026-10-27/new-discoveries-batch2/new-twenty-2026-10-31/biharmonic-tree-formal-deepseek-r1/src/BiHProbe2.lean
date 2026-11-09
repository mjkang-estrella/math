import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Matrix

namespace BiH

example : (∑ i in Finset.univ.filter (fun i : Fin 3 => i ≠ 0), (1:ℝ)) = 2 := by decide

example : (∑ i : Fin 3, (1:ℝ)) = 3 := by decide

abbrev starG (n : ℕ) (hn : 0 < n) : SimpleGraph (Fin n) := SimpleGraph.starGraph ⟨0, hn⟩

example (n : ℕ) (hn : 0 < n) : DecidableRel (starG n hn).Adj := inferInstance

abbrev pathG (n : ℕ) : SimpleGraph (Fin n) := SimpleGraph.pathGraph n

example (n : ℕ) : DecidableRel (pathG n).Adj := inferInstance

end BiH
