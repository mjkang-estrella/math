import ClosureChain
import SmallClosure
set_option autoImplicit false
namespace Polyomino57
theorem layer5_link : smallLayer4 = closedLayer5 := by decide

def sevenLayers : ℕ → Array (List GridPoint)
  | 0 => smallLayer0
  | 1 => smallLayer1
  | 2 => smallLayer2
  | 3 => smallLayer3
  | 4 => smallLayer4
  | 5 => layer6
  | _ => layer7

theorem sevenLayers_certified : ∃ choices : ℕ → List GridPoint → GridPoint → ℕ × GridPoint,
    ∀ k < 6, arrayClosureCheck (sevenLayers k) (sevenLayers (k+1)) (choices k) = true := by
  obtain ⟨c5,h5⟩ := closure5
  obtain ⟨c6,h6⟩ := closure6
  refine ⟨(fun k => match k with
    | 0 => smallChoices0
    | 1 => smallChoices1
    | 2 => smallChoices2
    | 3 => smallChoices3
    | 4 => c5
    | _ => c6), ?_⟩
  intro k hk
  have hh : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl
  · exact smallClosure0
  · exact smallClosure1
  · exact smallClosure2
  · exact smallClosure3
  · simpa only [sevenLayers,layer5_link] using h5
  · simpa only [sevenLayers,layer6_link] using h6

theorem seven_normalized_coverage (P : Finset GridPoint) (hP : EdgeConnected P)
    (hc : P.card = 7) :
    ∃ row ∈ layer7.toList, ∃ hr : row.toFinset.Nonempty,
      normalize P hP.1 = normalize row.toFinset hr := by
  obtain ⟨choices,hs⟩ := sevenLayers_certified
  have hb : [(0,0)] ∈ (sevenLayers 0).toList := by decide
  have hh := certificate_growth_coverage sevenLayers 6 choices hb hs
    (growth_complete hP) (by omega)
  simpa only [hc,sevenLayers] using hh
end Polyomino57
