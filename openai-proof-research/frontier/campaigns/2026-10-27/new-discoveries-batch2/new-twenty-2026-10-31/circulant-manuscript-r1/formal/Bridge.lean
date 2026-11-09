import Circulant
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Data.ZMod.Basic
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
namespace Circulant350979
example (a : V) : ZMod 15 := a

theorem encode : ∀ bits : Fin 7 → Bool, ∃ s : Fin 128,
    ∀ d : Fin 7, s.val.testBit d.val = bits d := by decide

theorem difference_cover : ∀ a b : V, a ≠ b → ∃ d : Fin 7,
    (b : ZMod 15) - a = ((d.val+1 : ℕ) : ZMod 15) ∨ (a : ZMod 15) - b = ((d.val+1 : ℕ) : ZMod 15) := by decide

theorem mod_difference : ∀ a b : V, ∀ d : Fin 7,
    ((a.val+d.val+1)%15=b.val ∨ (b.val+d.val+1)%15=a.val) ↔
    ((b : ZMod 15)-a=((d.val+1 : ℕ) : ZMod 15) ∨ (a : ZMod 15)-b=((d.val+1 : ℕ) : ZMod 15)) := by decide

theorem represent (J : Set (ZMod 15)) : ∃ s : Fin 128,
    ∀ a b : V, (SimpleGraph.circulantGraph J).Adj a b ↔ adj s a b := by
  classical
  let G := SimpleGraph.circulantGraph J
  obtain ⟨s,hs⟩ := encode (fun d => decide (G.Adj 0 (d.val+1 : ℕ)))
  refine ⟨s,?_⟩
  intro a b
  have h0 : ∀ x y : ZMod 15, G.Adj x y ↔ G.Adj 0 (y-x) := by
    intro x y
    have h := SimpleGraph.circulantGraph_adj_translate (s:=J) (u:=0) (v:=y-x) (d:=x)
    change G.Adj (0+x) ((y-x)+x) ↔ G.Adj 0 (y-x) at h
    simpa only [zero_add, sub_add_cancel] using h
  constructor
  · intro h
    obtain ⟨d,hd⟩ := difference_cover a b (G.ne_of_adj h)
    refine ⟨d,?_,(mod_difference a b d).mpr hd⟩
    rw [hs]; apply decide_eq_true
    rcases hd with hd | hd
    · exact hd ▸ (h0 a b).mp h
    · exact hd ▸ (h0 b a).mp h.symm
  · rintro ⟨d,hd,hab⟩
    have h : G.Adj 0 (d.val+1 : ℕ) := of_decide_eq_true (by simpa [hs] using hd)
    rcases (mod_difference a b d).mp hab with hab | hab
    · exact (h0 a b).mpr (hab.symm ▸ h)
    · exact ((h0 b a).mpr (hab.symm ▸ h)).symm
end Circulant350979
