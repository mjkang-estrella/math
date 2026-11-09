import Endpoint
import Mathlib.Tactic.Linarith
namespace Hetyei347230
private theorem word2 (w : Word) (h : w.length = 2) :
    w = [false,false] ∨ w = [false,true] ∨ w = [true,false] ∨ w = [true,true] := by
  match w with
  | [x,y] => cases x <;> cases y <;> simp
  | [] => simp at h
  | [_] => simp at h
  | _::_::_::_ => simp at h

theorem degree_two_expansion (p : ABPoly) (hp : p ∈ deg 2) :
    p = Finsupp.single [false,false] (p [false,false]) + Finsupp.single [false,true] (p [false,true]) +
      Finsupp.single [true,false] (p [true,false]) + Finsupp.single [true,true] (p [true,true]) := by
  ext w
  by_cases hw : w.length = 2
  · rcases word2 w hw with rfl | rfl | rfl | rfl <;> simp
  · have hz : p w = 0 := (Finsupp.mem_supported' ℚ p).mp hp w hw
    have h1 : [false,false] ≠ w := by intro he; subst w; exact hw rfl
    have h2 : [false,true] ≠ w := by intro he; subst w; exact hw rfl
    have h3 : [true,false] ≠ w := by intro he; subst w; exact hw rfl
    have h4 : [true,true] ≠ w := by intro he; subst w; exact hw rfl
    simp [hz, h1,h2,h3,h4]

private theorem image2 (x y : Bool) (c : ℚ) :
    I2 (Finsupp.single [x,y] c) =
      c • toPoly (I2w [x,y]) := by simp [I2]

theorem kernel_equality_degree_two : deg 2 ⊓ LinearMap.ker I2 = anti 2 := by
  ext p
  constructor
  · intro hp
    refine ⟨hp.1, ?_⟩
    have he := degree_two_expansion p hp.1
    have hz : I2 p = 0 := hp.2
    rw [he] at hz
    have haa := congrArg (fun q : ABPoly => q [false,false]) hz
    have hab := congrArg (fun q : ABPoly => q [false,true]) hz
    have hbb := congrArg (fun q : ABPoly => q [true,true]) hz
    norm_num [map_add, image2, I2w, Mw, Mrs, MrsAux_zero, MrsAux_succ, cop, inIndex, rsVal, toPoly, a, b,
      List.range_succ, Finsupp.single_apply] at haa hab hbb
    have h0 : p [false,false] = 0 := by linarith
    have h1 : p [true,true] = 0 := by linarith
    have h2 : p [true,false] = -p [false,true] := by linarith
    change star p + p = 0
    rw [he]
    simp [map_add, star_single, h0,h1,h2]
  · intro hp
    refine ⟨hp.1, ?_⟩
    have he := degree_two_expansion p hp.1
    have hs : star p + p = 0 := hp.2
    rw [he] at hs
    have haa := congrArg (fun q : ABPoly => q [false,false]) hs
    have hab := congrArg (fun q : ABPoly => q [false,true]) hs
    have hbb := congrArg (fun q : ABPoly => q [true,true]) hs
    norm_num [map_add, star_single, a,b, Finsupp.single_apply] at haa hab hbb
    have h0 : p [false,false] = 0 := by linarith
    have h1 : p [true,true] = 0 := by linarith
    have h2 : p [true,false] = -p [false,true] := by linarith
    change I2 p = 0
    rw [he]
    simp only [map_add, image2]
    norm_num [I2w, Mw, Mrs, MrsAux_zero, MrsAux_succ, cop, inIndex, rsVal, toPoly, a,b, List.range_succ,
      h0, h1, h2, smul_add, Finsupp.smul_single]
    abel
end Hetyei347230
