import Spans
import Symmetry
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Polyomino57.Diagonal
open Polyomino57

theorem signed_translate (p d : GridPoint) :
    u (p.1+d.1,p.2+d.2) = u p+u d ∧
    v (p.1+d.1,p.2+d.2) = v p+v d := by
  dsimp [u,v]; omega

-- Unbounded integer minima, including negative minima: no range premise.
theorem integral_normalizing_shift (U V : ℤ) :
    ∃ e : ℤ, (e = 0 ∨ e = 1) ∧ ∃ d : GridPoint, u d = -U ∧ v d = e-V := by
  let e := (V-U)%2
  have he : e = 0 ∨ e = 1 := by dsimp [e]; omega
  have hp : Parity (-U) (e-V) := by dsimp [Parity,e]; omega
  exact ⟨e,he,inverse (-U) (e-V),inverse_coordinates hp⟩

theorem translate_to_signed_box {P : Finset GridPoint} (h : EdgeConnected P)
    (hc : P.card = 11) :
    ∃ a b e : ℤ, 1 ≤ a ∧ a ≤ 10 ∧ 1 ≤ b ∧ b ≤ 10 ∧ (e = 0 ∨ e = 1) ∧
      ∃ d : GridPoint, translate d P ⊆ domain a b e ∧
        ExactExtrema (translate d P) a b e ∧
        (translate d P).card = 11 ∧ EdgeConnected (translate d P) := by
  let U := lo u P h.1
  let V := lo v P h.1
  let a := hi u P h.1-U
  let b := hi v P h.1-V
  obtain ⟨e,he,d,hdU,hdV⟩ := integral_normalizing_shift U V
  have hs := signed_spans_eleven h hc
  have ha : 1 ≤ a ∧ a ≤ 10 := hs.1
  have hb : 1 ≤ b ∧ b ≤ 10 := hs.2
  have he0 : 0 ≤ e := by omega
  refine ⟨a,b,e,ha.1,ha.2,hb.1,hb.2,he,d,?_,?_,?_,translate_connected d h⟩
  · intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    apply (mem_domain (by omega) (by omega) he0 _).mpr
    have huL := lo_le u P h.1 p hp
    have huH := le_hi u P h.1 p hp
    have hvL := lo_le v P h.1 p hp
    have hvH := le_hi v P h.1 p hp
    have hh := signed_translate p d
    change u d = -lo u P h.1 at hdU
    change v d = e-lo v P h.1 at hdV
    dsimp [a,b,U,V] at *
    omega
  · have transport : ∀ p ∈ P,
        (p.1+d.1,p.2+d.2) ∈ translate d P :=
      fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩
    obtain ⟨p,hp,hpu⟩ := lo_attained u P h.1
    obtain ⟨q,hq,hqu⟩ := hi_attained u P h.1
    obtain ⟨r,hr,hrv⟩ := lo_attained v P h.1
    obtain ⟨s,hs,hsv⟩ := hi_attained v P h.1
    have hp' := signed_translate p d
    have hq' := signed_translate q d
    have hr' := signed_translate r d
    have hs' := signed_translate s d
    dsimp [U,V,a,b] at *
    exact ⟨⟨_,transport p hp,by omega⟩,⟨_,transport q hq,by omega⟩,
      ⟨_,transport r hr,by omega⟩,⟨_,transport s hs,by omega⟩⟩
  · simpa only [translate_card] using hc

-- Both odd-span parity corrections are literal affine Cartesian D4 maps.
theorem odd_a_map (a : ℤ) (ha : a % 2 = 1) (p : GridPoint) :
    let d := inverse a (-1)
    u ((d4 true true true p).1+d.1,(d4 true true true p).2+d.2) = a-u p ∧
    v ((d4 true true true p).1+d.1,(d4 true true true p).2+d.2) = v p-1 := by
  have hd := inverse_coordinates (s := a) (t := -1) (by dsimp [Parity]; omega)
  dsimp [u,v,inverse,d4] at *; omega

theorem odd_b_map (b : ℤ) (hb : b % 2 = 1) (p : GridPoint) :
    let d := inverse 0 (b+1)
    u ((d4 true false false p).1+d.1,(d4 true false false p).2+d.2) = u p ∧
    v ((d4 true false false p).1+d.1,(d4 true false false p).2+d.2) = b+1-v p := by
  have hd := inverse_coordinates (s := 0) (t := b+1) (by dsimp [Parity]; omega)
  dsimp [u,v,inverse,d4] at *; omega

def Canonical (a b e : ℤ) : Prop :=
  1 ≤ b ∧ b ≤ a ∧ a ≤ 10 ∧ (e = 0 ∨ e = 1) ∧
    (e = 0 ∨ (a % 2 = 0 ∧ b % 2 = 0))
instance (a b e : ℤ) : Decidable (Canonical a b e) :=
  inferInstanceAs (Decidable (_ ∧ _))
def canonicalCases : Finset (ℤ × ℤ × ℤ) :=
  (((Finset.Icc 1 10).product (Finset.Icc 1 10)).product (Finset.Icc 0 1)).image
    (fun x => (x.1.1,x.1.2,x.2)) |>.filter (fun x => Canonical x.1 x.2.1 x.2.2)

theorem canonicalCases_card : canonicalCases.card = 70 := by decide
end Polyomino57.Diagonal
