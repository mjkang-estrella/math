import Diagonal
set_option autoImplicit false
namespace Polyomino57.Diagonal
open Polyomino57

theorem connected_has_edge {P : Finset GridPoint} (h : EdgeConnected P)
    (hc : 1 < P.card) : ∃ p ∈ P, ∃ q ∈ P, Adj p q := by
  have hg := growth_complete h
  cases hg with
  | singleton p => simp at hc
  | @insert Q a b hg ha hb hab =>
    exact ⟨a,Finset.mem_insert_of_mem ha,b,Finset.mem_insert_self _ _,hab⟩

def lo (f : GridPoint → ℤ) (P : Finset GridPoint) (h : P.Nonempty) : ℤ :=
  (P.image f).min' (h.image _)
def hi (f : GridPoint → ℤ) (P : Finset GridPoint) (h : P.Nonempty) : ℤ :=
  (P.image f).max' (h.image _)

theorem lo_attained (f : GridPoint → ℤ) (P : Finset GridPoint) (h : P.Nonempty) :
    ∃ p ∈ P, f p = lo f P h :=
  Finset.mem_image.mp (Finset.min'_mem (P.image f) (h.image _))
theorem hi_attained (f : GridPoint → ℤ) (P : Finset GridPoint) (h : P.Nonempty) :
    ∃ p ∈ P, f p = hi f P h :=
  Finset.mem_image.mp (Finset.max'_mem (P.image f) (h.image _))
theorem lo_le (f : GridPoint → ℤ) (P : Finset GridPoint) (h : P.Nonempty)
    (p : GridPoint) (hp : p ∈ P) : lo f P h ≤ f p :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
theorem le_hi (f : GridPoint → ℤ) (P : Finset GridPoint) (h : P.Nonempty)
    (p : GridPoint) (hp : p ∈ P) : f p ≤ hi f P h :=
  Finset.le_max' _ _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩)

theorem signed_spans_eleven {P : Finset GridPoint} (h : EdgeConnected P)
    (hc : P.card = 11) :
    (1 ≤ hi u P h.1-lo u P h.1 ∧ hi u P h.1-lo u P h.1 ≤ 10) ∧
    (1 ≤ hi v P h.1-lo v P h.1 ∧ hi v P h.1-lo v P h.1 ≤ 10) := by
  obtain ⟨umin,humin,heumin⟩ := lo_attained u P h.1
  obtain ⟨umax,humax,heumax⟩ := hi_attained u P h.1
  obtain ⟨vmin,hvmin,hevmin⟩ := lo_attained v P h.1
  obtain ⟨vmax,hvmax,hevmax⟩ := hi_attained v P h.1
  have hu := eleven_signed_bound h hc umax humax umin humin
  have hv := eleven_signed_bound h hc vmax hvmax vmin hvmin
  obtain ⟨p,hp,q,hq,hadj⟩ := connected_has_edge h (by omega)
  have had := (adjacency p q).mp hadj
  have pulo := lo_le u P h.1 p hp
  have puhi := le_hi u P h.1 p hp
  have qulo := lo_le u P h.1 q hq
  have quhi := le_hi u P h.1 q hq
  have pvlo := lo_le v P h.1 p hp
  have pvhi := le_hi v P h.1 p hp
  have qvlo := lo_le v P h.1 q hq
  have qvhi := le_hi v P h.1 q hq
  omega
end Polyomino57.Diagonal
