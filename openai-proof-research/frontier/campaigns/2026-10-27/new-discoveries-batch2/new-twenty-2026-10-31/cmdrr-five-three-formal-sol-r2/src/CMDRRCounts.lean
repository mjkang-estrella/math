import CMDRRCells
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega

open scoped Classical
namespace CMDRR
variable {M W O : Type} [Fintype M] [Fintype W] [Fintype O]

noncomputable instance (s : Matching M W) : Fintype (Cell s) :=
  inferInstanceAs (Fintype {p : M × W // ¬ s.spouse p.1 p.2})

noncomputable instance (d : Schedule M W O) : Fintype (Incidence d) :=
  inferInstanceAs (Fintype (Σ o, {p : M × W // p ∈ (d.game o).teams}))

theorem count_eq_card (p : M → Prop) : count p = Fintype.card {m // p m} := by
  exact (Fintype.card_subtype p).symm

 theorem cells_card (s : Matching M W) (hm : Fintype.card M = 5)
    (hw : Fintype.card W = 5) (hs : count (fun p : M × W => s.spouse p.1 p.2) = 3) :
    Fintype.card (Cell s) = 22 := by
  rw [count_eq_card] at hs
  change Fintype.card {p : M × W // ¬ s.spouse p.1 p.2} = 22
  rw [Fintype.card_subtype_compl, Fintype.card_prod, hm, hw, hs]

 omit [Fintype M] [Fintype W] in
 theorem incidence_card (d : Schedule M W O) :
    Fintype.card (Incidence d) = Fintype.card O * 2 := by
  change Fintype.card (Σ o, {p : M × W // p ∈ (d.game o).teams}) = _
  simp only [Fintype.card_sigma, Fintype.card_coe, Game.two, Finset.sum_const,
    Finset.card_univ]
  rfl

namespace Source
 theorem games_eleven {s : Matching M W} {d : Schedule M W O}
    (h : Source s d) (hm : Fintype.card M = 5) (hw : Fintype.card W = 5)
    (hs : count (fun p : M × W => s.spouse p.1 p.2) = 3) :
    Fintype.card O = 11 := by
  have hc := Fintype.card_congr h.cellsEquiv
  rw [incidence_card, cells_card s hm hw hs] at hc
  omega
end Source
end CMDRR
